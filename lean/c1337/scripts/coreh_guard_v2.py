#!/usr/bin/env python3
"""coreh_guard_v2.py (c8gen, 2026-10-23): automatic core-hour guard, version 2. coreh_guard.py (v1, sha256 302d8326...)
stays unchanged; records cite it. Meters the CPU time of one job and stops the job when the metered total reaches the cap.
Linux /proc only, standard library only.

Modes:
  --run -- CMD ...  (recommended; exact) the guard starts CMD as its own child, with CG_TAG=<tag> in its environment if
                    --tag is given, and makes itself the child subreaper (prctl PR_SET_CHILD_SUBREAPER), so every
                    descendant, orphans included, ends up reaped by the guard. Metered total = the guard's
                    RUSAGE_CHILDREN (every reaped descendant, recursively) + utime + stime + cutime + cstime of every live
                    or zombie descendant. The guard reaps at each poll, so no descendant's CPU is lost however short it
                    lives. It exits with CMD's exit status, or 137 after a kill at the cap.
  --tag TAG         every process of this uid whose environment holds CG_TAG=TAG at exec (children inherit it).
                    Metered total = the running sum of three parts:
                    (a) live tagged processes: utime + stime + cutime + cstime;
                    (b) a vanished tagged process none of whose last-seen ancestors is alive (live tagged, or a watched
                        foreign parent): its last-seen utime + stime + cutime + cstime (v1 added this only when its
                        parent was untagged; a whole tree that vanished between two polls lost all but its root's early
                        reading);
                    (c) watched foreign parents: an untagged process that was seen as the parent of a tagged process is
                        watched while it lives, and every increase of its cutime + cstime is added. This catches tagged
                        children it reaped, including builds that started and ended between two polls. The baseline is
                        0 if the parent was born after the guard, otherwise its value when the guard first saw it, so
                        builds reaped before the first sighting count too. It also counts any untagged children it
                        reaps, so it can overcount; for a cap that errs on the safe side. When a watched parent
                        exits, the children it reaped after the last poll are read from its own parent's cutime
                        growth, minus what is already counted and minus its own last-read cpu.
                    A tree whose foreign parent was never seen (no tagged process of that parent alive at any poll) is
                    still invisible. Use --run, or run builds under one long-lived runner that is tagged or seen.
  --pids P1,P2,...  explicit PIDs; metered total = their CPU since the guard started (last seen values kept).
At cap - margin: every metered process is re-checked (tag, start time, or descendant) and sent SIGSTOP, then SIGKILL.
The guard writes a status line every --every seconds and a final line with the total to LOG.
In tag mode the guard keeps running while a watched foreign parent lives (sequential builds may follow), but at most
--idle seconds (default 300) after the last live tagged process.
usage: coreh_guard_v2.py LOG CAP_CORE_H (--tag TAG | --pids P1,... | [--tag TAG] --run -- CMD ...) [--base CORE_S]
       [--wait SEC] [--idle SEC] [--margin SEC] [--poll SEC] [--every SEC]"""
import ctypes, os, resource, signal, subprocess, sys, time

TCK = os.sysconf('SC_CLK_TCK')
UID = os.getuid()


def stat(pid):
    """(ppid, own cpu s, reaped-children cpu s, starttime ticks) or None"""
    try:
        s = open('/proc/%d/stat' % pid).read()
    except OSError:
        return None
    f = s[s.rindex(')') + 2:].split()
    return int(f[1]), (int(f[11]) + int(f[12])) / TCK, (int(f[13]) + int(f[14])) / TCK, int(f[19])


def has_tag(pid, tag):
    try:
        if os.stat('/proc/%d' % pid).st_uid != UID:
            return False
        return ('CG_TAG=' + tag).encode() in open('/proc/%d/environ' % pid, 'rb').read().split(b'\0')
    except OSError:
        return False


def all_stats():
    out = {}
    for d in os.listdir('/proc'):
        if d.isdigit():
            s = stat(int(d))
            if s:
                out[int(d)] = s
    return out


def kill_all(pids_starts, w):
    ok = []
    for p, st in pids_starts:
        s2 = stat(p)
        if s2 and s2[3] == st:
            try:
                os.kill(p, signal.SIGSTOP); ok.append((p, st))
            except OSError:
                pass
    for p, st in ok:
        s2 = stat(p)
        if s2 and s2[3] == st:
            try:
                os.kill(p, signal.SIGKILL)
            except OSError:
                pass
    w('killed %s' % ' '.join(str(p) for p, _ in sorted(ok)))


def main():
    log, cap = sys.argv[1], float(sys.argv[2]) * 3600.0
    a = sys.argv[3:]
    cmd = None
    if '--run' in a:
        i = a.index('--run')
        rest = a[i + 1:]
        cmd = rest[1:] if rest and rest[0] == '--' else rest
        a = a[:i]
    opt = lambda k, d: type(d)(a[a.index(k) + 1]) if k in a else d
    tag = opt('--tag', '')
    pids0 = [int(x) for x in opt('--pids', '').split(',') if x]
    margin, poll, every = opt('--margin', 60.0), opt('--poll', 5.0), opt('--every', 60.0)
    base_cs, wait, idle = opt('--base', 0.0), opt('--wait', 120.0), opt('--idle', 300.0)
    if cmd is None:
        assert bool(tag) != bool(pids0), 'give --tag, --pids or --run'
    L = open(log, 'a', buffering=1)
    w = lambda m: L.write('%s %s\n' % (time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), m))
    mode = 'run' if cmd is not None else ('tag' if tag else 'pids')
    w('guard v2 pid %d cap %.3f core-h margin %g s base %.1f core-s mode %s%s' % (
        os.getpid(), cap / 3600, margin, base_cs, mode, (' tag ' + tag) if tag else '' if mode != 'pids' else ' pids %s' % pids0))
    best, last_w, t_start = base_cs, 0.0, time.time()

    if mode == 'run':
        libc = ctypes.CDLL(None, use_errno=True)
        libc.prctl(36, 1, 0, 0, 0)                        # PR_SET_CHILD_SUBREAPER
        env = dict(os.environ)
        if tag:
            env['CG_TAG'] = tag
        child = subprocess.Popen(cmd, env=env)
        me, status = os.getpid(), None
        while True:
            while True:                                   # reap every exited child (the command, or an adopted orphan)
                try:
                    p, st = os.waitpid(-1, os.WNOHANG)
                except ChildProcessError:
                    break
                if p == 0:
                    break
                if p == child.pid:
                    status = st
                    child.returncode = os.waitstatus_to_exitcode(st)
            ru = resource.getrusage(resource.RUSAGE_CHILDREN)
            S = all_stats()
            kids = {}
            for p, s in S.items():                       # descendants of the guard, by the ppid chain
                q, seen_ = p, 0
                while q in S and q != me and seen_ < 64:
                    q, seen_ = S[q][0], seen_ + 1
                if q == me and p != me:
                    kids[p] = s
            tot = ru.ru_utime + ru.ru_stime + sum(s[1] + s[2] for s in kids.values())
            best = max(best, base_cs + tot)
            now = time.time()
            done = status is not None and not kids
            if now - last_w >= every or done:
                w('metered %.1f core-s = %.3f core-h, live %d' % (best, best / 3600, len(kids)))
                last_w = now
            if done:
                code = os.waitstatus_to_exitcode(status)
                w('command exited %d: guard exits, total %.3f core-h' % (code, best / 3600))
                return code
            if best >= cap - margin:
                w('CAP reached (%.3f of %.3f core-h): SIGSTOP then SIGKILL %d processes' % (best / 3600, cap / 3600, len(kids)))
                kill_all([(p, s[3]) for p, s in kids.items()], w)
                time.sleep(1)
                while True:
                    try:
                        p, st = os.waitpid(-1, os.WNOHANG)
                    except ChildProcessError:
                        break
                    if p == 0:
                        break
                ru = resource.getrusage(resource.RUSAGE_CHILDREN)
                w('after kill: reaped total %.3f core-h' % ((base_cs + ru.ru_utime + ru.ru_stime) / 3600))
                return 137
            time.sleep(poll)

    seen, foreign, lost, ever, last_live = {}, {}, 0.0, False, time.time()
    my_start = stat(os.getpid())[3]
    first_obs = {}                                        # pid -> (starttime, cutime + cstime at the guard's first sight)
    base, lastv = {}, {}
    if mode == 'pids':
        for p in pids0:
            s = stat(p)
            if s:
                base[p] = (s[1], s[3]); lastv[p] = s[1]
    while True:
        cur = {}
        if mode == 'tag':
            S = all_stats()
            for p, s in S.items():
                if p != os.getpid() and has_tag(p, tag):
                    cur[p] = s
                if p not in first_obs or first_obs[p][0] != s[3]:
                    first_obs[p] = (s[3], s[2])
            # (c) foreign parents: watch untagged parents of live tagged processes, add their cutime increases
            for p, s in cur.items():
                q = s[0]
                if q not in cur and q in S and q not in foreign and q > 1:
                    # baseline: 0 if the parent was born after the guard (all it reaped is this job's or later work),
                    # else its reaped-children cpu when the guard first saw it
                    b0 = 0.0 if S[q][3] >= my_start else first_obs.get(q, (S[q][3], S[q][2]))[1]
                    foreign[q] = [S[q][3], b0, S[q][1], b0, None, None, None]
            for q in list(foreign):
                st0, c0, own_last, cut_last, gp, gp_st, gp_cut = foreign[q]
                s = S.get(q)
                if s is None or s[3] != st0:
                    # the watched parent exited: children it reaped after the last poll are visible only in its own
                    # parent's cutime, which grew by its whole cpu; add that growth minus what is already counted and
                    # minus its own last-read cpu (an overestimate of the tail, never an underestimate)
                    g = S.get(gp) if gp else None
                    if g is not None and g[3] == gp_st and gp > 1:
                        lost += max(0.0, (g[2] - gp_cut) - own_last - cut_last)
                    del foreign[q]
                    continue
                if s[2] > c0:
                    lost += s[2] - c0
                    c0 = s[2]
                g = S.get(s[0])
                foreign[q] = [st0, c0, s[1], max(c0, s[2]), s[0], g[3] if g else None, g[2] if g else None]
            # (b) vanished tagged processes with no live ancestor (tagged or watched foreign): add their last reading
            for p, s in seen.items():
                if p in cur:
                    continue
                q, carried, hops = s[0], False, 0
                while hops < 64:
                    if q in cur or q in foreign:
                        carried = True
                        break
                    if q in seen:
                        q, hops = seen[q][0], hops + 1
                        continue
                    break
                if not carried:
                    lost += s[1] + s[2]
            tot = lost + sum(s[1] + s[2] for s in cur.values())
        else:
            for p, (b, st) in base.items():
                s = stat(p)
                if s and s[3] == st:
                    cur[p] = s; lastv[p] = s[1]
            tot = sum(lastv[p] - b for p, (b, st) in base.items())
        seen = cur
        ever = ever or bool(cur)
        best = max(best, base_cs + tot)
        now = time.time()
        if cur:
            last_live = now
        if now - last_w >= every or (not cur and ever):
            w('metered %.1f core-s = %.3f core-h, live %d, foreign watched %d' % (best, best / 3600, len(cur), len(foreign)))
            last_w = now
        waiting_on_foreign = mode == 'tag' and foreign and now - last_live <= idle
        if not cur and not waiting_on_foreign and (ever or now - t_start > wait):
            w('job has no live process%s: guard exits, total %.3f core-h' % ('' if ever else ' (never seen)', best / 3600))
            return 0
        if best >= cap - margin:
            w('CAP reached (%.3f of %.3f core-h): SIGSTOP then SIGKILL %d processes' % (best / 3600, cap / 3600, len(cur)))
            kill_all([(p, s[3]) for p, s in cur.items() if (has_tag(p, tag) if mode == 'tag' else True)], w)
            return 137
        time.sleep(poll)


if __name__ == '__main__':
    sys.exit(main())
