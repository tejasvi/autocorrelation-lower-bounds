#!/bin/bash
# start5.sh CAP: start drive5.sh under coreh_guard_v2 (log /scratch/c1337/log/coreh5.log, cap CAP core-h) inside the
# systemd scope c1337-drive5.scope (MemoryMax 1240G = 87.5% of 1417 GiB, no swap), so that an OOM stays inside the scope
# and ssh survives. Driver output ~/drive5.out. Stop: sudo systemctl stop c1337-drive5.scope. The keep_src2 watcher runs
# outside the scope.
set -u
CAP=${1:?core-h cap}
cd ~
setsid nohup sudo -n systemd-run --scope --unit=c1337-drive5 -p MemoryMax=1240G -p MemorySwapMax=0 --uid=$(id -u) --gid=$(id -g) \
  /usr/bin/env HOME=$HOME PATH=$PATH python3 /scratch/c36/kit/coreh_guard_v2.py /scratch/c1337/log/coreh5.log $CAP \
  --run -- bash /scratch/c36/kit/drive5.sh > ~/drive5.out 2>&1 < /dev/null &
sleep 5
systemctl show c1337-drive5.scope -p ActiveState -p MemoryMax -p MemoryCurrent -p MainPID 2>&1
