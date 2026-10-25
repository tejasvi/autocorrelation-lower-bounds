#!/bin/bash
# startup3c.sh (= startup3.sh with the guard cap 20 h x vCPUs instead of 13; runs k39node3b.sh; never edit in place) (K1337 fleet VM, runs as root at boot): takes the item from K39_SET, K39_TARS and K39_PART (on the fleet: the VM's metadata attributes), fetches
# k39node.sh + the core-hour guard, and runs the node under coreh_guard_v2 (cap 20 h x vCPUs) inside the systemd scope
# k39node3b.scope (MemoryMax 90%); output /k39/node3b.out. Spot VMs are deleted on preemption, so this runs once.
SET=${K39_SET:?}; TARS=${K39_TARS:?}; PART=${K39_PART:-0/1}
mkdir -p /k39/log && cd /k39
[ -f /k39/started ] && exit 0
touch /k39/started
gcloud storage cp ${KIT_URL}/kit3/k39node3b.sh ${KIT_URL}/kit/coreh_guard_v2.py /k39/ > /k39/startup.log 2>&1
CAP=$(( $(getconf _NPROCESSORS_ONLN) * 20 ))
nohup systemd-run --scope --unit=k39node3b -p MemoryMax=90% /usr/bin/env HOME=/root K39_PART=$PART \
  python3 /k39/coreh_guard_v2.py /k39/log/coreh3b.log $CAP --run -- bash /k39/k39node3b.sh "$SET" "$TARS" > /k39/node3b.out 2>&1 &
