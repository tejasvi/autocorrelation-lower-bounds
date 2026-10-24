#!/bin/bash
# setup_vm.sh: one-time setup of the C1337 Lean server (Debian 13): local SSDs as RAID0 on /scratch,
# packages (mdadm, zstd, pip; numpy/scipy/highspy for the frozen dump verifier), the Lean bundle + overlay from the kit
# bucket into /scratch/c36 (~/c36 is a symlink). Idempotent; ends with "SETUP OK".
set -u
K=${KIT_URL:?set KIT_URL to the location of the build kit}
if [ ! -f /scratch/.raid_ok ]; then
  sudo apt-get -qq update > /dev/null 2>&1
  sudo DEBIAN_FRONTEND=noninteractive apt-get -y -qq install mdadm zstd python3-pip python3-venv > /dev/null 2>&1
  DEVS=$(ls ${LOCAL_SSD_GLOB:?set LOCAL_SSD_GLOB to a glob of the local NVMe devices} 2>/dev/null | sort)
  N=$(echo $DEVS | wc -w)
  [ "$N" -gt 0 ] || { echo "SETUP FAIL no local SSD"; exit 1; }
  sudo mdadm --create /dev/md0 --level=0 --raid-devices=$N $DEVS --force --run > /dev/null 2>&1 || { echo "SETUP FAIL mdadm"; exit 1; }
  sudo mkfs.ext4 -q -F -m 0 -E lazy_itable_init=1,lazy_journal_init=1 /dev/md0 || { echo "SETUP FAIL mkfs"; exit 1; }
  sudo mkdir -p /scratch && sudo mount -o noatime /dev/md0 /scratch && sudo chown $(id -u):$(id -g) /scratch && touch /scratch/.raid_ok
fi
df -h /scratch | tail -1
if [ ! -f /scratch/c36/.bundle_ok ]; then
  mkdir -p /scratch/c36 && cd /scratch/c36
  gcloud storage cp $K/c36lean.tar.zst . > /dev/null 2>&1 || { echo "SETUP FAIL bundle download"; exit 1; }
  [ "$(sha256sum c36lean.tar.zst | cut -c1-16)" = "$(gcloud storage cat $K/c36lean.sha16)" ] || { echo "SETUP FAIL bundle sha"; exit 1; }
  zstd -d -q -c c36lean.tar.zst | tar xf - && rm -f c36lean.tar.zst && touch .bundle_ok
fi
[ -e $HOME/c36 ] || ln -s /scratch/c36 $HOME/c36
cd /scratch/c36
gcloud storage cp $K/overlay.tar . > /dev/null 2>&1 || { echo "SETUP FAIL overlay download"; exit 1; }
tar xf overlay.tar && rm -f overlay.tar && sha256sum -c --quiet overlay.sha256 || { echo "SETUP FAIL overlay sha"; exit 1; }
# overlay layout: lib/ -> library build dir, tools/ -> project tools, checker/ -> ~/c36, kit/ -> ~/c36/kit
D=/scratch/c36/lean_c133_prod/.lake/build/lib/lean
cp -a overlay/lib/. $D/ && cp -a overlay/tools/. /scratch/c36/lean_c133_prod/tools/ && cp -a overlay/checker/. /scratch/c36/ && \
  mkdir -p /scratch/c36/kit && cp -a overlay/kit/. /scratch/c36/kit/ || { echo "SETUP FAIL overlay install"; exit 1; }
python3 -c "import numpy, scipy, highspy" 2>/dev/null || \
  python3 -m pip install -q --user --break-system-packages numpy scipy highspy > /dev/null 2>&1
python3 -c "import numpy, scipy, highspy; print('py deps', numpy.__version__, scipy.__version__)" || { echo "SETUP FAIL python deps"; exit 1; }
# CheckerXF rebuilt here from its audited source against this bundle's library (must equal the shipped olean)
T=/scratch/c36/.elan/toolchains/leanprover--lean4---v4.35.0-rc3
mkdir -p /scratch/c36/xfbuild/AutocorrCert && cd /scratch/c36/xfbuild && cp /scratch/c36/overlay/src/CheckerXF.lean AutocorrCert/ && \
  LEAN_PATH=$D:$T/lib/lean $T/bin/lean -o CheckerXF.olean -i CheckerXF.ilean -c CheckerXF.c AutocorrCert/CheckerXF.lean > build.log 2>&1 && \
  $T/bin/leanc -c -O3 -DNDEBUG -DLEAN_EXPORTING -fPIC -o CheckerXF.o CheckerXF.c && $T/bin/leanc -shared -o Autocorr_AutocorrCert_CheckerXF.so CheckerXF.o \
  || { echo "SETUP FAIL CheckerXF build"; exit 1; }
echo "CheckerXF olean: built $(sha256sum CheckerXF.olean | cut -c1-16) shipped $(sha256sum $D/AutocorrCert/CheckerXF.olean | cut -c1-16)"
cp CheckerXF.olean CheckerXF.ilean $D/AutocorrCert/ && cp Autocorr_AutocorrCert_CheckerXF.so $D/
ls $D/AutocorrCert/CheckerXF.olean $D/AutocorrCert/GroupCheckX.olean $D/Autocorr_AutocorrCert_CheckerXF.so > /dev/null || { echo "SETUP FAIL libs"; exit 1; }
echo "SETUP OK $(nproc) threads, $(free -g | awk '/Mem:/ {print $2}') GiB RAM, $(df -BG --output=avail /scratch | tail -1 | tr -d ' ') free on /scratch"
