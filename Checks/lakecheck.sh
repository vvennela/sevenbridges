set -e
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq && apt-get install -y -qq curl git ca-certificates bubblewrap >/dev/null
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
[ -x $HOME/.elan/bin/lake ] || sh /tmp/elan-init.sh -y --default-toolchain none >/dev/null 2>&1
export PATH=$HOME/.elan/bin:$PATH
mkdir -p /run/user/0 && chmod 700 /run/user/0
export XDG_RUNTIME_DIR=/run/user/0
cd /work
echo "== toolchain"; lean --version
echo "== lake build"; time lake build 2>&1 | grep -E "error|Build completed" | head -5
echo "== lake check"; time lake check; echo "lake check exit: $?"
echo "== lake check --paranoid"; time lake check --paranoid; echo "paranoid exit: $?"
