#!/usr/bin/env bash
# Recreate the pinned Linux x86_64 / WSL environment without changing shell profiles.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd -- "$MATH_RESEARCH_FORMAL_DIR"

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo "This bootstrap supports x86_64 Linux/WSL. See README.md for other hosts." >&2
  exit 1
fi
for tool in curl git tar sha256sum python3 cc realpath; do
  command -v "$tool" >/dev/null || { echo "Missing prerequisite: $tool" >&2; exit 1; }
done

python3 scripts/prepare_storage.py
source scripts/env.sh

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  installer_dir="$(mktemp -d)"
  trap 'rm -rf -- "$installer_dir"' EXIT
  curl --fail --location --retry 3 \
    https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
    --output "$installer_dir/elan.tar.gz"
  (
    cd -- "$installer_dir"
    echo '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  elan.tar.gz' | sha256sum --check
    tar -xzf elan.tar.gz
    ./elan-init -y --no-modify-path --default-toolchain none
  )
fi

elan toolchain install "$(cat lean-toolchain)"
# Existing clones resolve from the retained lockfile; do not update their pins.
if [[ ! -f lake-manifest.json ]]; then
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
fi
lake exe cache get
python3 scripts/verify.py
