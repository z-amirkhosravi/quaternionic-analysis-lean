#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"
cd -- "$MATH_RESEARCH_FORMAL_DIR"
exec lake "$@"
