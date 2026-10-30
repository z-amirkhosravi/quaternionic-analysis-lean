#!/usr/bin/env bash
# Source this file from Bash. Runtime links are prepared by setup.sh.
MATH_RESEARCH_FORMAL_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export MATH_RESEARCH_FORMAL_DIR
export ELAN_HOME="$(realpath -m -- "$MATH_RESEARCH_FORMAL_DIR/.elan")"
export XDG_CACHE_HOME="$(realpath -m -- "$MATH_RESEARCH_FORMAL_DIR/.cache")"
export PATH="$ELAN_HOME/bin:$PATH"
