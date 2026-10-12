#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
task_lake=${LAKE:-lake}
python3 scripts/check-lean-sources.py
"$task_lake" build
"$task_lake" env lean Audit.lean
