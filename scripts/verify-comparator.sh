#!/usr/bin/env bash
set -euo pipefail
# Local verification only. This script does not contact Palomar or submit work.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
task_lake=${LAKE:-lake}
task_options=()
if [ "${1:-}" = "--native" ]; then
  # Native verification for this trusted local project on macOS.
  task_options+=(--inadvisably-no-sandbox)
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "usage: $0 [--native]" >&2
  exit 2
fi
if [ "${#task_options[@]}" -eq 0 ] && ! command -v bwrap >/dev/null 2>&1; then
  echo "error: Palomar-compatible sandboxed Comparator requires Linux and bubblewrap (bwrap)." >&2
  exit 2
fi
prefix=$("$task_lake" env lean --print-prefix)
export PATH="$prefix/bin:$PATH"
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: the pinned Lean toolchain does not bundle $tool" >&2
    exit 2
  fi
done
task_config=$(mktemp "${TMPDIR:-/tmp}/esc-to-froberg-comparator.XXXXXX")
trap 'rm -f "$task_config"' EXIT
python3 - comparator.json "$task_config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if "external_kernels" in config:
    raise SystemExit("error: external_kernels is not a Palomar submitter field")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
"$task_lake" comparator --config "$task_config" "${task_options[@]}"
