#!/usr/bin/env bash
# Reproduce the project build and audit the three final theorem dependencies.
# Optional: LAKE_PACKAGES_OVERRIDES=/absolute/path/to/local-overrides.json
# uses existing dependency checkouts without changing the published manifest.
set -euo pipefail

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"

log_dir="${VERIFY_LOG_DIR:-verification/latest}"
mkdir -p "$log_dir"
log_dir="$(cd -- "$log_dir" && pwd)"
stage="configuration"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

finish() {
  local result=$?
  trap - EXIT
  python3 - "$log_dir/status.json" "$result" "$stage" <<'PY'
import datetime
import json
import pathlib
import sys

pathlib.Path(sys.argv[1]).write_text(json.dumps({
    "status": "passed" if sys.argv[2] == "0" else "failed",
    "exit_code": int(sys.argv[2]),
    "last_stage": sys.argv[3],
    "finished_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
}, indent=2) + "\n")
PY
  exit "$result"
}
trap finish EXIT

lake_args=()
if [[ -n "${LAKE_PACKAGES_OVERRIDES:-}" ]]; then
  if [[ ! -f "$LAKE_PACKAGES_OVERRIDES" ]]; then
    printf 'Missing package overrides file: %s\n' "$LAKE_PACKAGES_OVERRIDES" >&2
    exit 1
  fi
  lake_args+=("--packages=$LAKE_PACKAGES_OVERRIDES")
fi

run_logged() {
  local log_name="$1"
  shift
  printf 'Running %s\n' "$log_name"
  "$@" 2>&1 | tee "$log_dir/$log_name.log"
}

python3 - "$log_dir" <<'PY'
import datetime
import hashlib
import json
import os
import pathlib
import sys

root = pathlib.Path.cwd()
logs = pathlib.Path(sys.argv[1])
expected_toolchain = "leanprover/lean4:v4.19.0"
expected_mathlib = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
toolchain = (root / "lean-toolchain").read_text().strip()
if toolchain != expected_toolchain:
    raise SystemExit("Unexpected Lean toolchain: " + toolchain)
manifest = json.loads((root / "lake-manifest.json").read_text())
mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
if len(mathlib) != 1 or mathlib[0].get("rev") != expected_mathlib:
    raise SystemExit("Mathlib must use the published v4.19.0 commit")
files = sorted(root.glob("*.lean")) + [
    root / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "scripts/verify.sh", ".github/workflows/lean.yml", ".gitignore",
    )
]
hashes = {
    str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in files
}
(logs / "source-sha256.json").write_text(json.dumps(hashes, indent=2) + "\n")
(logs / "run.json").write_text(json.dumps({
    "started_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "toolchain": toolchain,
    "mathlib_revision": expected_mathlib,
    "dependency_mode": "local_path_overrides" if os.environ.get("LAKE_PACKAGES_OVERRIDES") else "published_git_manifest",
    "github_actions": os.environ.get("GITHUB_ACTIONS") == "true",
    "github_sha": os.environ.get("GITHUB_SHA"),
    "lean_num_threads": os.environ["LEAN_NUM_THREADS"],
}, indent=2) + "\n")
PY

stage="toolchain"
run_logged toolchain lake "${lake_args[@]}" env lean --version
python3 - "$log_dir/toolchain.log" <<'PY'
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text()
if not re.search(r"Lean \(version 4\.19\.0,", text):
    raise SystemExit("The active Lean executable is not version 4.19.0")
PY

stage="dependency_cache"
if [[ -n "${LAKE_PACKAGES_OVERRIDES:-}" ]]; then
  printf 'Using supplied local dependency overrides; no cache download requested.\n' \
    | tee "$log_dir/cache-get.log"
else
  run_logged cache-get lake exe cache get
fi

stage="build"
run_logged lake-build lake "${lake_args[@]}" build

stage="axiom_audit"
run_logged axioms lake "${lake_args[@]}" env lean Erdos1027Audit.lean
python3 - "$log_dir" <<'PY' | tee "$log_dir/axiom-check.log"
import hashlib
import json
import pathlib
import re
import sys

logs = pathlib.Path(sys.argv[1])
text = (logs / "axioms.log").read_text()
targets = [
    "Erdos1027Main.count_lower_bound",
    "Erdos1027Main.erdos_1027",
    "Erdos1027Main.erdos_1027_subsets",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
pattern = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
)
records = {}
for name, raw in pattern.findall(text):
    if name in targets:
        if name in records:
            raise SystemExit("Duplicate axiom report for " + name)
        records[name] = {a.strip() for a in raw.split(",") if a.strip()}
if "sorryAx" in text:
    raise SystemExit("The audit output contains sorryAx")
for name in targets:
    if name not in records:
        raise SystemExit("Missing axiom report for " + name)
    extra = records[name] - allowed
    if extra:
        raise SystemExit("Unexpected axioms for " + name + ": " + repr(sorted(extra)))
    print(name + ": " + ", ".join(sorted(records[name])))

hashes = json.loads((logs / "source-sha256.json").read_text())
for name, expected in hashes.items():
    if hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest() != expected:
        raise SystemExit("Source or configuration changed during verification: " + name)
(logs / "axiom-check.json").write_text(json.dumps({
    "status": "passed",
    "allowed_axioms": sorted(allowed),
    "theorems": {name: sorted(records[name]) for name in targets},
}, indent=2) + "\n")
print("All three final theorem axiom reports passed; source hashes are unchanged.")
PY

stage="complete"
printf 'Verification passed. Logs: %s\n' "$log_dir"
