#!/usr/bin/env bash
# Verify the project with the pinned toolchain and the standard Lean axioms.
# Run from any directory: bash /path/to/bounded_arity_lean/scripts/verify.sh
set -euo pipefail

fresh_build=false
case "${1:-}" in
  "") ;;
  --fresh-build) fresh_build=true ;;
  -h|--help)
    printf '%s\n' \
      'Usage: bash scripts/verify.sh [--fresh-build]' \
      '' \
      'Build with warnings treated as failures, print the theorem audit,' \
      'enforce the project-wide axiom allowlist, and replay all imported' \
      'proof declarations through the Lean kernel in a fresh environment.' \
      '' \
      "--fresh-build removes only this project's .lake/build directory first." \
      'It preserves the downloaded dependency sources and Mathlib cache.' \
      'Logs are written to .verification/.'
    exit 0
    ;;
  *) printf 'Unknown argument: %s\n' "$1" >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
  printf '%s\n' 'Pass at most one argument; see --help.' >&2
  exit 2
fi

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
for required_file in lean-toolchain lake-manifest.json BoundedArity.lean AxiomAudit.lean; do
  if [ ! -f "$required_file" ]; then
    printf 'Missing project file: %s\n' "$required_file" >&2
    exit 1
  fi
done
for required_command in lake git; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    printf 'Required command is not installed or not on PATH: %s\n' "$required_command" >&2
    exit 1
  fi
done

if [ "$fresh_build" = true ]; then
  printf '%s\n' "Removing this project's build outputs for a fresh source build."
  rm -rf -- "$project_root/.lake/build"
fi
report_dir="$project_root/.verification"
mkdir -p -- "$report_dir"
rm -f -- "$report_dir/PASS.txt"

printf '%s\n' '[1/5] Toolchain'
{
  lake env lean --version
  lake --version
  printf 'Expected toolchain: '
  cat lean-toolchain
} | tee "$report_dir/environment.txt"

printf '%s\n' '[2/5] Build; any warning is a failure'
lake --wfail build BoundedArity 2>&1 | tee "$report_dir/build.log"

printf '%s\n' '[3/5] Readable theorem and axiom audit'
lake env lean -DwarningAsError=true AxiomAudit.lean 2>&1 \
  | tee "$report_dir/declaration-audit.log"

printf '%s\n' '[4/5] Automatic project-wide axiom allowlist audit'
# The audit is a separate, dependency-free tool, compiled with this project's
# Lean version. Verify its exact commit as well as its human-readable tag.
audit_ref='v0.1.2'
audit_sha='46024e005996495c65ef609368e11ab39c4222e3'
audit_workdir="$(mktemp -d "${TMPDIR:-/tmp}/bounded-arity-axiom-audit.XXXXXX")"
trap 'rm -rf -- "$audit_workdir"' EXIT
git -c advice.detachedHead=false clone --depth 1 --branch "$audit_ref" \
  https://github.com/leanprover-community/axiom-audit.git "$audit_workdir/tool"
actual_sha="$(git -C "$audit_workdir/tool" rev-parse HEAD)"
if [ "$actual_sha" != "$audit_sha" ]; then
  printf 'Axiom-audit commit mismatch: expected %s; received %s\n' \
    "$audit_sha" "$actual_sha" >&2
  exit 1
fi
cp -- lean-toolchain "$audit_workdir/tool/lean-toolchain"
(
  cd -- "$audit_workdir/tool"
  lake --wfail build
) 2>&1 | tee "$report_dir/axiom-audit-tool-build.log"
printf '%s\n' "$audit_sha" > "$report_dir/axiom-audit-tool-commit.txt"
lake env "$audit_workdir/tool/.lake/build/bin/axiom-audit" \
  --root BoundedArity \
  --allow propext,Classical.choice,Quot.sound \
  --json | tee "$report_dir/axiom-audit.json"

printf '%s\n' '[5/5] Fresh-environment kernel replay, including imported declarations'
# This is the SAME Lean kernel used during compilation. --fresh starts an
# empty environment and checks the target plus its imports; without --fresh,
# the checker would trust the existing imported environment. The explicit
# module name matters because the Lake package is named bounded_arity.
LEAN_NUM_THREADS=1 lake env leanchecker --fresh --verbose BoundedArity 2>&1 \
  | tee "$report_dir/kernel-replay.log"

printf '%s\n' \
  'PASS: warning-free build, theorem audit, project-wide axiom allowlist,' \
  'and fresh-environment Lean kernel replay all succeeded.' \
  | tee "$report_dir/PASS.txt"
printf 'Verification logs: %s\n' "$report_dir"
