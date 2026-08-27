#!/usr/bin/env bash
#
# Best-effort guard against the specific way `ManyOneReduces` / `Undecidable`
# (DiagonaLean/Synthetic/Definitions.lean, DiagonaLean/Synthetic/Undecidability.lean) can be
# proved vacuously under Lean's classical logic: branching on an otherwise-undecided `Prop` to
# fabricate a reduction witness with no algorithmic content. See the docstring on
# `ManyOneReduces` for the full explanation.
#
# `Classical.propDecidable`, `Classical.byCases`, `Classical.choice`, and bare `Classical.dec`
# are exactly the primitives that can decide an arbitrary `Prop` out of thin air, so this bans
# them (in actual code, not comments) across the reduction-adjacent parts of the library. Other
# classical lemmas (`Classical.decEq`, `Classical.byContradiction`, ...) are unaffected and
# remain in normal use -- e.g. Halt/Undecidable.lean uses `Classical.decEq` to obtain
# `DecidableEq` on a TM's state type, which is a fact about the input *data*, not about the
# predicate being decided, and is fine.
#
# This is a textual tripwire, not a soundness proof: it will not catch classical case-splitting
# hidden behind tactics (e.g. `choose`) that don't mention these names literally. Treat a clean
# run as "no obvious vacuous witness," not as a guarantee.

set -euo pipefail

cd "$(dirname "$0")/.."

pattern='Classical\.(propDecidable|byCases|choice|dec)\b'
dirs=(DiagonaLean/Synthetic DiagonaLean/Halt DiagonaLean/*/Reductions)

existing_dirs=()
for d in "${dirs[@]}"; do
  [ -d "$d" ] && existing_dirs+=("$d")
done

# Blank out `/- ... -/` block comments (Lean also uses `/-- -/` and `/-! -/`, both matched by
# the same `/-`/`-/` markers) and `-- ...` line comments, so identifiers mentioned only in
# prose (like this script's own docstring, or the one on `ManyOneReduces`) don't trip the check.
# Doesn't handle nested block comments or `--`/`/-` inside string literals.
decomment() {
  awk '
    { line = $0; out = ""; i = 1; len = length(line)
      while (i <= len) {
        if (!incomment && substr(line, i, 2) == "/-") { incomment = 1; i += 2; continue }
        if (incomment && substr(line, i, 2) == "-/") { incomment = 0; i += 2; continue }
        if (!incomment) { out = out substr(line, i, 1) } else { out = out " " }
        i++
      }
      if (!incomment) {
        idx = index(out, "--")
        if (idx > 0) out = substr(out, 1, idx - 1)
      }
      print out
    }
  ' "$1"
}

fail=0
while IFS= read -r -d '' file; do
  hit=$(decomment "$file" | grep -nE "$pattern" || true)
  if [ -n "$hit" ]; then
    echo "$hit" | sed "s|^|$file:|"
    fail=1
  fi
done < <(find "${existing_dirs[@]}" -name '*.lean' -print0 2>/dev/null)

if [ "$fail" -ne 0 ]; then
  echo >&2
  echo "Found classical Prop-deciding primitives in reduction-adjacent code (above)." >&2
  echo "If this witnesses a ManyOneReduces/Undecidable proof, it likely has no algorithmic" >&2
  echo "content -- see the docstring on ManyOneReduces in DiagonaLean/Synthetic/Definitions.lean." >&2
  echo "If it's unrelated, move it out of these directories or use a lemma not in the banned" >&2
  echo "list (e.g. Classical.decEq)." >&2
  exit 1
fi

echo "No classical Prop-deciding primitives found in reduction-adjacent code."
