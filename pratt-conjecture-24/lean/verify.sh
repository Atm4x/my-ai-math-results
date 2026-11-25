#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
lean_bin="${1:-lean}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
"$lean_bin" --version
"$lean_bin" --trust=0 --error=warning -o "$tmp/Pratt.olean" Pratt.lean | tee "$tmp/verification.log"
grep -F "'Pratt.not_ValPrattConjecture24' depends on axioms: [propext, Classical.choice, Quot.sound]" "$tmp/verification.log" >/dev/null
if grep -E 'sorryAx|Lean\.ofReduceBool|Lean\.ofReduceNat|implementedBy' "$tmp/verification.log"; then
  echo 'Unexpected proof dependency' >&2
  exit 1
fi
echo 'PASS: full formal theorem and axiom audit.'
