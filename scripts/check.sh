#!/bin/sh
# Project checks beyond `lake build`: no sorry, no axiom declarations, and the
# generated SBML import is up to date with its source.
set -eu
cd "$(dirname "$0")/.."

if grep -rnE '(^|[^`[:alnum:]_])sorry([^`[:alnum:]_]|$)' --include='*.lean' BioLib BioLib.lean \
    | grep -vE 'No `sorry`|no `sorry`'; then
  echo "error: sorry found" >&2
  exit 1
fi

if grep -rnE '^[[:space:]]*(private |protected )?axiom[[:space:]]' --include='*.lean' BioLib BioLib.lean; then
  echo "error: axiom declaration found" >&2
  exit 1
fi

python3 scripts/sbml_to_lean.py examples/sbml/enzyme.xml EnzymeMechanism \
  | diff - BioLib/Imported/EnzymeMechanism.lean

echo "checks passed"
