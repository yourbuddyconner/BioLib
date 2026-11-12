#!/bin/sh
# Download public reference OTU tables used for simulator realism checks.
# Source: Knights Lab MLRepo (https://github.com/knights-lab/MLRepo, MIT licence).
# Files go to data/reference/, which is not tracked by git.
set -eu
cd "$(dirname "$0")/.."
base=https://raw.githubusercontent.com/knights-lab/MLRepo/master/datasets
for ds in yatsunenko gevers; do
  mkdir -p "data/reference/$ds"
  for f in gg/otutable.txt mapping-orig.txt; do
    out="data/reference/$ds/$(basename "$f")"
    [ -s "$out" ] || curl -fsSL --retry 3 -o "$out" "$base/$ds/$f"
  done
done
ls -la data/reference/*
