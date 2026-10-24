#!/bin/sh
# Check current observer capstone source and complete theorem dependencies.
set -eu
paper_dir="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
repo_dir="$(git -C "$paper_dir" rev-parse --show-toplevel)"
scratch_dir="$(mktemp -d /tmp/quantum-recurrence-axioms.XXXXXX)"
scratch="$scratch_dir/Audit.lean"
trap 'rm -f "$scratch"; rmdir "$scratch_dir"' EXIT HUP INT TERM
python3 - "$repo_dir" "$paper_dir" "$scratch" <<'PY'
from pathlib import Path
import sys
repo, paper, scratch = map(Path, sys.argv[1:])
source = repo / "formal/GaloisForLFunctions/HTGeometry/ConnectedNetworkAllObserverRecurrenceLaw.lean"
names = (paper / "audit/declarations.txt").read_text().splitlines()
imports = (
    "import GaloisForLFunctions.RHTower.UniversalStationaryRecurrenceLaw\n"
    "import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw\n"
)
scratch.write_text(imports + source.read_text() + "\n" +
                   "".join("#print axioms " + name + "\n" for name in names))
PY
cd "$repo_dir/formal"
lake --old env lean "$scratch"
