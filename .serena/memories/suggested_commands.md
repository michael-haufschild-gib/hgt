# Suggested Commands

- Check whole Lean library: `cd formal && lake build GaloisForLFunctions`.
- Check Böttcher tower only: `cd formal && lake build GaloisForLFunctions.Bottcher`.
- Formal overview: `scripts/formal_tools.py status` from repo root, or read `formal/LEAN_OVERVIEW.md`.
- Research declarations/gaps first: `scripts/formal_tools.py research "<query>"`.
- Regenerate generated formal indexes after declaration moves/additions: `scripts/formal_tools.py index`.
- Local formal lint: `scripts/formal_tools.py lint --check-generated`.
- Check one Lean file/module by module import path, e.g. `cd formal && lake env lean GaloisForLFunctions/Bottcher/LogPotential.lean` for direct file diagnostics.
- Probe mathlib names/axioms in scratch files outside the tree: `cd formal && lake env lean /tmp/x.lean`.
- Search code with `rg`; prefer `rg --files formal` for file discovery.
