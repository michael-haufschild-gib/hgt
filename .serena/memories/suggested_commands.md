# Suggested Commands

- Check whole Lean library: `cd formal && lake build GaloisForLFunctions`.
- Check Böttcher tower only: `cd formal && lake build GaloisForLFunctions.Bottcher`.
- Check one Lean file/module by module import path, e.g. `cd formal && lake env lean GaloisForLFunctions/Bottcher/LogPotential.lean` for direct file diagnostics.
- Probe mathlib names/axioms in scratch files outside the tree: `cd formal && lake env lean /tmp/x.lean`.
- Search code with `rg`; prefer `rg --files formal` for file discovery.