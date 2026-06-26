# Task Completion

- For Lean edits, run the narrowest affected `lake env lean <file>` first, then the relevant module build.
- For Böttcher changes, target `cd formal && lake build GaloisForLFunctions.Bottcher` when feasible.
- Check for proof debt with `rg -n "sorry|admit|axiom" formal/GaloisForLFunctions/Bottcher` after Böttcher work.
- For promoted theorem claims, use `/tmp` scratch files with `#print axioms <name>`; expected baseline is only `[propext, Classical.choice, Quot.sound]` unless the existing theorem already depends on more.