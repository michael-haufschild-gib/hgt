# NHG Stage 3 promotion (2026-08-13)

- Audited all 26 cards formerly under `docs/drafts/pipeline/2-fully-proven/nomological-homotopy-geometry`.
- Exact Lean theorem witness exists for every card.
- Added `GaugeSpectralFlow.lean` (committed concurrently as 6c7f4a918) with unitary conjugation, inertia invariance, gauge-invariant crossing form, and pure-gauge rigidity.
- Added missing `MinimalLawLeadingJet` import to `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry.lean`.
- Verification:
  - `lake build +GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.GaugeSpectralFlow` passed.
  - `lake build +GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry` passed.
  - Scratch `#print axioms` audit for one exact capstone per card (26 total) passed; only standard `propext`, `Classical.choice`, `Quot.sound`.
  - Scoped forbidden-declaration scan found no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations in NHG/CrossGram.
  - Full `scripts/formal_tools.py lint` was run, but global lint failed only on unrelated concurrently added/unwired RHTower and HTGeometry modules; NHG umbrella built successfully.
- Moved all 26 cards to `docs/drafts/pipeline/3-formalized/nomological-homotopy-geometry`, updated every header/status, documented four previously stale cards, repointed all 26 inbound foundation links, and added promotion-ledger row.
- No commit/push performed by this agent. Worktree remains shared and dirty with other agents' changes.
