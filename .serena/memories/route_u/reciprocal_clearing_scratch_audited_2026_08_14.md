# Route U reciprocal-clearing module completed

- Lean module: `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeReciprocalClearingHyperbolicity.lean`.
- Proves complex evaluation, exact pole value, full pole/non-pole zero classification, generic real-root transfer, canonical first-face pole exclusion, and canonical cleared-root reality.
- Wired into `formal/GaloisForLFunctions/RHTower.lean`.
- Research card promoted to `docs/drafts/pipeline/3-formalized/route-u-hard-edge-reciprocal-clearing-root-classification.md`.
- Exact checked-in source compiled to `/tmp/route_u_reciprocal_clearing_source.olean`; scratch import checked all six theorems.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`; target file has no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- No `lake build` was run after user correction. Permanent policy for this task: validate with isolated scratch Lean objects/files only, then wire umbrella; do not run full/named builds.
- Scratch import initially hit stale missing objects. They were compiled only into `/tmp/route_u_lean_overlay`; project build tree was untouched.
- Next substantive Route-U candidate: compose `XiShiftedFilteredGammaTransmutation` with `XiPolynomialGaussianExplicitFormula` to expose the cofinal finite-Hankel packet as an exact literal filtered prime–Gamma time integral before divisor aggregation. Then attack an unconditional sign/finite-capital bound; avoid scalar budgets already killed by countermodels.
- Goal remains unconditional Lean RH; reciprocal classification is a bridge, not RH.