# Route A terminal positive-transport classification — 2026-08-01

## Status
Route A in `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is terminalized as an independent source-producing mechanism, while retained honestly as an exact RH coordinate. RH and its negation remain unproved.

## New formal knowledge
1. `RHTower/CCMFirstClockPhaseNaturalTransportRigidity.lean`
   - A fixed source-faithful finite matrix natural for every physical phase `sin(2π h_i/L)` is identity.
   - Explicit pair-separating aperture: `L=4(h_i+h_j)`.
   - Every nonidentity source-faithful mixer has an explicit nonzero phase-connection defect.
   - Literal duplicate-free prime-power specialization is formalized.
2. `RHTower/CCMFirstClockBarycentricOrientationCompleteness.lean`
   - For finite nonnegative source `w` with positive total mass, existence of a column-stochastic `M` with `Mw=w` and coordinatewise `Mᵀs≥0` iff `w·s≥0`.
   - Canonical rank-one witness: `M_ij=w_i/Σw`; its dual output is constant `(w·s)/Σw`.
   - Completed CCM packet uses Option anchor: continuous half-wave budget at none, critical Mellin weights at arithmetic coordinates.
   - Exact endpoint: `ccmFirstClockAllCompletedMarkovOrientations_iff_rh`.

## Anti-theatre conclusion
Fixed physical-phase intertwiners collapse to identity. Arbitrary aperture-dependent positive source-faithful Markov mixers are feasible exactly when target source scalar already has desired sign. Neither is an independent RH predecessor. Strongest survivor is signed phase-connection current; any attempt needs a new route and source-first orientation theorem.

## Pipeline
- Formalized cards:
  - `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-first-clock-phase-natural-transport-rigidity.md`
  - `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-first-clock-source-faithful-barycentric-orientation-completeness.md`
- Failed/retired attack:
  - `docs/drafts/pipeline/5-failed/ccm-first-clock-direct-positive-factorization-attack.md`
- Frontier map and SOTA narrative updated.
- Both modules wired into `RHTower.lean` and `RiemannHypothesisSOTA2026.lean`.

## Verification
- Both module direct checks passed with `lake env lean <file>`.
- Final SOTA build passed 9,960 jobs (this was broader than necessary; future audits should build only changed module).
- Scratch `#print axioms` for load-bearing endpoints: only `propext`, `Classical.choice`, `Quot.sound`.
- Targeted forbidden-token scan clean; `git diff --check` clean.
- Repository-wide lint was attempted twice but concurrent unrelated new modules were temporarily unreachable from umbrellas. Route A modules themselves are reachable from both umbrellas.
- No numerical computations used.
