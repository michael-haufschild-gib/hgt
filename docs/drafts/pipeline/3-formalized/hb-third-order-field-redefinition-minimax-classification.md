# HB third-order field-redefinition minimax classification

## Status

Paper proof and Lean formalization complete, 2026-08-28. Promoted to stage 3. Frontier map is read-only and remains untouched.

## Route

HB, auditing coordinate invariance of HC45--HC46 quantitative third-order `++-` channel burden.

## Failed conjecture

HC47-0 conjectured Einstein Taylor symmetries might select HC46's equipartition branch as physical. Corpus theorem `d4TeukolskyQuadraticFieldRedefinition_resonantProjection_eq` disproves this framing: total resonant source is invariant under quadratic perturbation-coordinate changes, but direct/cascade decomposition is not. Existing scalar countermodel changes direct vertex from `0` to `3/2`.

## Corpus basis

- `d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus_eq` gives exact transfer from cascade insertions into direct vertex.
- `d4TeukolskyQuadraticFieldRedefinition_resonantProjection_eq` proves total on-shell projection invariant.
- `d4TeukolskyQuadraticFieldRedefinedDirectProjection_eq_iff` classifies when direct channel alone is invariant.
- HC45--HC46 prove sharp one-third norm burden and unique equality configuration for every fixed three-channel decomposition.
- Corpus search found no affine redistribution orbit, minimax classification, or coordinate-invariant reformulation of HC45--HC46.

## HC47 conjecture

At projection level, quadratic field redefinition acts by

`(a,b,c) ↦ (a-δ, b-ε, c+δ+ε)`.

This preserves total exactly. Conversely any two triples with equal total are related by a unique pair `(δ,ε)`, so individual channel values and equipartition are not invariant. The positive invariant survivor is minimax:

- every representative cancelling target `t` has peak norm at least `‖t‖/3`;
- unique representative with all channel norms at most this threshold is equipartition `(-t/3,-t/3,-t/3)`;
- every equal-total orbit contains this unique minimax representative.

## Positive survivor

HC45's one-third existential burden is coordinate-independent even though channel identity is not. HC46 equipartition is reinterpreted as unique minimax gauge representative rather than a physical symmetry law. Literal source computation must therefore target total cokernel class plus gauge-fixing data; no individual cascade/direct coefficient can be used invariantly without that data.

## Bounded novelty audit

Search date: 2026-08-28. Primary-source search covered quadratic field-redefinition amplitude invariance in gravity (`arXiv:1309.5945`), AIME (`arXiv:2112.11168`), conserved QNM projections (`arXiv:2210.15935`), second-order Teukolsky nonlinear sources (`arXiv:2305.19332`), and nonlinear QNM excitation beyond GR (`arXiv:2404.11110`). Bounded search found no exact three-channel affine orbit, unique minimax equipartition, or BM/AIME one-third invariant classification. This is a bounded no-match finding, not exhaustive literature-wide novelty claim.

## Conjecture loop

- HC47-A: affine redistribution preserves total — proved in Lean.
- HC47-B: equal-total triples have unique redistribution coordinates — proved in Lean.
- HC47-C: equipartition is unique minimax orbit representative — proved in Lean.
- HC47-D: actual quadratic field-redefinition transfer law — proved in Lean.
- HC47-E: closed scalar no-go for direct-channel invariance with total invariance — proved in Lean.

## Lean artifact

`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderFieldRedefinitionMinimax`

All declarations are closed Lean proofs. No new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations are introduced.

## Verification audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMThirdOrderFieldRedefinitionMinimax.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderFieldRedefinitionMinimax`: passed, 12,752 jobs.
- `#print axioms` for all nine public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella; no umbrella build was run.
- Formal lint contains no HC47 error. Global lint remains red only on unrelated pre-existing or concurrently added unreachable owned modules.
