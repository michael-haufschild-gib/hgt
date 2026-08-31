# CCM-FU first-moment Abel transfer (2026-08-31)

Formalized in `formal/GaloisForLFunctions/RHTower/SuzukiFirstMomentTriangularAbelTransfer.lean`, wired into `RHTower.lean`.

New closed chain:
- `CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound`: `|suzukiCheckpointWeightedSignedCurvaturePrefix N| = O(N)`.
- Generic `HTGeometry.abs_sum_mul_weight_le_of_linear_partialSum` controls summable reciprocal-scale reporters without Jordan decomposition.
- Exact `suzukiCheckpointTriangularCurvatureTransform_eq_reciprocalLogSums` splits CCM-FU triangular kernel into signed `1/(k log^3 k)` and `1/(H k log^2 k)` Abel channels.
- `ccmFUSuzukiTriangularCurvatureTransformBound_of_weightedFirstMomentLinearBound` discharges full triangular-transform premise.
- `weightedFirstMomentLinearBound_of_unitRieszCentralBarycenterNaturalBound` uses exact unit-Riesz landing plus archimedean `O(sqrt N)` renormalization.
- RH capstones: `riemannHypothesis_of_suzukiWeightedCurvatureFirstMomentLinearBound`, `riemannHypothesis_of_unitRieszCentralBarycenterNaturalBound`.

Research card promoted to `docs/drafts/pipeline/3-formalized/suzuki-first-moment-triangular-abel-transfer.md`. Frontier map untouched.

Validation: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.SuzukiFirstMomentTriangularAbelTransfer` passed (11639 jobs); capstone axiom audit only `propext`, `Classical.choice`, `Quot.sound`. Global lint has only unrelated concurrent umbrella-reachability errors; new module reachable and has no forbidden declarations.

Remaining arithmetic burden: prove linear growth of exact weighted curvature first moment, equivalently enough natural-aperture control on central unit-Riesz incoming barycenter. This is source-specific and RH-bearing; analytic CCM-FU transfer is now closed.

Related memory: `mem:research/ccm_fu_triangular_curvature_reduction_2026_08_31`.