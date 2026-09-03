Active four-card /goal remains incomplete and active. This continuation made concrete Schanuel progress.

New generic leaf:
- formal/GaloisForLFunctions/HTGeometry/ComplexPointRationalSmoothPath.lean
- Defines AlgebraicGeometry.Scheme.ComplexPointPath.IsRationallySmooth: every function-field element with a regular germ at every point has C∞ evaluated pullback.
- contDiff_value theorem.
- Direct check, targeted build passed; wired into HTGeometry.

Extended:
- formal/GaloisForLFunctions/HTGeometry/BaseFieldPointComplexification.lean
- New exact generic declarations:
  - Scheme.BaseFieldPointOver.toComplexPoint_center
  - Scheme.ComplexPoint.stalkEval_transport
  - Scheme.specFieldStalkEquiv_apply
  - Scheme.Hom.stalkMap_germ_apply
  - Scheme.specMap_stalkEval
  - Scheme.BaseFieldPointOver.stalkEvalAtComplexCenter
  - Scheme.BaseFieldPointOver.toComplexPoint_stalkEval
- These prove complexified stalk evaluation is literally algebraMap k C of base-field evaluation.
- Direct check and targeted leaf build passed.

New global Schanuel leaf:
- formal/GaloisForLFunctions/RHTower/SchanuelStageTwoDefectSlopeProjectiveRationalSmoothPath.lean
- StageTwoProjectiveRationallySmoothDivisorAvoidingPath is global on actual proper projective normalization, not confined to one affine chart.
- Path carries rational smoothness, actual AlgNum source point and source factorization, smooth-source condition, canonical target, order, divisor avoidance.
- Coordinate derivatives and continuous derivatives are derived.
- Algebraic source coordinate values are now derived via toComplexPoint_stalkEval, not supplied.
- Target x/exp x values are derived from canonical target.
- exists_stageTwoProjectiveRationallySmoothPathRegulatorWitness.
- StageTwoDefectSlopeRationalSmoothProjectivePackage and unconditional capstones under original hx/hlt (plus extraction-failure form).
- Direct check and targeted leaf build passed; wired into RHTower.
- All new declarations audited exactly [propext, Classical.choice, Quot.sound].
- Schanuel card appended truthfully.

Exact remaining mismatch: prove ordinary smooth complex-analytification paths imply IsRationallySmooth (forward comparison suffices). Current corpus/mathlib lacks global projective analytification/manifold interface. Do not rename rational smoothness as ordinary smoothness or promote card without comparison.

Workflow: required formal_tools.py research was used before corpus work; no umbrella/full build. Scoped git diff --check passed. No scratch Hgt files remain. Our Lean processes ended; an unrelated external Claude process was visible and must not be killed.

Other exact blockers unchanged:
- centralizer: Strong-Atiyah/free-field evaluation-kernel mass = inner-rank defect.
- differential: global noncommutative Cartan/building CAT(0)/boundary flags.
- cascade: valuative analytic finite Puiseux selection plus RatIn/response bounds.
