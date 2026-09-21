# PW-B full-circle CTP reflection orientation

- **ID:** pw-b-full-circle-ctp-reflection-orientation
- **Stage:** 3-formalized
- **Type:** SIGNIFICANT PREMISE DISCHARGED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B literal cyclic-Peierls source bridge

## Result

For the literal full direct-minus-image circle kernel, the equal-amplitude complementary-branch two-event CTP numerator obeys
`C(1-q, branch) = -C(q, !branch)`.

## Consequence for the whole route

PW forward/reverse real Borel imbalance is reflection odd. The literal full CTP source now has exactly that orientation parity without a scalar proxy, same-rate collapse, or boundary premise. The remaining PW-B source burden is strictly narrower: prove its cap/lift-defect boundary transport is a nonzero real multiple of the fixed-grade PW imbalance. No parity-selection law remains open.

## Formal evidence

- `fullCircleCrossBranchCausalPair_reflection_odd` is closed by source-field reflection, circular-kernel reflection, and literal reversal of the two CTP integrals.
- `angularMean_reflect`, `angularDirichletKernel_reflect`, and `fullCircleSourcePairDensity_reflect` make all source transformations explicit.
- Direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularSourceReflection.lean` passed on 2026-09-21.
- Leaf OLean audit remains pending: targeted `lake build` incorrectly replayed over 12,000 unrelated modules and was stopped under the no-long-build rule.
