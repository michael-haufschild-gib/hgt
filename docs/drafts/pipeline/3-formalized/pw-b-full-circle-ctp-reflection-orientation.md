# PW-B full-circle CTP reflection orientation

- **ID:** pw-b-full-circle-ctp-reflection-orientation
- **Stage:** 3-formalized
- **Type:** SIGNIFICANT PREMISE DISCHARGED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B literal cyclic-Peierls source bridge

## Result

For the literal full direct-minus-image circle kernel, the equal-amplitude complementary-branch two-event CTP numerator obeys
`C(1-q, branch) = -C(q, !branch)`.  Its physical two-branch completion
`CΣ(q) = C(q, true) + C(q, false)` is branch-free and obeys
`CΣ(1-q) = -CΣ(q)`; therefore `Re CΣ(1-q) = -Re CΣ(q)`.

## Consequence for the whole route

PW forward/reverse real Borel imbalance is reflection odd. The literal full CTP source now has a branch-free scalar with exactly that orientation parity, without a scalar proxy, same-rate collapse, or boundary premise. This closes branch selection, but not critical-line detection: reflection sends `q` to `1-q`, reversing its imaginary coordinate. The remaining PW-B source burden is therefore prove a critical-fibre conjugation/invariance law for `Re CΣ`, or directly prove its normalized cap/lift-defect transport is a nonzero real multiple of fixed-grade PW imbalance.

## Formal evidence

- `fullCircleCrossBranchCausalPair_reflection_odd` is closed by source-field reflection, circular-kernel reflection, and literal reversal of the two CTP integrals.
- `fullCircleCrossBranchSymmetricCausalPair_reflection_odd` and its real-part corollary extract the forced two-branch, branch-free PW-oriented scalar.
- `divisorReflectionOddReal_not_sufficient_for_balance` formally rules out a parity-only inference; `divisorReflectionOddReal_eq_zero_of_criticalFiberInvariant` gives the exact positive survivor.
- `fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_iff_conjInvariant_on_critical` refines that survivor: at a critical divisor copy, source cancellation is equivalent to invariance of its real part under the canonical Schwarz conjugate copy.
- `angularMean_reflect`, `angularDirichletKernel_reflect`, and `fullCircleSourcePairDensity_reflect` make all source transformations explicit.
- Direct `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFullAngularSourceReflection.lean` passed on 2026-09-21.
- Leaf OLean audit remains pending: targeted `lake build` incorrectly replayed over 12,000 unrelated modules and was stopped under the no-long-build rule.
