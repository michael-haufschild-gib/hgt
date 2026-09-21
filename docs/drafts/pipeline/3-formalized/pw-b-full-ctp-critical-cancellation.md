# PW-B literal full-circle CTP critical cancellation

- **ID:** pw-b-full-ctp-critical-cancellation
- **Stage:** 3-formalized
- **Proof chain:** original-time source → two-event full-circle density → ordered cross-branch CTP pair → branch completion → critical-fibre real cancellation → normalized PW magnitude → partner balance → RH

## Closed theorem

`fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_on_critical` proves, for every
`q : XiZeroCopy`, `X k : ℝ`, and
`(deningerDivisorThetaEigen q).re = 1/2`, that the literal unit-amplitude
branch-completed full-circle CTP source has real part zero.

## Dependency-closed mechanism

`fullCircleSourcePairDensity_conj` transports both exact
`timeReducedCoefficient` legs, the fundamental `physicalRate`, and the literal
direct-minus-image angular kernel. Product-measure conjugation transports each
ordered cross-branch CTP integral. Their sum is conjugation invariant; the
pre-existing critical-fibre reflection/conjugation iff converts this to real
cancellation. No phase scalar, hypothesis, or axiom is introduced.

## Lean status

- Source: `ThetaCuspHawkingBMFullAngularCTPSchwarz.lean` and
  `ThetaCuspHawkingBMFullAngularCTPCriticalCancellation.lean`.
- Direct source audits and direct needed Olean emission passed.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella not built.
- `#print axioms` inspection import exceeded two 240-second caps without output;
  do not state a completed transitive-axiom report until this operational audit is repaired.

## Remaining route burden

Prove the literal normalized cap/lift-defect magnitude identity yielding the
fixed-grade PW imbalance. Only then can PW partner balance and RH follow.
