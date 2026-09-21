# PW-B reflection-parity-only source bridge

- **ID:** pw-b-reflection-parity-only-source-bridge
- **Stage:** 5-failed
- **Type:** SIGNIFICANT SUBROUTE KILLED; POSITIVE SURVIVOR FORMALIZED
- **Source:** PW-B literal cyclic-Peierls CTP source bridge

## Killed mechanism

The inference
`functional-equation odd CTP orientation → zero on critical line → PW partner balance`
is invalid.  Reflection is `q ↦ 1-q`, not pointwise fixing a divisor copy on
`Re q=1/2`: it reverses the nonzero imaginary coordinate.

Lean constructs the decisive witness `F(q)=Im q`.  It obeys
`F(1-q)=-F(q)` and is nonzero for every actual Xi-divisor copy.  Consequently,
no argument using only source reflection oddness can establish PW balance.

## Positive survivor

For any real reflection-odd divisor observable `F`, Lean proves that
`F(q)=0` on the critical fibre if the additional, exact condition
`F(1-q)=F(q)` holds there.  For the literal branch-completed source `Re CΣ`,
Lean sharpens this to an equivalence: because the reflected and Schwarz
conjugate divisor copies coincide on that fibre,
`Re CΣ(q)=0 ↔ Re CΣ(conj q)=Re CΣ(q)`.  Thus Schwarz invariance is the exact
source-real-structure target; the stronger cap/lift-defect normalized
magnitude law to PW imbalance would imply it and close the full PW-B chain.

## Formal evidence

- `divisorReflectionOddReal_not_sufficient_for_balance` is a closed Xi-divisor
  counterexample, using `xi_divisor_support_im_ne_zero`.
- `divisorReflectionOddReal_eq_zero_of_criticalFiberInvariant` is the
  dependency-closed positive survivor.
- `fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_iff_conjInvariant_on_critical`
  specializes it to the literal full-circle source using the canonical
  multiplicity-exact Schwarz divisor transport.
- Direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularSourceReflection.lean` passed on 2026-09-21.
- No OLean audit was attempted after the required amplitude dependency's leaf
  build immediately replayed more than 12,000 unrelated modules and was
  stopped under the no-long-build rule.
