# Universal scalar Narain zero at half

- **ID:** W11-NZ
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** The apparent scalar Mellin singularity at `s=1/2` is
  removable and its value is zero for every target pair.

## Proof

The entire filled numerator satisfies `T_z(0)=0`. Its removable divided
difference `S_z(u)=T_z(u)/u` is entire. Therefore the main-pole numerator
has the globally equal representation

`A(u)=u S_ρ(u)S_σ(u)/[2(1+2u)ξ(1+2u)]`.

This denominator is nonzero at zero, where `ξ(1)=1/2`, and `A(0)=0`.
Since `u−1/2` is also nonzero there, `M(u)=A(u)/(u−1/2)²` is analytic and
vanishes at zero. The equality includes zero: both existing totalized
quotients have value zero there.

The same representation makes `A` holomorphic wherever
`(1+2u)ξ(1+2u)≠0`, removing the artificial exclusion of zero from the
principal-part remainder's domain. This is needed for contour shifts
through `s=1/2`; it proves no arithmetic zero-free region.

Corpus search found the filled-numerator zero and general analytic divided
differences, but no earlier scalar Narain specialization.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/NarainCentralZero.lean`.

- `narainMainPoleNumerator_eq_reduced`: global equality with the reduced quotient.
- `analyticAt_narainMainPoleNumerator`: enlarged analytic domain.
- `analyticAt_narainMellinContinuation_zero`, `narainMellinContinuation_zero`:
  the analytic extension and its universal zero.

The direct `lake --old env lean` check passes without warnings.
All four endpoint axiom audits contain only `propext`, `Classical.choice`,
`Quot.sound`. The topic umbrella imports the module.

## Gates

- [x] 0 → 1: exact cancellation and enlarged analytic domain identified.
- [x] 1 → 2: pointwise quotient equality and removable extension.
- [x] 2 → 3: direct Lean check, axiom audits and umbrella import.
