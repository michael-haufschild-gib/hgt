# Actual unit-averaged Hecke theta Mellin continuation

- **ID:** actual-unit-averaged-hecke-theta-mellin-continuation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** Integrate both actual Hecke theta families over the actual global-unit fundamental domain and prove their continued Mellin functional equation with exact regulator-scaled residues.

## Exact result

Let `D` be the actual weighted unit-log parallelepiped, `y(x)` its completed
weighted-zero profile, and `R_K=volume(D)` the regulator. Define

`F(t)=∫_D Θψ,b(y(x),t)` and `G(t)=∫_D Θdualψ,b(-y(x),t)`.

Both are continuous for `t>0`. Their zero modes are `R_K*cphysical` and
`R_K*cdual`; the remaining tails decay exponentially. The actual inversion is

`F(1/t)=A(0)*t^κ*G(t)`, where `κ=[K:ℚ]/2+parityDegree`.

Every field of the associated Mellin pair is proved from this actual data.
Its continuation equals the convergent Mellin integral on `Re z>κ`, is
holomorphic away from `0,κ`, and has residues `-R_K*cphysical` and
`A(0)*R_K*cdual`. Its regular part is entire. Nonzero parity removes both
poles. The exact change `z=([K:ℚ]*s+parityDegree)/2` gives reflection `s ↦ 1-s`.

## Dependency-closed proof

Joint theta continuity gives integrability on the compact closure of the
actual domain. For continuity of the parameter integral near any positive
parameter, clamp the parameter below a smaller positive threshold; compact
parametric integration then applies with the restricted domain measure.
The proved uniform exponential tails and the actual finite positive domain
volume give the averaged tails. Weighted-zero profiles make the arithmetic
Poisson scalar constant, so pointwise inversion integrates exactly.
The resulting actual fields discharge Mathlib's `WeakFEPair` constructor;
no analytic premise or unproved interface remains in the public construction.

## Lean and verification

[HeckeThetaAveragesOverTheUnitDomain.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeThetaAveragesOverTheUnitDomain.lean)
contains the actual averages, weighted-unit covariance and periodicity,
unit-domain integrability, positive-parameter continuity, exponential tails,
constant Poisson scalar, and averaged reciprocal identity. Main continued
transform declarations:

- `heckeUnitThetaMellinPair`
- `heckeUnitThetaMellinContinuation`, `heckeUnitThetaMellinRegularPart`
- `differentiable_heckeUnitThetaMellinRegularPart`
- `differentiableAt_heckeUnitThetaMellinContinuation`
- `hasMellin_heckeUnitAveragedTheta`
- `heckeUnitThetaMellinContinuation_residue_zero`
- `heckeUnitThetaMellinContinuation_residue_weight`
- `heckeUnitThetaMellinPair_isStrong_of_parity_ne_zero`
- `differentiable_heckeUnitThetaMellinContinuation_of_parity_ne_zero`
- `heckeUnitThetaMellinContinuation_reflection`

The complete scratch passes without warnings. Five main transitive audits and
one additional domain-volume positivity audit contain only `propext`,
`Classical.choice`, and `Quot.sound`. The final direct `lake --old env lean`
source audit passes without warnings. The module is wired into the Hecke
umbrella; no umbrella was compiled. No proof limit was raised. Explicit
coordinate maps resolve composition elaboration. Both dependency oleans are
built. The completed scratch is removed; no olean for this module is needed yet.

## Remaining identification

This is an actual **unit-averaged theta** Mellin theorem. The unit-orbit
bijection, absolute Tonelli/Fubini argument, exact Gamma normalization and
identification with the ideal Hecke series remain open. Ordinary class-character
residue cancellation and primitive Gauss evaluation also remain open. No full
Hecke continuation or primitive functional equation is claimed here.
