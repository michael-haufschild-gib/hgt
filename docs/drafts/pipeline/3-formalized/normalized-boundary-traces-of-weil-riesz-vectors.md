# Normalized boundary traces of Weil Riesz vectors

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every actual precontact Fourier evaluation Riesz source has a unique continuous compactly supported physical representative, vanishing outside the open aperture. Both normalized endpoint limits exist and equal absolutely convergent renewal readouts.

## Theorem

For `a<a*(ζ)` and `z∈ℂ`, let `u_z` denote the actual evaluation Riesz source.
There is a unique continuous `U_z=u_z` almost everywhere. It vanishes for
`x≤-a` and `x≥a`, and

`U_z(t-a) sqrt(log(1/t)) → ∫₀∞ v(y) f₋,z(y) dy`,

`U_z(a-t) sqrt(log(1/t)) → ∫₀∞ v(y) f₊,z(y) dy`

as `t↓0`. Both integrals converge absolutely. Here `v` is the actual causal
logarithmic probability density and `f±,z` are the complete localized
forcings, including the finite prime sum and both polar terms.

## Proof

The [actual endpoint localizations](the-weil-riesz-vectors-localize-to-the-logarithmic-half-line.md)
are unique half-line logarithmic Green solutions with bounded L² forcings.
Their continuous representatives `L,R` vanish on the nonpositive half-line.
For `χ_a(x)=min(max(3-2x/a,0),1)`, define

`U_z(x)=(L(x+a)+R(a-x))/(χ_a(x+a)+χ_a(a-x))`.

The denominator is at least one. The localized source identities prove
`U_z=u_z` almost everywhere. Continuity and full support of Lebesgue measure
upgrade both cutoff identities to pointwise identities and prove uniqueness.
Near each endpoint the corresponding cutoff is one, so the exact Green
boundary limit transfers to `U_z`. Its vanishing outside the open aperture
gives compact support.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheWeilRieszVectorsHaveNormalizedEndpointTraces.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact`.

- `evalVectorContinuousRepresentative_ae`
- `evalVectorContinuousRepresentative_unique`
- `evalVectorEndpointReadouts_integrable`
- `evalVectorContinuousRepresentative_eq_zero`
- `hasCompactSupport_evalVectorContinuousRepresentative`
- `evalVectorContinuousRepresentative_left_normalized_limit`
- `evalVectorContinuousRepresentative_right_normalized_limit`

Transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`.
Production plain audit passed. Umbrella imports the module.

## Remaining canonical-system inputs

[Boundary flux and support variation](../1-in-progress/boundary-flux-generates-the-weil-canonical-system.md),
origin normalization and prime-entry laws remain separate. Trace existence
alone asserts none of those identities.
