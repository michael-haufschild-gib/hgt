# Exact radial/logarithmic Jacobian for Hecke Mellin unfolding

- **ID:** hecke-radial-logarithmic-jacobian
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke theta Mellin unfolding](../1-in-progress/hecke-theta-mellin-continuation-and-unit-unfolding.md)
- **Statement:** The actual map `(q,l) ↦ (q-P(l)_v)_v` pushes product Lebesgue measure forward to `2^r₂/[K:Q]` times place-coordinate Lebesgue measure, with exact nonnegative and complex integral formulas and equivalence of absolute integrability.

## Dependency-closed proof

Write `m_v` for the actual place multiplicity and `W=sum m_v=[K:Q]`.
The existing profile map `P` completes all but the distinguished coordinate
to a weighted-zero place profile. Completing `(m_v*f_v)_{v≠w₀}` recovers
any weighted-zero profile `f`: retained coordinates cancel their positive
multiplicities, and the weighted-zero sum determines the omitted coordinate.

Store the radial logarithm in the distinguished coordinate of the full
place-coordinate space. The linear map `E(x)_v=x(w₀)-P(x|off)_v` has inverse
`T(z)(w₀)=weightedMean(z)` and
`T(z)(v)=m_v*(weightedMean(z)-z_v)` off that place.
The completion lemma proves both inverse identities.

The inverse matrix is `diagonal d + vecMulVec u m`, where `d(w₀)=0`,
`d(v)=-m_v` elsewhere, `u(w₀)=1/W`, and `u(v)=m_v/W` elsewhere.
The existing corpus theorem `bgv_det_diagonal_add_vecMulVec` evaluates its
determinant. The diagonal product vanishes, and every rank-one sum term
except the distinguished term contains the zero diagonal entry. Hence

`det T = (m_w₀/W) * prod_(v≠w₀) (-m_v)`.

Taking absolute values gives `|det T|=(prod m_v)/W=2^r₂/[K:Q]`.
The existing degree identity is reused from
`NumberFieldArchimedeanCanonicalDeterminant.lean`; the multiplicity product
splits over real and complex places, contributing respectively one and two.

Splitting off the distinguished coordinate preserves Lebesgue measure:
split the finite product by the singleton predicate, then collapse its
singleton-coordinate factor. The two finite enumerations of that singleton
are identified by the subsingleton property of `Fintype`; no measure equality
is assumed. The linear Haar pushforward theorem now proves the exact measure
identity for `(q,l) ↦ q-P(l)`.

The map is a measurable embedding. Its measure identity gives nonnegative
and complex integral formulas. Its density is finite and strictly positive,
so a function is integrable in place coordinates exactly when its pullback
is integrable in radial/unit-log coordinates.

## Lean declarations and audit

Module: `GaloisForLFunctions/HTGeometry/NumberFieldRadialLogarithmicJacobian.lean`.

- `numberFieldWeightedLogProfile_complete`
- `numberFieldRadialLogEquiv`, with explicit forward and inverse formulas
- `abs_det_numberFieldRadialLogEquiv_symm`
- `abs_det_numberFieldRadialLogEquiv`
- `prod_numberFieldInfinitePlace_mult`
- `measurePreserving_numberFieldRadialLogSplit`
- `map_numberFieldRadialLogParam_volume`
- `lintegral_numberFieldRadialLogParam`
- `integrable_numberFieldRadialLogParam_iff`
- `integral_numberFieldRadialLogParam`

Seven main transitive axiom checks return only `propext`, `Classical.choice`,
and `Quot.sound`. Final source audit passed without warnings:

`lake --old env lean GaloisForLFunctions/HTGeometry/NumberFieldRadialLogarithmicJacobian.lean`

The module is wired into the geometry umbrella; no umbrella was compiled.

## Remaining application

The substitution `t=exp(2q)` supplies an additional factor two in the Mellin
integral. Its existing corpus theorem is source-checked, but the actual Hecke
kernel application, Gamma evaluation, and ideal-series exchange belong to
[the formalized archimedean Mellin card](hecke-archimedean-mellin-integrals.md).
These are not claimed by the Jacobian module.
