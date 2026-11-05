# The logarithmic factor has its reflection identity

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual slit-plane factor satisfies `κ(z)κ(-z)=1+(1/2)Log(1-z²)` for every nonreal `z`, and `|κ(iy)|²=1+(1/2)log(1+y²)` for every nonzero real `y`. Its reciprocal tends uniformly to zero at infinity over all nonreal directions.

## Proof

Write `Ψ(t)=1+(1/2)log(1+t²)`. The slit-plane factor and the
right-half-plane integral

`exp((1/π)∫₀∞ z log Ψ(t)/(z²+t²)dt)`

are holomorphic and agree for positive real parameters. Analytic uniqueness
identifies them. Real-part partial fractions and reflection of the negative
half-line give

`|κ(x+iy)|²=exp((1/π)∫ℝ log Ψ(y+xu)/(1+u²)du)`, `x>0`.

For `0<x≤1`, the numerator is bounded above by
`log(2+2y²)+log(1+u²)`. This gives an integrable majorant, so dominated
convergence sends the exponent to `log Ψ(y)` as `x↓0`. Slit-plane
continuity gives the exact boundary modulus when `y≠0`.

Conjugation gives `κ(iy)κ(-iy)=Ψ(y)`. Both sides of the stated reflection
identity are holomorphic on the upper half-plane, so analytic uniqueness
extends it from the positive imaginary axis. Conjugation gives the lower
half-plane identity.

For `Re z>0`, the symbol comparison `Ψ(t)≤Ψ(R)(1+t²/R²)` and
`(Im z+Re z·u)²≤|z|²(1+u²)` give `|κ(z)|²≤CΨ(|z|)` with finite
universal `C`. When `Im z≥0`, the interval `1≤u≤2` gives the lower bound
`|κ(z)|²≥exp(log Ψ(|z|)/(5π))`. Conjugation treats the other sign.
Thus the reciprocal vanishes uniformly on the right. On the left,
reflection gives `1/κ(z)=κ(-z)/(1+(1/2)Log(1-z²))`; for `|z|≥2`,
the denominator has norm at least `(1/2)log|z|`. The upper bound and
`Ψ(R)/log R→1` give uniform reciprocal decay there as well.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicFactorHasItsReflectionIdentity.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `complexLogReferenceFactor_eq_right`
- `tendsto_logarithmic_poisson_boundary`
- `complexLogReferenceFactor_norm_sq`
- `complexLogReferenceFactor_imaginary_norm_sq`
- `complexLogReferenceFactor_reflection`

`TheReciprocalLogarithmicFactorVanishesAtInfinity.lean` proves
`complexLogReferenceFactor_norm_sq_le`, `complexLogReferenceFactor_norm_sq_lower`,
and `tendsto_inv_complexLogReferenceFactor_nonreal`.

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
Stieltjes inversion, the causal inverse, and the Green identity remain open
on the [half-line kernel card](../1-in-progress/the-half-line-logarithmic-green-kernel.md).
