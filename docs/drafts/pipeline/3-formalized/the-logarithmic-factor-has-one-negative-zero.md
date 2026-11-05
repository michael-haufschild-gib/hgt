# The logarithmic factor has one negative zero

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The logarithmic factor continues holomorphically to `ℂ \ (-∞,-1]`, takes value one at zero, and has exactly one zero, `-b` with `b=√(1-exp(-2))`. This zero is simple. Its reciprocal residue is `R=κ(b)(1-b²)/b>0`.

## Proof

On the left half-plane define the continuation by
`(1+(1/2)Log(1-z²))/κ(-z)`. The reflection identity identifies it with
the slit-plane factor wherever both are analytic. It extends across
`(-1,0)` since `1-z²>0` there.

The angular upper bound controls the factor near zero on the right.
On the left the reflected numerator is bounded and `|κ(-z)|≥1`.
The bounded singularity is removable; the positive-real unit limit fixes
its value as one.

A zero satisfies `Log(1-z²)=-2`, hence `z²=1-exp(-2)`.
The positive-real factor never vanishes, leaving exactly `-b`.
Differentiating the reflected quotient gives
`κ′(-b)=b/((1-b²)κ(b))=1/R`. Continuity of its divided difference
then gives `(z+b)/κ(z)→R`.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicFactorHasOneNegativeZero.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `analyticOnNhd_continuedLogReferenceFactor`
- `continuedLogReferenceFactor_zero`
- `continuedLogReferenceFactor_eq_zero_iff`
- `hasDerivAt_continuedLogReferenceFactor_neg_radius`
- `tendsto_logarithmicFactor_reciprocal_residue`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
Stieltjes inversion remains on the
[half-line kernel card](../1-in-progress/the-half-line-logarithmic-green-kernel.md).
