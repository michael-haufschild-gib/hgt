# Positive first-moment inverses of the first fold

- **ID:** F1-PI
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Remaining first-moment payment](../1-in-progress/f1-primitive-variance-joint-payment.md)
- **Statement:** Both polynomial and exact logarithmic reflection forms have explicit positive
  first-moment inverses. For the exact form, `0<q(u)≤u/A(u)` for `0<u<1`, with strict upper
  inequality on the active strip.

Write `b=log2`, `d=2b`, `l=d−1`, `w=b/√2`, and
`A₀(u)=137/60−c+u²/2+u⁴/4+u⁶/6+u⁸/8`, with `c` as in the source card.
For `u∈[l,1]`, put `v=d−u` and `δ(u)=A₀(u)A₀(v)−w²`.
The proved spectral bracket gives `δ(u)>0`. Define

`q(u)=(A₀(v)u−wv)/δ(u)` on `[l,1]`, and `q(u)=u/A₀(u)` off the strip.

## Proof

The numerator is uniformly positive. For `0≤x≤1`, the exact identity

`(11/20+V₄(x))(693/500−x)−(2451/5000)x−7451/60000`

`=(1−x)[7081/30000+(193/480)(1−x)+(491/6000)x²
          +(2509/12000)x²(1−x)+(149/6000)x⁴+(1351/12000)x⁴(1−x)
          +(421/6000)x⁶+(193/4000)x⁶(1−x)+x⁸/8]`,

where `V₄=x²/2+x⁴/4+x⁶/6+x⁸/8`,

has a nonnegative right side, vanishing exactly at `x=1`. Since `d≥693/500`,
`A₀(x)≥11/20+V₄(x)` and `w≤2451/5000`, it follows that
`A₀(v)u−wv≥7451/60000` on the strip.
Thus both components of the pair inverse are positive, although the inverse matrix
has negative off-diagonal entries.

Matrix multiplication gives `A₀(u)q(u)+wq(v)=u` on the strip; off it,
`A₀(u)q(u)=u`. Positivity of `q(v)` gives `q(u)≤u/A₀(u)`.

For the exact coefficient `A(u)=137/60−c−½log(1−u²)`, use the open strip `(l,1)`;
endpoints do not affect the form. Since `A≥A₀>0` on `(0,1)`, both adjugate numerators
and the determinant retain their positive lower bounds. The same explicit formula
therefore gives the exact inverse. Its equation and `wq(v)>0` give the strict upper
bound `q(u)<u/A(u)` on the strip.

This identifies the sign of the explicit first-moment solution. It does not pay the
joint first/third-moment charge: the mixed inverse pairing remains to be bounded.

## Lean

WTZ `TheFirstMomentHasAPositiveReflectionInverse` proves:

- `firstFold_first_moment_numerator_lower` and
  `firstFold_logarithmic_first_moment_numerator_lower`: numerator floor `7451/60000`.
- `firstFoldFirstMomentInverse_equation`, `firstFoldFirstMomentInverse_pos`,
  `firstFoldFirstMomentInverse_le_local`: polynomial inverse and bounds.
- `firstFoldLogarithmicFirstMomentInverse_equation`, `firstFoldLogarithmicFirstMomentInverse_pos`,
  `firstFoldLogarithmicFirstMomentInverse_lt_local`: exact logarithmic inverse and strict strip bound.

Individual Lean source audit passes. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
