# The κ=1 Chebyshev parameters: height and width

Card: `docs/drafts/pipeline/1-in-progress/chebyshev-exponent-one-half.md`.

## Height (`RHTower/Sieve/ChebyshevHeightOne.lean`)

    chebHeightOne x = exp( 2 √(log x) )

Because the height is a **real** exponential (not a natural-number ceiling as in the Möbius
chain's `contourParamTwo`), both balance conditions are **exact identities**:

- `saving_exponent_one` : `(1/40000)/log T · log x = √(log x)/80000`
- `right_exponent_one`  : `(1/log T) · log x = √(log x)/2`
- `exp_right_le_chebHeightOne` : `exp((1/log T)·log x) = exp(-(3/2)√(log x)) · T`

and hence (`RHTower/Sieve/ChebyshevRatePowersOne.lean`), also exactly:

- `rpow_chebLeftTwo_at`  : `x^{c(T)} = x · exp(-√(log x)/80000)`
- `rpow_chebRightTwo_at` : `x^{d(T)} = x · exp(-(3/2)√(log x)) · T`

**The factor 2 in the height is essential** — at `log T = √(log x)` the truncation term's growth
`x^{1/log T} = exp(√(log x))` exactly cancels `1/T` and nothing is saved.  This is the third
appearance of the phenomenon; it is a property of the balance, not of a particular chain.

## Width (`RHTower/Sieve/ChebyshevWidthOne.lean`)

    chebRatioOne N = exp( √(log N) / 240000 ),   chebWidthOne N = N / chebRatioOne N

Forced from both sides: the contour coefficient carries `(N/H)²`, so `α` must exceed `2·80000`;
the smooth-vs-sharp comparison costs `(H+1)·log(N+H)`, so `α` must not be too large.
`α = 240000` leaves `exp(-√(log N)/240000)` on both sides.

## Reusable

    sq_le_exp_div_gen : 0 ≤ t → 0 < k → t² ≤ 4k²·exp(t/k)

the general "absorb a polynomial into an exponential" step, from `Real.add_one_le_exp` squared.
The Möbius chain's `sq_le_exp_div` is the case `k = 108` (`4·108² = 46656`).

## Traps

- `Real.sqrt` is nonneg unconditionally, so hypotheses like `0 ≤ Real.log N` are silently unused in
  `one_le_chebRatioOne`-style lemmas and the **lint gate fails on the unused-variable warning**.
  Drop the hypothesis rather than naming it `_`.
- `le_div_iff₀` does not apply to a goal `t ≤ 2*k*E` (the RHS is a product, not a quotient); use
  `mul_le_mul_of_nonneg_left` plus a `field_simp` equation.
