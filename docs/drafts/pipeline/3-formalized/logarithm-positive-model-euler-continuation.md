# The positive near-count model preserves the right-half-plane zero divisor

- **ID:** SPL-positive-model-Euler
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual Dirichlet series of the odd-prime system with extra
  norms three and four continues as `ζ(s)/((1+2^(−s))(1−3^(−s)))`.

## Theorem

For `Re s>1`, the displayed quotient equals `BeurlingSystem.zetaSeriesC`.
It is analytic on `Re s>0`, away from one; at one its residue is one.
Throughout that punctured half-plane its zeros and their multiplicities
are exactly those of `ζ`.

## Proof

The existing Riesz bound gives `xN(x)≤R(2x)≤2x²`, hence `N(x)≤2x`
for `x≥1`. The actual generalized-integer series therefore converges
absolutely for `Re s>1`.

Unique coordinates `(u,a,b)`, with `u` positive odd and norm `u3^a4^b`,
turn that series into the odd-integer series times the two geometric sums.
Splitting ordinary positive integers by parity identifies the odd series
as `(1−2^(−s))ζ(s)`. Cancelling
`1−4^(−s)=(1−2^(−s))(1+2^(−s))` proves the quotient formula.

For `q>1` and `Re s>0`, `|q^(−s)|<1`. Both remaining denominator factors
are therefore nonzero and analytic. Their reciprocal preserves analytic
orders. At one the denominator equals `(3/2)(2/3)=1`, so the usual zeta
residue transfers unchanged.

## Formalization

Module `SumProductArithmeticOfTheLogarithm/PositiveNearCountEuler.lean`,
namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount`:

- `hasLinearCounting`
- `zetaSeriesC_eq_continuation`
- `analyticAt_zetaContinuation`
- `zetaContinuation_zero_iff`
- `analyticOrderAt_zetaContinuation`
- `zetaContinuation_residue_one`

Direct source check and transitive axiom audit: PASS; only `propext`,
`Classical.choice`, and `Quot.sound`.

## Consequence and boundary

This genuine positive-generator model changes the count by logarithmic scales
while preserving the full right-half-plane zero divisor. Its count deformation
therefore cannot witness the minimum distance required to insert an exceptional
zero. The actual-series identification is essential: a formally defined quotient
without that identification would not establish a model theorem.
