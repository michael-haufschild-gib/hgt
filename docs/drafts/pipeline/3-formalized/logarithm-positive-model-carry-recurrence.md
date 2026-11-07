# Ternary digits under dyadic dilation

- **ID:** SPL-positive-model-carries
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Exact carry recurrence and signed logarithmic deficits for
  the positive-generator model with
  odd primes and extra labels of norms three and four.

## Exact identity

Write `N` for its count, `D(n)=N(n)−n`, and `s₃(n)` for the ternary digit sum.
The factorization coordinates give

`N(n)+N(⌊n/2⌋)=Σ_{a≥0}⌊n/3^a⌋=(3n−s₃(n))/2`,

hence

`D(n)+D(⌊n/2⌋)=(n mod 2−s₃(n))/2`.

The proof adds the odd-integer counts at `y` and `y/2`, obtaining
`⌊y⌋−⌊y/4⌋`, then telescopes over powers of four. The remaining sum is
the base-three digit-sum identity.

## Quantitative question

The model has proven error `O((log x)²)`, whereas every nonclassical positive
integer-norm system has error `Ω(log x)` along an unbounded sequence.
Whether alternating ternary digit sums along the dyadic orbit improve the
upper bound, or force a larger lower bound, remains open. The recurrence
does not exclude a zeta zero.

## Signed consequence

At `n=3^k−1`, the ternary digits are all two and `n` is even. The recurrence
therefore gives `D(n)+D(n/2)=−k`. At least one of these two thresholds has
`D≤−k/2`. This is a signed lower excursion, stronger than merely locating
an absolute jump. The proof reduces to the finite floor telescope and the
base-three digit recursion. In particular, arbitrarily large `n` satisfy
`N(n)≤n−log n/(2 log 3)`.

## Lean proof

Module `SumProductArithmeticOfTheLogarithm/PositiveNearCountCarries.lean`,
namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount`:

- `count_add_half_eq_floor_sum`: the real-threshold finite telescope.
- `count_add_half_digit_sum`: `2(N(n)+N(⌊n/2⌋))+s₃(n)=3n`.
- `repdigit_discrepancy_sum`, `repdigit_deficit`: exact repdigit sum and
  its signed deficit alternative.
- `negative_log_excursions`: the quantified logarithmic lower excursion.

Direct source check and capstone dependency audit pass. Only `propext`,
`Classical.choice`, `Quot.sound` occur. No external novelty claim.
