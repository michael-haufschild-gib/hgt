# Real multiplicative contractions have positive divisor counts

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** If `ω(1)=1`, `ω(mn)=ω(m)ω(n)` for positive integers, and `|ω(n)|≤1`, then `g(n)=Σ_(d|n)ω(d)≥0` and `Σ_(n≤N)ω(n)/n≥−1` for every `N`.
- **Use:** Removing small primes introduces zeros into a sign gauge. The lower bound survives this removal.
- **Quantitative consequence:** Writing `S_N=Σω(n)/n`, `G_N=Σg(n)/n`, one has
  `S_N log N≤2G_N+(16+3log 4)(1+log N)` for `N≥1`.
  Every rough prime flip therefore satisfies `|S_N|≤2G_N/log N+32+6log 4` for `N≥3`, uniformly in its cutoff.

## Proof

At a prime power, `g(p^k)=Σ_(j≤k)ω(p)^j`. For nonnegative
`ω(p)` every summand is nonnegative. For `−1≤ω(p)<0`, the geometric
identity gives `(1−ω(p))g(p^k)=1−ω(p)^(k+1)≥0`.
Multiplicativity gives the result at every integer.

The exact count is `Σ_(n≤N)g(n)=Σ_(d≤N)ω(d)⌊N/d⌋`.
The total rounding error is at most `N`, since `|ω(d)|≤1`.
Nonnegative counts therefore give `NΣ_(n≤N)ω(n)/n≥−N`.

Since `S_Y≥−1` and `−1≤ω(d)≤1`, one has `ω(d)S_Y≤S_Y+2`.
Apply this to the full von Mangoldt convolution. Mertens' first estimate
bounds the untwisted convolution by the logarithmic primitive with error
`(log 4+4)H_N`; the divisor mean differs from that primitive by at most
`H_N`. The polar primitive differs by at most `2`.
Using `H_N≤1+log N` gives the quantitative comparison above.

## Lean

`ArithmeticCountingPositivity/RealMultiplicativeContractionsHavePositiveDivisorCounts.lean`:

- `contractionDivisorCount_nonneg`
- `abs_mul_harmonicSum_sub_divisorCount_le_of_abs_le_one`
- `neg_one_le_harmonicSum_of_real_multiplicative`

`RenormalizedIntersectionTheory/TheRoughFlipHasAPositiveDivisorMean.lean`:

- `harmonicSum_mul_log_le_two_divisorMean`
- `roughFlipDivisorCount_nonneg`
- `neg_one_le_roughFlipHarmonicSum`
- `roughFlipHarmonicSum_mul_log_le_two_divisorMean`
- `abs_roughFlipHarmonicSum_le_divisorMean`

Plain kernel checks passed. Capstone audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
