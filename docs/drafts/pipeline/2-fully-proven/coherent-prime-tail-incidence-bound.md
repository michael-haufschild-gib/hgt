# Coherent prime-tail incidence bound

- **ID:** critical-rigidity-prime-incidence-tail-bound
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Lean:** `CriticalScaleArithmeticRigidity/PrimeIncidenceHarmonicWindows.lean` — pending check

## Statement

Let `S(n)=Σ_(P<p≤Q)log p/(p−1)·1_(p∤n)`, `B=Σ_(P<p≤Q)log p/p`, `A'=Σ_(P<p≤Q)log p/(p−1)`, and `H=Σ_(A<n≤A+K)1/n`. Then

`|Σ_(A<n≤A+K)(S(n)−B)/n|≤A'/(A+1)`,

`Σ_(A<n≤A+K)S(n)²/n ≥ H B²−2BA'/(A+1)`.

The loss depends on prime incidence mass, with no quadratic conductor factor. On `floor(N/P)<n≤N`, the literal coherent complementary tail dominates `S(n)≥0`, so the same lower bound applies to its full harmonic square.

## Proof

For every positive integer `d`, the prefix sum of `1_(d|n)−1/d` equals `−(X mod d)/d` at `X`. The difference of two such prefix sums lies in `[-1,1]`. Finite Abel summation therefore bounds its harmonic sum on `A<n≤A+K` by `1/(A+1)`.

For each prime, `log p/(p−1)·1_(p∤n)=log p/p−[log p/(p−1)](1_(p|n)−1/p)`. Summing the harmonic bounds with these nonnegative weights gives the first inequality. Expand `S²=B²+2B(S−B)+(S−B)²`; the final square is nonnegative and `B≥0`, proving the second inequality. Source positivity then transfers it to the actual complementary tail.

## Consequence to establish separately

For `Q=P²` and `N≥P`, harmonic mass is at least `log P−log 2`, while `B=log P+O(1)` and `A'=log P+O(1)`. The tail lower bound is cubic logarithmic; its boundary correction is only quadratic logarithmic. Combining the exact scalar-residual comparison should establish the matching relative residual scale without a polynomial lower bound on `N` in terms of `Q`. That specialization is not included in the present theorem.
