# Positive renewal at zero logarithmic prime density

- **ID:** zero-density-positive-renewal-tauberian
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Γ12, zero-Euler-mass endpoint.
- **Statement:** If `A_P(N)=Σ_(p∈P,p≤N)log p/p=o(log N)`, then `L(u)=Σ_(n≤e^u)ω_P(n)/n` tends to `+∞` and `L(cu)/L(u)→c` for every `c>0`. For every `α<1`, `L(u)/u^α→+∞`.

## Positive count and kernel

Put `g=1*ω_P`, `G(u)=Σ_(n≤e^u)g(n)/n`,
`M(u)=∫_0^u L(v)dv`, and `J(u)=∫_0^u G(v)dv`.
Prime-power factors of `g` are either `k+1` or an alternating sum in
`{0,1}`, so `g≥0`, `G` is nondecreasing, and `J(u)≥u` for `u>0`.
The divisor swap and rounding error give

`|NΣ_(n≤N)ω_P(n)/n−Σ_(n≤N)g(n)|≤N`, hence `L≥−1`.

The logarithmic derivative of `g` is `K(n)=(1+ω_P(n))Λ(n)≥0`:
`g(n)log n=Σ_(d|n)K(d)g(n/d)`. Its cumulative harmonic mass satisfies

`B(e^u)=Σ_(n≤e^u)K(n)/n=2u−2A_P(e^u)+O(1)=2u+o(u)`.

The error is bounded because the total harmonic mass of non-prime
prime powers is bounded; the full-prime term is Mertens' first theorem.

## Regular variation of the positive mean

The exact logarithmic identity and a finite divisor swap give

`uG(u)−J(u)=Σ_(m≤e^u)(g(m)/m)B(e^u/m)`.

For every `ε>0`, choose `C_ε≥0` with
`|B(e^v)−2v|≤εv+C_ε` for all `v≥0`. Positive weights imply

`|uG(u)−3J(u)|≤εJ(u)+C_εG(u)`.

Consequently, for large `u`,

`(3−ε)/(u+C_ε)≤G(u)/J(u)≤(3+ε)/(u−C_ε)`.

The continuous function `J` has right derivative `G` everywhere.
The right-derivative comparison theorem, applied to `log J` and
multiples of `log(u±C_ε)`, gives `J(cu)/J(u)→c³` as `ε↓0`.
Also `uG(u)/J(u)→3`,
so `G(cu)/G(u)→c²`. Taking one `ε<1` in the lower bound gives
`G(u)≫u^(2−ε)`, in particular `G(u)/u→∞`.

## Recovering the signed mean

The harmonic-number bound `0≤H_⌊x⌋−log x≤1` for `x≥1` gives
`G(u)=M(u)+O(u+1)`, hence `M(u)∼G(u)`.

The signed logarithmic identity, Mertens summation, and the bounded
prime-power remainder give

`uL(u)=2M(u)−2E(u)+O(u+1)`,
`E(u)=Σ_(p∈P,p≤e^u)(log p/p)L(u−log p)`.

For the full-prime convolution, swapping finite sums gives weights
`ω_P(m)/m` against `Σ_(p≤e^u/m)log p/p`. Its difference from
`u−log m` is bounded by Mertens' theorem, so the total error is
`O(H_⌊e^u⌋)=O(u+1)`. The non-prime prime-power contribution obeys
the same bound. Since `L≥−1`,
`E(u)≥−A_P(e^u)`, whence `L(u)≤2G(u)/u+O(1)`.

The derivative limit gives `uJ'(u)/J(u)≥5/2` for large `u`.
Right-derivative comparison yields `J(u)/J(v)≥(u/v)^(5/2)` for
large `v≤u`. Since `uG(u)/J(u)→3`, this implies
`G(v)/v≤2G(u)/u` uniformly on that range.
The remaining bounded interval has bounded `L`, and `G(u)/u→∞`.
Thus `sup_(0≤v≤u)L(v)≤C'G(u)/u` for large `u`. Together with
`L≥−1` and `A_P(e^u)=o(u)`, this yields `E(u)=o(G(u))`.
The signed equation now gives `uL(u)∼2G(u)`, proving eventual
positivity and regular variation of index one. The lower bound
`G(u)≫u^(2−ε)` for each `ε>0` gives `L(u)/u^α→+∞` for every
`0≤α<1` by choosing `ε<1−α`.

## Lean

`RenormalizedIntersectionTheory/TheSparseFlipHasAnEventuallyPositiveHarmonicMean.lean`:

- `tendsto_signedMean_mul_log_div_positiveDivisorMean`
- `tendsto_sparse_signedMean_div_log_rpow_atTop`
- `tendsto_sparse_signedMean_atTop`

`RenormalizedIntersectionTheory/TheSparseFlipHarmonicMeanVariesRegularly.lean`:

- `tendsto_real_signedMean_mul_div_positiveDivisorMean`
- `tendsto_real_sparse_signedMean_div_rpow_atTop`
- `tendsto_sparse_signedMean_scale_ratio`

`RenormalizedIntersectionTheory/TheSparseFlipHasUniformHarmonicRatios.lean`:

- `exists_sparse_signedMean_uniform_power_comparison`
- `exists_sparse_signedMean_uniform_earlier_bound`

For every `ε>0`, signed recovery and positive power comparison give
`c^(1−ε)L(u)/6≤L(cu)≤6c^(1+ε)L(u)` simultaneously for all `c≥1`
and sufficiently large `u`. In particular, uniformly for large `m≤N`,
`S_P(m)≤6(log m/log N)^(1−ε)S_P(N)`.

Plain kernel checks passed. All capstone axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
The supporting renewal and positive-growth declarations are recorded in
`zero-density-positive-renewal-estimate.md` and `signed-positive-renewal-comparison.md`.

The relative spectral tail and endpoint conductor criterion are formalized in
[Bare zero-density conductor classification](bare-zero-density-conductor-classification.md).
