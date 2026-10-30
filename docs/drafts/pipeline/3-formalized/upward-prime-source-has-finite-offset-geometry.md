# Upward prime source has finite offset geometry

- **ID:** upward-prime-source-has-finite-offset-geometry
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statements

Fix `c>0` and put `B=⌈c exp c⌉`. The literal upward row at width `c/N`
equals its finite prime-power sum over `1≤k≤N+B` and offsets `1≤h≤B`.
Positive offsets retain `kn+h≤N`; negative offsets retain
`h<kn` and `kn−h≤N`. Exact ratios remain removed.

For a compact `C²` unit profile with autocorrelation `G`, there are `C,N₀`
such that, for `N≥N₀`, positive distinct integers `T,j` with `|j−T|≤B` satisfy

`|√(T/j) G((N/c)log(j/T)) − G(N(j−T)/(cT))| ≤ C/N`.

For a nonzero profile, the literal upward Ramanujan row has bounded square-root row size, uniformly
in `n,N` at fixed `c`. Reciprocal prime-power mass in any fixed-width interval
about `Y` tends to zero as `Y→∞`. These are supporting source estimates;
the complete upward norm identification is not asserted here.

## Proof [PROVED HERE]

Autocorrelation support gives `|log T−log j|≤c/N`. Since `j≤N`,
`|T−j|≤j(exp(c/N)−1)≤c exp c≤B`. Splitting `j<kn` and `kn<j`, then
reindexing by their positive integer differences, gives the offset identity.
Its cutoffs vanish when `k>N+B`, since `kn≥k`.

Let `A=c exp c+2c+1`. A nonzero logarithmic kernel and integer separation
give `N≤c exp c·min(T,j)`. A nonzero reciprocal kernel gives `N≤cT`;
when `N≥2cB`, the offset bound also gives `N≤2cj`. Thus either both kernels
vanish or `N≤AT,Aj`. For `N≥2AB`, put `z=(j−T)/T`; then `|z|≤AB/N≤1/2`.
Lipschitz continuity of `G`, `|log(1+z)−z|≤2z²`, and
`|√T/√j−1|≤|T−j|/j` give the displayed estimate with
`C=4 Lip(G) A²B²/c+AB∫φ²`.

For the actual row bound, use `|c_m(j)|≤ϕ(m)`, normalized autocorrelation
bounded by its support indicator, and the already proved directed upward
row estimate. Its cost is `2(log 4+4)e^(3c/(2N))(e^(c/N)−1)N·ϕ(m)`,
bounded by `2(log 4+4)c e^(5c/2)ϕ(m)`.

Finally `0≤Λ(k)/k≤log k/k→0`; a fixed-width interval has bounded cardinality
and its least index tends to infinity. If `|kn−N|≤B`, then
`k∈[⌊N/n⌋−B,⌊N/n⌋+B+1]`, so this tail applies to boundary prime indices.

## Lean

`CriticalArithmeticCorrelationTheory/TheUpwardPrimeRowsHaveUniformKernelBounds.lean`:

- `upwardRamanujanRow_eq_offsets` gives the exact source identity;
- `exists_logPrimeKernel_linearization_bound` gives the uniform kernel estimate;
- `abs_sqrt_mul_upwardRamanujanRow_le` bounds the literal directed source;
- `tendsto_primeIndexBoundaryMass` and `prime_product_boundary_mem` control the boundary;
- `sum_prime_product_strip_sq_le` retains the stronger divisor-square alternative.

Final direct no-olean audit passed without warnings. Five main declarations
have only `propext`, `Classical.choice`, and `Quot.sound`; CACT umbrella wired.
This is supporting work for the upward norm theorem, not a separate count.
