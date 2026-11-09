# Decisive prime samples with arbitrarily large gaps

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Obstacle:** B136. Necessity of power-saving gaps is false.

## Result

There exists a fixed set D of primes such that:

1. For every R,N∈ℕ there is r≥N, r>0, with D∩[r,Rr)=∅.
2. No exponent θ<1 satisfies `PowGaps θ D`.
3. For every tempered zero configuration Z without real zeros, a lower bound
   `2 Re lagStructure(Z,B,log p) ≥ −T` for all p∈D forces every zero onto Re s=½,
   where B is the cubic box spline. No attainment assumption is imposed.

The construction uses compactness and finite prime detectors. It supplies no trace bound for ζ.

## Proof

For each zero occurrence put t=1/Im ρ and σ=Re ρ. Temperedness implies summability
of t²: outside |Im ρ|<1, inverse-square weights are at most three times the tempered
weights; the remaining carrier is finite. Order occurrences by decreasing t², breaking
ties by an injection into ℕ. Each occurrence has finite rank n and `(n+1)t²≤Σt²`.
Fill unused ranks with t=0. Each active slot supplies its point and its horizontal
reflection; this reproduces twice the original configuration, with collisions counted
by their natural multiplicity.

For K∈ℕ impose `(n+1)tₙ²≤K`, every partial sum `Σ_{n<N}tₙ²≤K`, and one protected
coordinate n≤K with `|σₙ−½|,|tₙ|≥1/(K+1)`. These are closed subsets of a product of
compact rectangles. The coordinate bound gives local finiteness; the partial-sum
bound gives temperedness; the protected coordinate retains an off-line zero. The
families are nested and cover every encoded impure configuration.

At fixed lag, the two Fourier factors of an autocorrelation of a compact C² test
bound each zero contribution by `C t⁴`. The contribution extends continuously by zero
at t=0. On the K-th chart its series has summable uniform envelope
`C K²/(n+1)²`. Thus the actual lag trace is continuous, and the encoded trace equals
twice the original trace.

Every tail of the primes detects an impure configuration below any threshold −T:
otherwise a finite-prefix bound extends the tail bound to all primes, contradicting
`onLine_of_bddBelow_primes`. The corresponding open sets cover each compact chart,
so finitely many arbitrarily late primes detect its entire family below −K.

Choose the K-th finite block after `(K+2)r_K`, then choose `r_{K+1}` beyond that
block. Their union D omits `[r_K,(K+2)r_K)`. These gaps rule out every power bound
`O(x^θ)`, θ<1. If an impure configuration had lower bound −T on D, its encoding
would lie in every sufficiently late chart. A block with K>2T would detect its
doubled trace below −K, contradicting the original bound.

## Lean

- `ZeroConfigurationGeometry/TheCompactCoordinatesOfTemperedConfigurations.lean`:
  `tempered_config`, `isCompact_family`, `exists_family_encoding`,
  `tsum_encoding_eq_double`.
- `ZeroConfigurationGeometry/TheSplineTracesOnCompactConfigurationFamilies.lean`:
  `continuous_traceSum_family`, `traceSum_eq_lagStructure`, `traceSum_encoding`.
- `SurfaceOfSpecZ/DecisivePrimeSamplesCanHaveArbitrarilyLargeGaps.lean`:
  `exists_finite_prime_block`, `onLine_of_bddBelow_decisiveSample`,
  `decisiveSample_has_large_gaps`, `not_powGaps_decisiveSample`,
  `exists_decisive_prime_sample_without_power_saving_gaps`.

Source checks: `lake --old env lean` on all three leaves. Capstone axiom audits:
`propext`, `Classical.choice`, `Quot.sound`. Leaves imported through the existing
ZeroConfigurationGeometry and SurfaceOfSpecZ umbrellas into MainTheorems.
