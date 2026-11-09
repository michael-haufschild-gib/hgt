# Weighted heavy-return measure at the separation horizon

- **ID:** CDG-ENTROPY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Control weighted heavy-return measure by the weight ratio
  `S/A`, with an explicit observation horizon and no union over prime subsets.

## Theorem

For distinct primes, nonnegative weights `a_j≤A`, `A>0`, total mass `S`,
and `N≥16`, let `H=N−1` and let `δ` be the weighted coordinate separation
floor. In any interval of length `T≥0`,

`vol{at least 7S/8 returns at precision 1/(2N)}`
`≤ (5π/2) max(T/2,δ⁻¹) exp(−S/(8A))`.

Precision is chord distance; the same estimate holds in radian distance.
Targets may have arbitrary coordinate phases. The arithmetic floor is
`hereditaryDepthFloor k (ceil(Σ log p_j)+1) H`.

## Proof

Weighted separation selects coordinates of mass `S_J≥S/2` with no nonzero
height-`H` form below `δ`. A return missing at most `S/8` of the original
mass misses at most `S_J/4` of the selected mass.

Let `K_N` be the normalized squared geometric sum, with constant Fourier
coefficient `1/N` and value at least `1/4` at precision `1/(2N)`. Set
`τ=1/A`, `u_j=4(exp(τa_j)−1)`, and use the nonnegative detector

`F(t)=∏_{j∈J}(1+u_j K_N(t log p_j−θ_j))`.

On the heavy-return set, `F≥exp(3τS_J/4)`. Expanding the product into
squared smooth-box sums and applying the Fejér window removes every
off-diagonal frequency at the separation horizon. The remaining factor is
`∏(1+u_j/N)≤exp(8τS_J/N)≤exp(τS_J/2)`, giving the entropy loss.

For every subset `K⊆J`, exponent differences of its smooth box extend by
zero to height-`H` integer vectors supported on `J`. Separation implies
that two frequencies within `δ` have identical exponent vectors. The
close-pair count is exactly `N^|K|`. The existing Fejér inequality bounds
the integral of `∏_(j∈K) K_N` by
`(5π/2) max(T/2,δ⁻¹) N^(−|K|)`, also when `K` is empty.
The finite product expansion, nonnegative `u_j`, and linearity of the
integral give the asserted bound on `∫F`.

For `0≤x≤1`, convexity gives `exp(x)−1≤(e−1)x≤2x`, hence
`u_j≤8τa_j`. Also `1+x≤exp(x)`. These prove the displayed product bound.
On a returning coordinate, `1+u_j K_N≥exp(τa_j)`; every other factor is
at least one. Missing selected weight is at most `S/8≤S_J/4`, proving
the lower bound on `F`. Markov's integral inequality gives
`exp(−τS_J/4)≤exp(−S/(8A))`. The radian assertion follows from
`|exp(ix)−1|≤|x−2πm|`.

## Calibration and boundary

At fixed `N`, elementary separation of smooth rational numbers is stronger
than the collective floor in growing dimension. Moreover, Matveev's scalar
bound already has linear dimension degree, keeps all coordinates and gives
a stronger floor than the weighted collective theorem. The proposed detector
with that theorem therefore has no established improvement over scalar
separation, even when `H` grows. The estimate alone does not meet the
programme's research-frontier criterion.

The remaining research question is whether the product detector can exploit
the distribution of small smooth ratios before the worst-separation horizon.
Keep both elementary and scalar transcendence baselines in any such comparison.

The local [unrestricted smooth-head moments](../3-formalized/unrestricted-smooth-head-arithmetic-moments.md)
already retain the primitive cost
`Σ|r_m r_n| Z(2Z+m/gcd(m,n)+n/gcd(m,n))`.
[Normalized tail moments](../3-formalized/primitive-head-normalized-tail-moments.md)
divide by actual head mass at the reduced-support horizon
`T≥52 max(1,max m/gcd(m,n))`. A new estimate must improve this arithmetic
cost or its admissible range, not merely reapply the Fourier majorant.

This is a finite-time measure estimate. It does not by itself exclude a first
return before the observation horizon or provide the prime-degree trace bound.

## Open extension

An estimate before the worst-separation horizon, with a proved gain over
existing smooth-head/resonator bounds, remains open. No such improvement is
included in this theorem.

## Formalization

`CollectiveDiophantineGeometry/WeightedReturnCounts.lean` proves:

- `integral_returnKernel_product_le`: exact diagonal cost for every subproduct.
- `integral_weightedReturnDetector_le`: product of constant coefficients.
- `measure_weightedChordReturnWindow_le`: actual weighted prime-return measure.
- `measure_weightedRadianReturnWindow_le`: the same bound with integer windings.

Direct `lake --old env lean` source verification passed. All four transitive
axiom audits contain only `propext`, `Classical.choice` and `Quot.sound`.
The programme umbrella imports the module.
