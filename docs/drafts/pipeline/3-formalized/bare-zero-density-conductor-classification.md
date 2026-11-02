# Conductor classification at bare zero prime density

- **ID:** bare-zero-density-conductor-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ12, solved at the zero-density endpoint.
- **Notation:** `A_P(N)=Σ_(p∈P,p≤N)log p/p`, `δ_Q=Π_(p∈P,p<Q)(p−1)/(p+1)`, `S_P(N)=Σ_(n≤N)ω_P(n)/n`, `H_N=Σ_(n≤N)1/n`.
- **Statement:** If `A_P(N)=o(log N)`, then `HodgeSeparates(ω_P)` iff some `0<s<2log 2` satisfies `Σ_(m≥2)w_P(m)/(E_m−γ−s)>1/s`. Otherwise `ω_P` has the maximal hyperplane gap `2log 2`.

No density-error rate or positive limiting Euler harmonic density is required.
The former corpus criterion required positive limiting Euler mass, or positive
relative prime density with a power error.

## Harmonic comparison and Euler removal

Positive renewal for `g=1*ω_P` gives regular variation of
`G(u)=Σ_(n≤e^u)g(n)/n` with index two. Signed recovery gives
`uS_P(⌊e^u⌋)∼2G(u)` and `S_P(N)/(log N)^α→∞` for every `α<1`.
Uniform positive power comparison transfers to
`S_P(m)≤6(log m/log N)^(1−ε)S_P(N)` for all sufficiently large `m≤N`.
See [positive renewal and signed recovery](zero-density-positive-renewal-tauberian.md).

Positive Laplace comparison, the exact finite-prime removal identity, and
the tilted Euler-head estimate give, uniformly for large `Y` and `3≤Q≤Y`,
`|S_(P,Q)(Y)|≤C[S_P(Y)/(log Q·δ_Q)+1]`.
See [uniform rough means](zero-density-uniform-rough-means.md).

The density limit gives `A_P(N)≤κlog N+C_κ` for every `κ>0`.
The existing subquarter conductor estimate at `κ=1/8` proves convergence
throughout `0≤s<2log 2`. Its weighted prime estimate, applied with
`σ=1/log Q`, gives
`Σ_(p∈P,p≤Q)1/p≤ηloglog Q+K_η` for every `η>0`, since `p^(−σ)≥e^(−1)`.
The elementary finite Euler-factor bound
`δ_Q⁻²≤exp(8Σ_(p∈P,p≤Q)1/p)` therefore yields
`δ_Q⁻²≤C_ε(log Q)^ε` for every `ε>0`.

## Relative spectral tail

Set `Z_N=S_P(N)/√log N`. Square-root comparison between earlier horizons,
the rough-mean bound, and rough harmonic coercivity give
`‖P_Q ω⃗_P‖²≤C Z_N²δ_Q⁻²+Dlog Q` for `3≤Q≤N`.
In the smooth-fibre sum, apply `sq_div_le_of_rough_bound` at `β=1/2`;
the rough harmonic denominator cancels the smooth reciprocal-mass cost `O(log Q)`.
Finite initial horizons and `Y<Q` contribute only a constant.

Use `δ_Q⁻²≲√log Q` and eventual `S_P(N)≥(log N)^(3/4)`.
Then `log Q≤Z_N²√log Q`, so
`‖P_Q ω⃗_P‖²≤K Z_N²√log Q` uniformly for `3≤Q≤N`.
Rough Poincaré at the preceding squared cutoff costs one logarithm.
Cauchy–Schwarz and geometric summation along `Q_j=T^(2^j)` give

`|⟨u,ω⃗_P−P_Tω⃗_P⟩|≤[K₁ Z_N(log T)^(−1/4)+K₂]√poleDefect(u)`.

The final scale costs only `O(√poleDefect(u))`, because its logarithm is at
least half `log N`. Thus the normalized tail tends to zero by choosing `T`
large, then `N` large.

## Fixed-scale identification and classification

For every real completely multiplicative contraction, finite prime peeling gives
`S_T(N)=Π_(p<T)(1−ω(p)/p)S(N)+O_T(1)`.
With `c_N=S_P(N)/H_N`, the fixed-scale fibre error is `O_T(1+log a)`;
its total squared defect is uniformly bounded because
`Σ_(a T-smooth)(1+log a)²/a<∞`.
This holds for every prime pattern. At zero density it is
`o(S_P(N)²/H_N)` by signed growth.
See [bounded fixed-scale defects](fixed-scale-prime-flip-defects-are-bounded.md).

Divide the raw-vector approximation by `√H_N`. Relative to `c_N`, its error
in excited energy norm is
`O((log T)^(−1/4)√(H_N/log N))+O_T(√H_N/S_P(N))`.
Since `H_N/log N→1` and `S_P(N)/√H_N→∞`, finite flips approximate the
infinite flip with arbitrarily small relative error. Finite-flip resolvent
bounds transfer to the actual harmonic normalization.

If every conductor sum is at most `1/t`, compare at `0<s<t<2log 2`.
The strict margin `s/t<1`, excited upper bound, and pole-ground comparison
give the full hyperplane gap `2log 2`.
Conversely, a convergent conductor sum exceeding `1/s` contains a finite
separating packet; `hodgeSeparates_primeSetFlip_of_packet` applies to every
prime pattern. These implications prove the exact criterion.

## Lean

Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory`.

The four capstones in `TheZeroDensityEndpointHasTheConductorCriterion.lean` are:

- `exists_scale_zeroDensity_inner_sub_le`
- `eventually_zeroDensity_inner_sq_le_conductorSeries`
- `zeroDensity_primeSetFlip_hasHyperplaneGap_of_conductorSeries`
- `zeroDensity_hodgeSeparates_primeSetFlip_iff_conductorSeries`

Supporting modules:

- `TheSparseFlipHasUniformHarmonicRatios.lean`: uniform dilation and earlier-horizon bounds.
- `TheZeroDensityConductorSeriesConverges.lean`: conductor convergence and inverse-density subpower bound.
- `TheSparseFlipHasRelativeProjectedMass.lean`: uniform earlier rough envelope and relative projection estimates.
- `TheZeroDensitySpectralTailIsRelative.lean`: relative dyadic spectral tail.
- `TheFixedScaleDefectIsBounded.lean`: bounded defect for every prime pattern.

All passed direct Lean checks. Every capstone's transitive axiom audit contains
only `propext`, `Classical.choice`, and `Quot.sound`.
