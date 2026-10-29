# Prime–polar cancellation on Gamma-bounded complete sources

- **ID:** acs-prime-polar-cancellation-in-gamma-norm
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Statement:** Transfer the actual prime–polar cancellation from derivative
  norms to Gamma-plus-mass norms, uniformly over original compact BV profiles.

## Target

For every ε>0, there is R₀≥0 such that every R≥R₀ and every real compact BV
profile f supported in [−R,R] satisfies

`|primeSource(f)−P(f)| ≤ ε exp(R) (Γ(f)+∫f²)`.

Both exponential pole moments and every actual von Mangoldt coefficient
must remain in the same source. The estimate must hold uniformly in f;
pointwise convergence for one fixed test is insufficient. The theorem gives
actual signed cancellation on complete logarithmic cells, whose derivative
norms are infinite. It does not close ACS: the remaining aperture factor
still grows, and no full-Weil sign or finite global index follows.

## Candidate mechanisms

1. Normalize the finite prime measure by exp(R), recenter at lag 2R, and
   compare with its exponential horizon density. The corpus proves the
   corresponding prime-comb translation/resolvent law and prime–polar
   derivative-norm cancellation.
2. Upgrade to operator norm from Gamma-plus-mass to L²: bounded-frequency
   cancellation plus the unbounded Gamma symbol controls high frequencies.
   An equivalent physical proof would use uniform Gamma-controlled smoothing
   before the existing derivative estimate.
3. Restore all source terms literally. Prime-comb Euler weights and the
   actual prime-power lags are different; an identification must pay those
   differences rather than silently replacing the source.

## Research status

The previous joint whole-square payment is checked. Adding absolute
first-prime weights does not estimate the required all-prime coupling.
The ordered Chebyshev/Gamma-square identity gives a signed discrepancy but
does not determine its sign. The arithmetic prime-comb corpus explicitly
distinguishes relative cancellation from a bounded critical remainder.

The initial search established the ingredients below. No web search,
novelty checks, numerical computations or axiom checks.

## Paper proof

Write C_f(s)=∫f(x)f(x+s)dx and M_f=∫f². For S>1 put
χ_S(s)=smoothTransition(S−s), and define the literal cutoff multiplier

`B_S(t)=2[Σ_{n≤ceil(exp S)} Λ(n)n^(−1/2)χ_S(log n)cos(t log n)
           −∫₀^S (exp(s/2)+exp(−s/2))χ_S(s)cos(ts)ds]`.

If f is supported in [−R,R] and S≥2R+1, C_f vanishes outside
[−2R,2R] and χ_S=1 wherever its positive-lag values can be nonzero.
Fourier inversion and finite-sum/Fubini interchange therefore identify
`primeSource(f)−P(f)=∫ B_S(2πξ)|f̂(ξ)|²dξ`, with every original prime
power retained. The polar equality follows by expanding both exponential
moments: `P(f)=4∫₀∞cosh(s/2)C_f(s)ds`. These integrals are absolutely
convergent on the compact lag interval.

Let D bound |smoothTransition′|. Lag Abel summation gives B_S/2 as
`∫₀^S E(s) d/ds[exp(−s/2)χ_S(s)cos(ts)]ds`, where
E(s)=exp(s)+s−1−ψ(exp(s)). The corpus proves universal c>0,K≥0,S₀>0
such that `|E(s)|exp(−s/2)≤K exp(S/2)exp(−c√S)` for 0≤s≤S and
S≥S₀. Consequently

`|B_S(t)|≤2KS exp(S/2)exp(−c√S)(1/2+D+|t|)`.

The positive polar mass is at most 4exp(S/2). At t=0 the preceding
bound therefore bounds the positive prime mass as well. Since
S exp(−c√S)→0, there is a universal C with
`|B_S(t)|≤C exp(S/2)` for all t and all sufficiently large S.

The actual Gamma increment γ is nonnegative and satisfies
γ(t)≥(log|t|)/2 outside a fixed compact interval. Given η>0, choose T
so that C≤ηγ(t) for |t|≥T. On |t|≤T, the first bound is at most
ηexp(S/2) for all sufficiently large S, uniformly in t. Hence

`|B_S(t)|≤ηexp(S/2)(1+γ(t))` for every t.

Integrating against |f̂|², Plancherel and the exact Gamma jump identity
give `|primeSource(f)−P(f)|≤ηexp(S/2)(M_f+Γ(f))` for every smooth
compact profile of the stated support. Take S=2R+2. Pole-preserving
mollification of a compact BV profile is supported in [−R−1/2,R+1/2],
preserves both exponential moments, and converges in square mass,
Gamma energy and every correlation value. The common support leaves
only finitely many prime-power terms, so the entire prime source also
converges. Passing to the limit and taking η=ε/exp(1) proves the target.

No source-sign conclusion follows: exp(R) remains in the bound.

## Formalization status

The exact paper statement is formalized. Main declarations:

- `ArithmeticCompensationTheory.ThePrimePolarCutoffHasUniformFrequencyBounds`:
  `exists_primePolarCutoffSymbol_low_frequency_bound`,
  `eventually_primePolarCutoffSymbol_small_on_frequency_interval`,
  `eventually_primePolarCutoffSymbol_bounded_all_frequencies`.
- `ArithmeticIndexDescent.ThePrimePolarCutoffIsSmallInGammaNorm`:
  `eventually_primePolarCutoffSymbol_gamma_small`.
- `ArithmeticIndexDescent.ThePrimePolarCutoffRepresentsTheFullSource`:
  `integral_primePolarCutoffSymbol_density`,
  `primeSum_eq_primePolarCutoff_core`,
  `primeSum_sub_poles_eq_primePolarCutoff_integral`.
- `ArithmeticIndexDescent.TheFullPrimePolarSourceCancelsInGammaNorm`:
  `eventually_primePolar_gamma_bound_core`,
  `exists_primePolar_gamma_bound_bv`.

All four direct checks passed, run individually from `formal/`:

```text
lake --old env lean GaloisForLFunctions/ArithmeticCompensationTheory/ThePrimePolarCutoffHasUniformFrequencyBounds.lean
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/ThePrimePolarCutoffIsSmallInGammaNorm.lean
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/ThePrimePolarCutoffRepresentsTheFullSource.lean
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheFullPrimePolarSourceCancelsInGammaNorm.lean
```

The three prerequisite oleans were previously absent and were built only
for these new imports; their builds passed without diagnostics. Both
programme umbrellas import the finished modules and were not compiled.
No axiom checks were run.

## Frontier advance and remaining gap

The original complete-cell source now admits uniform relative cancellation
in its finite Gamma-plus-mass norm. No derivative norm, parity restriction,
discarded prime power or modified pole appears. This removes a norm-transfer
obstacle; it does not pay the first-prime coupling uniformly in aperture.
The remaining exp(R) factor leaves full-source sign and global index open.
