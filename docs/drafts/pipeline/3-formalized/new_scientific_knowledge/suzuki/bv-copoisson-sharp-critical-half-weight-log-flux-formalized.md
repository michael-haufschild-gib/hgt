# BV co-Poisson: sharp critical half-weight and the logarithmic flux

- **ID:** `bv-copoisson-sharp-critical-half-weight-log-flux`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./bv-copoisson-sharp-critical-half-weight-log-flux.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/BVCoPoissonSharpCriticalFluxCore.lean`
  - `formal/GaloisForLFunctions/RHTower/BVCoPoissonSharpCriticalFlux.lean`
  - `formal/GaloisForLFunctions/RHTower/BVCoPoissonLogBoundaryQuotient.lean`
  - `formal/GaloisForLFunctions/RHTower/BVCoPoissonHalfWeightResonance.lean`
  - `formal/GaloisForLFunctions/RHTower/BVCoPoissonCompactSeedRigidity.lean`

## Formal content

| Card | Lean |
|---|---|
| Theorem A, sharp harmonic error bounds | `sharpHarmonicError_bounds`, `sharpHarmonicError_pos`, `sharpHarmonicError_lt_odd_reciprocal`, `sharpOddError_pos`, `tendsto_nat_mul_sharpHarmonicError`, `tendsto_nat_mul_odd_reciprocal`, `tendsto_nat_mul_sharpOddError` |
| Theorem A, summable `O(m⁻²)` block energy | `sharpCriticalEnergy_error_bound`, `summable_sharpCriticalEnergy_error`, `tendsto_nat_mul_evenCriticalEnergy`, `tendsto_nat_mul_oddCriticalEnergy`, `tendsto_nat_mul_sharpCriticalEnergy` |
| Theorem B, ordinary `L²` survives | `integrableOn_sharpCoPoissonP_sq_Ioi_zero` |
| Theorem B, critical half-weight fails | `not_integrableOn_sharpCriticalDensity_Ioi_zero` |
| Theorem C, exact cell integrals | `sharpCoPoissonP_even_cell`, `sharpCoPoissonP_odd_cell`, `integral_even_cell_criticalEnergy`, `integral_odd_cell_criticalEnergy`, `integral_two_cell_criticalEnergy` |
| Theorem C, cutoff flux and its logarithmic rate | `integral_sharpCriticalFlux_cutoff_eq`, `tendsto_harmonic_div_log`, `tendsto_sharpCriticalPartialEnergy_div_log`, `tendsto_sharpCriticalPartialEnergy_div_log_cutoff`, `tendsto_integral_sharpCriticalFlux_cutoff_div_log` |
| Theorem C at arbitrary real `T` | `tendsto_sharpCriticalFlux_div_log`, `tendsto_sharpCriticalFluxFromZero_div_log` |
| Theorem E, multiplier-ideal density | `logIdealSpan_topologicalClosure_eq_top`, `logIdealSpan_dense` |
| Theorem F, parity resonance of the sharp eta lattices | `polynomial_eq_zero_of_cancels_criticalEta_even_poles`, `polynomial_eq_zero_of_cancels_criticalEta_odd_poles` |
| Theorem G, compact-seed rigidity | `ae_eq_zero_of_even_moments_of_positive_compact_support`, `ae_eq_zero_of_odd_moments_of_positive_compact_support` |

## What the card actually closes

The five alternatives for this provider family are exhaustive and each is now a theorem:

```text
ordinary Burnol L² completion       -> critical half-weight leaves the carrier
logarithmic boundary quotient       -> multiplier ideal is dense, quotient is zero
extended property-S, sharp eta      -> infinite parity-resonance obstruction
compact multiplicative correction   -> all-moments rigidity forces zero seed
noncompact Gamma-Gaussian repair    -> exists for arbitrary moderate data, hence nonselective
```

Theorem G's rigidity is proved in the generality the exhaustion needs — *arbitrary* finite measures
on a positive compact interval, with vanishing of all even **or** all odd moments forcing the
density to vanish almost everywhere — so no compact multiplicative correction can repair the
half-density resonance.  Theorem F is the sharp form: no nonzero polynomial cancels either infinite
pole family, so the obstruction is not a finite-rank accident.

The card is a **no-go with a positive survivor**, and the survivor is named: the exact Rademacher
logarithmic Gram and Stein defect of Theorem D.

## Hypotheses

Each theorem carries its own analytic data — measurability, integrability, compact support in the
positive ray, finiteness of the measure.  No hypothesis is a theorem proved elsewhere in the
corpus, and no theorem assumes RH, a zeta-zero hypothesis, a source sign, or a numerical
certificate.

No `sorry`, `axiom`, `opaque`, `unsafe`, or numerical computation occurs.  Every exported terminal
theorem audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

Theorem D's conormal is unbounded, and the card states explicitly that its remaining formalization
cannot change the terminal implication and is deliberately not represented by an abstract `ℓ²`
surrogate — a scope decision with a stated reason, not a gap in the closure.

What remains beyond this card is source-generated causal-dagger positivity on the completed
principal conormal; the card terminalizes this provider family rather than claiming RH.
