# The prime-valuation product sector (2026-08-07)

Module `HTGeometry/PrimeValuationSector.lean`, `lake build` green (2995 jobs), axioms
`[propext, Classical.choice, Quot.sound]`, in the HTGeometry umbrella.

## The blocker was wrong — check mathlib first

Two earlier passes recorded "needs an infinite product measure over the primes, which the corpus does
not have" and stopped. **Mathlib has it**: `MeasureTheory.Measure.infinitePi`
(`Mathlib/Probability/ProductMeasure.lean`) builds the product of a family of probability measures
over an ARBITRARY index type, with `infinitePi_pi : infinitePi μ (Set.pi ↑s t) = ∏ i ∈ s, μ i (t i)`.
With `ProbabilityTheory.geometricMeasure` the sector is a short file.

## What is built

- `primeValuationLaw p = geometricMeasure (1 - 1/p)`, matching `μ_p(k) = (1-1/p) p^{-k}` because
  mathlib's `geometricPMFReal q k = (1-q)^k * q`.
- `primeValuationMeasure = Measure.infinitePi primeValuationLaw` on `∏_p ℕ`.
- `primeValuationMeasure_cylinder : μ₀(A_P) = ENNReal.ofReal (sieveDensity P)` — the product-sector
  cylinder mass IS the corpus's `sieveDensity` from `PrimeSieveDensityTelescope`.
- `primeValuationLaw_compl_zero : μ_p({0}ᶜ) = 1/p` — the second factor of the restarted Euler sieve
  weight `w_{N,n} = D_{N,n}/p_{N+n}`. So the sieve weights are event probabilities of this sector:
  "the first `n` tail primes have valuation zero and the next one divides".
- `iInter_primeValuationCylinder` — along a full enumeration the cylinders shrink exactly to the
  all-zero valuation point.
- `primeValuationMeasure_zeroValuation` — the sector is atomless there (squeeze by
  `tendsto_sieveDensity_sievePrefix`; no new arithmetic).
- `ae_exists_valuation_ne_zero` — **almost surely some prime divides**. This is the probabilistic
  content of the sieve's unit total variation.
- Instantiating `mem:conditioning_total_variation_core_2026_08_07`:
  `abs_toReal_cond_primeValuation_le` (ratio `1 - a_Q/a_P`),
  `abs_toReal_cond_primeValuation_insert_le` (exactly `1/p`, via `sieveDensity_insert`),
  `toReal_restrict_primeValuation_le` (difference `a_P - a_Q`),
  `cond_primeValuation_zeroValuation`, `abs_toReal_cond_sub_dirac_zeroValuation` (maximal distance
  one to the atomic weak limit at every finite stage).

Card `prime-valuation-conditioning-normalization-amplification-no-go` advanced 2 → 3 and moved.

## Not reachable yet

The PARENT card `prime-valuation-kakutani-polar-third-completion` still has "full
product-measure/Kakutani formalization" open. **Mathlib has no Kakutani dichotomy and no Hellinger
machinery** (only Riesz–Markov–Kakutani, unrelated). That gate needs either a general Kakutani proof
or a bespoke SLLN argument for non-identically-distributed independent variables; mathlib's
`strong_law_ae` is iid only. The card is flagged `[NOT RH]` and `[NOT NEW AS RH MECHANISM]`, so the
value there is infrastructure, not RH.

## Lean notes

- `Measure.infinitePi_pi` will not fire under `rw` after def-unfolding; supply `(μ := …) (s := …)
  (t := …)` in a `have` and rewrite with that.
- `unitInterval` membership is `⟨x, h0, h1⟩`, and the subtype drags in `Real.instInv`, so the
  parameter definition must be `noncomputable`.
- `ENNReal.ofReal x ≠ 0` via `rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]`.
- `ENNReal.toReal_eq_zero_iff_of_ne_top` does not exist; `ENNReal.toReal_eq_zero_iff` gives the
  disjunction `a = 0 ∨ a = ⊤`.
- Appending to a file with `cat >>` lands OUTSIDE the closing `end Namespace` — move the `end`.
