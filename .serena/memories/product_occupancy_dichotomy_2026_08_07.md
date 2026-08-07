# The occupancy dichotomy: one law, three instances (2026-08-07)

`HTGeometry/ProductOccupancyDichotomy.lean` — for `μ : ι → Measure ℕ` (all probability measures) and
any enumeration `e : ℕ ≃ ι`, the Kolmogorov product `Measure.infinitePi μ` satisfies

`Π {k | (occupiedSet k).Infinite} = 1  ↔  (∑' i, μ i {0}ᶜ) = ∞`

with `occupiedSet k = {i | k i ≠ 0}`. Both directions: second Borel–Cantelli (needs
`iIndepSet_occupiedEvent`) and first Borel–Cantelli (needs nothing). Green, axiom-clean.

Key reusable pieces: `infinitePi_occupiedEvent` (occupancy mass is local — replaces hand-rolled
pushforward computations), `iIndepSet_occupiedEvent`, `limsup_occupiedEvent`,
`tsum_ofReal_ne_top_iff_summable` (the device for checking the hypothesis from a real family),
`measure_singleton_eq_zero_of_finite_occupiedSet`.

## Why it matters: the corpus had three shadows of it

1. `RHTower/EulerActivationSquarefreeProbability.criticalEulerProductMeasure_infinite_occupancy`
   (σ = 1, second BC, with a 20-line bespoke `iIndepSet` proof).
2. `RHTower/EulerActivationSubcriticalFiniteness.subcriticalEulerProductMeasure_finite_occupancy`
   (σ > 1, first BC).
3. The prime-valuation sector — where the statement was missing entirely.

## The two new instances

- `HTGeometry/PrimeValuationInfiniteSupport.lean`: local masses are `1/p`, so they diverge; a.e.
  configuration has infinitely many prime divisors; **`primeValuationMeasure_range_natValuationVector`
  — the integers are null in the sector** (finite-support vectors `n ↦ v_p(n)`). Also
  `primeValuationMeasure_singleton_of_finite_occupiedSet`, which strictly generalizes
  `primeValuationMeasure_zeroValuation` and proves it WITHOUT the sieve-density telescope.
- `RHTower/EulerActivationOccupancyPhaseTransition.lean`: the activation product at every `σ ≥ 0`,
  bridges to both existing products (`eulerActivationProductMeasure_one`, `_of_one_lt`), and
  `summable_diagonalActivationOccupancy_iff : Summable (q_p/(1+q_p)) ↔ 1 < σ`. Capstone
  `eulerActivationProductMeasure_finiteOccupancy_eq_one_iff` — **the Euler edge is the sharp
  occupancy phase boundary**, and it belongs to the divergent side (`_infiniteOccupancy_of_le_one`
  covers all of `0 ≤ σ ≤ 1`, new).

## Lean notes

- `iIndepSet.precomp` needs `(s := …) (g := …)` given explicitly: higher-order unification of `s ∘ g`
  against `fun n => f (e n)` picks the wrong assignment under dot notation.
- `MeasurableSet.measurableSet_limsup` (mathlib) covers limsup of sets; there is no need to unfold to
  `⋂ ⋃`. `Nat.frequently_atTop_iff_infinite` + `Set.infinite_image_iff` gives the limsup identity.
- `ENNReal.ofReal x = ((x.toNNReal : NNReal) : ENNReal)` holds by `rfl`; that plus
  `ENNReal.tsum_coe_ne_top_iff_summable` and `NNReal.summable_coe` is the whole
  divergence-transport toolkit.
- `push_neg` is deprecated on this toolchain (warning ⇒ gate failure): use `not_lt.mp`.

Card: `docs/drafts/pipeline/3-formalized/product-occupancy-dichotomy-euler-edge.md`.
See also `mem:prime_valuation_sector_independence_2026_08_07`.
