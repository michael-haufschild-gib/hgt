# Level structure of the prime-valuation sector (2026-08-07)

Follow-up to `mem:product_occupancy_dichotomy_2026_08_07`. The dichotomy is now stated for an
ARBITRARY local target family `t : ι → Set ℕ` (`localHitSet`, `localEvent`,
`measure_infiniteHit_eq_one_iff`, `measure_finiteHit_eq_one_iff`, `ae_infinite/finite_localHitSet`);
occupancy is the `t = fun _ => {0}ᶜ` instance and all its old names survive as one-line corollaries.
No measurability hypotheses on `t`: `MeasurableSet.of_discrete` covers all subsets of `ℕ`.

## New modules

- `HTGeometry/GeometricTailMass.lean` — `geometricMeasure_Ici hp m : geometricMeasure p {k | m ≤ k} =
  ofReal ((1-p)^m)`. **Mathlib gap.** Proof: one-step atom recursion
  `μ {k | m ≤ k} = μ {m} + μ {k | m+1 ≤ k}` + `WithTop.add_left_cancel ENNReal.ofReal_ne_top` — no
  tail series summed.
- `HTGeometry/PrimeValuationLevelStructure.lean`:
  - `primeValuationLaw_Ici p m = ofReal (p⁻¹ ^ m)` (level mass is `p^{-m}`).
  - `tsum_primeValuationLaw_Ici_ne_top (2 ≤ m)` — summable above level one (comparison with
    `∑ p^{-2}` via `Nat.Primes.summable_rpow`, `pow_le_pow_of_le_one`).
  - `ae_finite_level (2 ≤ m)`, `ae_finite_squarefull` — a.e. only finitely many primes of
    multiplicity ≥ m; **a random integer is squarefree away from a finite set.**
  - `ae_primeValuation_level_structure` — a.s. `{p | 2 ≤ v_p}` finite AND `{p | v_p = 1}` infinite.
    Complete description of the carrier: infinitely many prime divisors, almost all simple.

**Level one is the only divergent level.** That is why the squarefree kernel carries the asymptotics.

## Lean notes

- Corollary layers over a general `t` must pass `t` EXPLICITLY (`(fun _ => ({0}ᶜ : Set ℕ))`):
  higher-order unification cannot solve `occupiedSet k =?= localHitSet ?t k`. Defeq then closes it.
- `Set.Infinite.diff` is deprecated → `Set.Infinite.sdiff`. `Set.Infinite.mono` takes the subset
  AFTER the infiniteness (`hs.mono hsub`).
- `omega` cannot see through `Set.mem_setOf`; `rw [Set.mem_setOf_eq] at h` first.

Card: `docs/drafts/pipeline/3-formalized/product-occupancy-dichotomy-euler-edge.md` (appended).
