# Residue reader on an enlarged domain: ℓ¹ + o(1/p) (2026-08-06, fifth pass)

Follows `mem:route_r/first_wall_lane_classified_terminus_2026_08_06`. The lane stays closed as a
criterion; this pass enlarges the *reader's* domain, which is what a producer needs.

## Negligible fields (HTGeometry/CofinalUnitProfileResidue.lean)

`IsCofinitelyNegligible h b := ∀ ε > 0, ∃ s : Set ι, s.Finite ∧ ∀ i ∉ s, ‖b i‖ ≤ ε * h i`

Use `Set` not `Finset` in the definition — a `Finset` membership in a statement drags in
`DecidableEq ι`, and `Set.Finite.toFinset` covers the one place `escapes` needs a Finset.

- Not comparable with ℓ¹ in either direction. Over the primes it means `b(p) = o(1/p)`, and that
  catches NON-summable fields: `∑_p 1/p ~ log log x`, so `b(p) = 1/(p log log p)` diverges while
  `p·b(p) → 0`.
- `tendsto_profileAverage_zero_of_cofinitelyNegligible` — once a stage vanishes on the finite
  exceptional set, `mu_N(i)‖b i‖ ≤ ε (mu_N(i) h i)` holds at EVERY index, so `tsum_stageWeighted_le`
  gives `‖A_N(b)‖ ≤ ε`. No convergence of `b` used.
- Fixed-`N` summability (before escape) needs a majorant: `mu_N h + Set.indicator s (mu_N ‖b‖)`, with
  `summable_of_hasFiniteSupport` + `Set.support_indicator_subset`. Note
  `summable_of_finite_support` is deprecated → `summable_of_hasFiniteSupport`.
- `HasReferenceResidueMod h a c` = residue modulo `ℓ¹ + negligible`; `tendsto_profileAverage_mod`
  reads it; `HasReferenceResidueMod.unique_of_profile` pins it (one line via limit uniqueness —
  much cheaper than redoing the divergence argument on the enlarged class).
- `finite_primes_lt Q`, `isCofinitelyNegligible_primeHarmonic` (from an explicit `o(1/p)` threshold),
  `primeHarmonicWeight_nonneg`.

## Robust criterion (RHTower/RouteRHarmonicQuantumGapCriterion.lean)

- `not_frequently_abs_re_le_of_unit_limit` — sequence-level form; replaced the earlier private
  lemma that was specialized to `profileAverage mu N (W_t)`. Generalizing removed an unused binder.
- `hasReferenceResidueMod_of_negligible_sub_criticalWall` — a producer field `a` with
  `a - W_t` summable or `o(1/p)` carries the same oriented residue.
- `eq_zero_of_frequently_abs_re_profileAverage_le_of_negligible_sub`,
  `riemannHypothesis_of_frequently_negligible_producer` — RH from producer fields that never have to
  equal the first-wall field exactly.
- `primeHarmonicResidueMod_unique`.

## Contention note

Another session ran a full `lake build GaloisForLFunctions.RHTower` concurrently; it transiently
removed `EulerTruncationRigidity.olean`, so `lake env lean` on a consumer failed with "object file
does not exist". That is contention, not a defect — retry after their build, and do not interpret a
missing-olean error as a broken file.
