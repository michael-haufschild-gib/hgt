# Littlewood Z4: index/cast bridge (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/ZetaLineIndexBridge.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `sum_Icc_cpow_eq_sum_Ico (t) (M)` :
  `∑_{k ∈ Icc 1 M} ((k:ℝ):ℂ)^{−(1+It)} = ∑_{n ∈ Ico 1 (M+1)} (n:ℂ)^{−1−It}`.
  (`Finset.Ico_add_one_right_eq_Icc` for the range; base cast + exponent rearrangement termwise.)
- `cube_le_two_pow_topExponent (ht : 8π ≤ t)` :
  `(t/(8π))³ ≤ ((2^{topExponent t + 1} : ℕ) : ℝ)`.
  (`Nat.lt_floor_add_one` on `topExponent`'s definition, then compare exponentials.)

These close the two mismatches from `route_e/littlewood_z4_partial_sum_truncation_2026_08_06`.
With `M + 1 = 2^{topExponent t + 1}` the truncation reads

`‖ζ(1+It)‖ ≤ ‖∑_{n ∈ Ico 1 (2^{topExponent t+1})} n^{−1−It}‖ + 1/t + ‖1+It‖/M`,

head bounded by `littlewood_littleOh`, last term `≤ (1+t)/((t/8π)³ − 1) → 0`.

## Remaining for Z4

Assemble into a statement about `ζ(1+It)` itself: `∀ ε > 0, ∃ T, ∀ t ≥ T,
‖ζ(1+it)‖ ≤ C + ε·log(t/2π)` — the qualitative `ζ(1+it) = o(log t)`.

## Lean note

For `((k:ℝ):ℂ)^a = (k:ℂ)^b` with `a = −(1+It)`, `b = −1−It`: `congr 1` mis-splits (leaves one goal,
then a second bullet errors "No goals"). Prove the base cast and the exponent equality as separate
`have`s and `rw` both.
