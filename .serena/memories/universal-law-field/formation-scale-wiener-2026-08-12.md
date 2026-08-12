# ULF-FSR-1 formation-scale / Wiener receiver card — IN PROGRESS (2026-08-12)

Card: `docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-scale-mechanics/one-norm-impossibility-formal-receiver-collapse-and-wiener-scale-fusion-law.md`
Its section 12 is the authoritative remaining-work list.  Ledger row 27.

## Lean modules
- `HTGeometry/FormationScaleReceiver.lean` (pre-existing): Thm 2.1
  `no_bounded_derivation_of_generator`, `continuous_receiver_kills_formal_generator`,
  polynomial-level Thm 5.3 (`derivative_formationAdams`, `eval_formationAdams`,
  `eval_derivative_formationAdams`), log-collar ghost transport.
- `HTGeometry/WienerFormationScale.lean` (NEW, wired into `HTGeometry.UniversalLawField`):
  the scale `W_R` in coefficient coordinates on `ℂ⟦X⟧` — `wienerScaleWeight`,
  `WienerScaleAdmissible`, `wienerScaleNorm`, closure under `+ - • *` with
  `wienerScaleNorm_mul_le` (FSR1.11), `wienerScaleNorm_mono`, `wienerScaleEval` with
  `norm_wienerScaleEval_le` (FSR1.13) and `wienerScaleEval_mul`, `wienerScale_collar_bound` +
  `wienerScaleNorm_derivative_le` (FSR1.15, sharp `1/(R-r)`), `wienerScaleAdams` with the exact
  `wienerScaleNorm_adams : ‖Ψ_q f‖_r = ‖f‖_{r^q}` and `wienerScaleNorm_adams_le` (FSR1.19),
  unconditional `wienerScaleEval_adams` (FSR1.23), `wienerScaleGeom` with
  `one_sub_mul_wienerScaleGeom`, `wienerScale_witt_fusion` (FSR1.26),
  `wienerScaleAdmissible_witt_formation`/`_exterior`, `wienerScaleNorm_geom` (FSR1.27).

## Remaining
1. Banach completeness of `W_R` (Thm 4.1(1)).  Plan: carve `W_R` as a `Subalgebra ℂ (PowerSeries ℂ)`
   using the closure lemmas already proved, build `NormedAddCommGroup`/`NormedRing` from
   `wienerScaleNorm`, and get `CompleteSpace` by an isometric ℂ-linear equivalence with
   `lp (fun _ : ℕ => ℂ) 1` (the map `f ↦ fun n => coeff n f * R^n`).
2. Thm 4.1(3)/(FSR1.28): every bounded unital character is `ev_z`, `‖z‖ ≤ R`.  Proof needs no
   completeness: put `z = χ X`, get `‖z‖^n ≤ C R^n` hence `‖z‖ ≤ R`, then use polynomial density
   in `‖·‖_R` plus boundedness.
3. Series-level Thm 5.3: `D (Ψ_q f) = q X^(q-1) Ψ_q (D f)` (coefficientwise, needs the ℕ-division
   bookkeeping `q ∣ n+1`), and the composite bound (FSR1.22).
4. Thm 3.1 for the literal `T`-adic topology on `ℂ⟦T⟧`.

## Name traps in this area
- `HTGeometry.wienerNorm` is ALREADY TAKEN by `ClockAnalyticWienerScale` (two-sided `ℤ → ℝ`).
  That is why everything here is prefixed `wienerScale…`.
- Antidiagonal membership lemma resolves as `List.Nat.mem_antidiagonal`, not
  `Finset.Nat.mem_antidiagonal` (which does not exist).
- `tsum_ite_eq b a` takes `a : β → α`, so write `tsum_ite_eq m fun _ => R ^ m`.
- `WienerScaleAdmissible` unfolds to `Summable`, so `hf.add hg` picks the *new*
  `WienerScaleAdmissible.add`; write `Summable.add hf hg` when the plain one is meant.
- Mathlib names used: `summable_sum_mul_antidiagonal_of_summable_mul`,
  `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, `Summable.tsum_le_tsum`,
  `Summable.of_nonneg_of_le`, `summable_nat_add_iff`, `Summable.tsum_eq_zero_add`,
  `Function.Injective.tsum_eq`, `Function.Injective.summable_iff`, `geom_sum_mul`,
  `pow_le_pow_of_le_one`, `PowerSeries.coeff_derivative` (`d⁄dX ℂ`), `PowerSeries.coeff_C_mul`,
  `PowerSeries.coeff_succ_X_mul`, `PowerSeries.coeff_zero_X_mul`.
