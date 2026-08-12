# ULF-FSR-1 formation-scale / Wiener receiver card — STAGE 3 COMPLETE (2026-08-12)

Card: `docs/drafts/pipeline/3-formalized/universal-law-field/formation-scale-mechanics/one-norm-impossibility-formal-receiver-collapse-and-wiener-scale-fusion-law.md`
Certificate: same folder, `formation-scale-receiver-core-formalized.md` (see its
"Full-surface closure (2026-08-12)" section for the clause→declaration table).

## Lean modules (all wired into `HTGeometry.UniversalLawField`)
1. `HTGeometry/FormationScaleReceiver.lean` (pre-existing, namespace
   `GaloisForLFunctions.HTGeometry` — NOT `HTGeometry`): Thm 2.1
   `no_bounded_derivation_of_generator`, the abstract
   `continuous_receiver_kills_formal_generator`, polynomial-level Thm 5.3.
2. `HTGeometry/WienerFormationScale.lean` (NEW): the scale `W_R` on `ℂ⟦X⟧`.
   `wienerScaleWeight`/`WienerScaleAdmissible`/`wienerScaleNorm`; closure lemmas;
   `wienerScaleNorm_mul_le` (FSR1.11); `wienerScaleNorm_mono`; `wienerScaleEval` with
   `norm_wienerScaleEval_le` (FSR1.13), `wienerScaleEval_mul`, `wienerScaleEvalHom`;
   `wienerScale_collar_bound` + `wienerScaleNorm_derivative_le` (FSR1.15, sharp `1/(R-r)`);
   `wienerScaleAdams` with `wienerScaleNorm_adams : ‖Ψ_q f‖_r = ‖f‖_{r^q}` and
   `wienerScaleNorm_adams_le` (FSR1.19); `derivative_wienerScaleAdams` (FSR1.21) and
   `wienerScaleNorm_derivative_adams_le` (FSR1.22); unconditional `wienerScaleEval_adams`
   (FSR1.23); `wienerScaleGeom`, `wienerScale_witt_fusion` (FSR1.26), `wienerScaleNorm_geom`
   (FSR1.27); `wienerScaleAlgebra` (a `Subalgebra ℂ (PowerSeries ℂ)`); `wienerScaleTrunc`,
   `wienerScaleNorm_sub_trunc`; `exists_eval_of_bounded_character` (Thm 4.1(3)),
   `wienerScaleEval_injective_point`.
3. `HTGeometry/WienerFormationBanach.lean` (NEW): Thm 4.1(1).  `WienerAlgebra R` for
   `[Fact (0 < R)]` with `NormedCommRing`, `NormedAlgebra ℂ`, `CompleteSpace`.  Completeness via
   `isometryLp : WienerAlgebra R ≃ᵢ lp (fun _ : ℕ => ℂ) 1`.
   `exists_eval_of_continuous_character`, `norm_eval_le`, `norm_one_eq`.
4. `HTGeometry/FormalAdicReceiverCollapse.lean` (NEW): Thm 3.1 for the literal `T`-adic topology.
   `formalAdicIdeal`, `formalAdic_tendsto_smul_X_pow` (FSR1.6), `formalAdic_tendsto_trunc`,
   `formalAdicCharacter_apply_X` (FSR1.8), `formalAdicCharacter_eq_constantCoeff` (FSR1.9),
   `formalAdicCharacter_unique`.

Axiom prints on the whole surface: only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella foreground build: 11,857 jobs.

## Deliberately NOT formalized
Section 8's source-compatible scale/sheaf over `Re(s) > 1/2` — the successor research problem.

## Name traps in this area
- `HTGeometry.wienerNorm` is ALREADY TAKEN by `ClockAnalyticWienerScale` (two-sided `ℤ → ℝ`);
  hence the `wienerScale…` prefix everywhere.
- `FormationScaleReceiver` lives in namespace `GaloisForLFunctions.HTGeometry`, the new modules in
  `HTGeometry`.  Cross-references need the full prefix.
- Antidiagonal membership resolves as `List.Nat.mem_antidiagonal` (no `Finset.Nat.mem_antidiagonal`).
- `tsum_ite_eq b a` takes `a : β → α`: write `tsum_ite_eq m fun _ => R ^ m`.
- `WienerScaleAdmissible` unfolds to `Summable`, so `hf.add hg` picks the NEW
  `WienerScaleAdmissible.add`; write `Summable.add hf hg` for the plain one.
- `ℝ≥0∞` notation is not in scope in these files — write `ENNReal`; `ENNReal.toReal_one`
  (not `ENNReal.one_toReal`).
- Subalgebra coercions: `Subalgebra.coe_pow`, `AddSubmonoidClass.coe_finsetSum`
  (there is no `Subalgebra.coe_sum`, no `SubalgebraClass.coe_pow`).
- `PowerSeries.constantCoeff` takes the ring implicitly: `PowerSeries.constantCoeff f`.
- `push_neg` is deprecated and fails the lint gate; use `rw [not_le]` etc.
- `SemilinearMapClass.bound_of_continuous` is the continuous ⇒ bounded lemma
  (no `LinearMap.bound_of_continuous`).
- Mathlib names used: `summable_sum_mul_antidiagonal_of_summable_mul`,
  `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, `Summable.tsum_le_tsum`,
  `Summable.of_nonneg_of_le`, `summable_nat_add_iff`, `Summable.tsum_eq_zero_add`,
  `Summable.sum_add_tsum_nat_add`, `tendsto_sum_nat_add`, `Function.Injective.tsum_eq`,
  `Function.Injective.summable_iff`, `geom_sum_mul`, `pow_le_pow_of_le_one`,
  `PowerSeries.coeff_derivative` (`d⁄dX ℂ`), `PowerSeries.coeff_mul_X_pow'`,
  `PowerSeries.X_pow_dvd_iff`, `Ideal.span_singleton_pow`, `Ideal.hasBasis_nhds_zero_adic`,
  `Ideal.hasBasis_nhds_adic`, `memℓp_gen`, `lp.norm_eq_tsum_rpow`, `lp.memℓp`,
  `IsometryEquiv.completeSpace_iff`, `AddGroupNorm.toNormedAddCommGroup`.
