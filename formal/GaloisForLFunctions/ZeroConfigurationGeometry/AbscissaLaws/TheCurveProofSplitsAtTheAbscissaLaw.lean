import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration
import GaloisForLFunctions.CountingHolography.TheCountLawOfATrueCurveAtEveryGenus

/-!
# The curve proof splits at the abscissa law

For every curve datum in the strip, stated in the coordinate `s` where `ζ`'s laws live
(`curve_template_split`):

* **AAL is free**: the zeros are periodic in height (the Frobenius);
* **the crude half is everything**: a crude count `|N_n − qⁿ − 1| ≤ C qⁿᐟ²` at every level, ZAL,
  purity of the zeros and unitarity of the Frobenius eigenvalues are equivalent.

So the curve proof's two steps — Stepanov's crude count and the power-sum self-improvement — both
sit inside ZAL; the eventual-to-global step AAL is supplied by periodicity, which `ζ` lacks.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.ZeroConfigurationGeometry.CurveAbscissa

open ArithmeticCastelnuovoSeveri ConfigAbscissa

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- A unitary datum has traces bounded by its rank. -/
theorem abs_trace_le_card_of_unitary (hU : ∀ i, ‖D.β i‖ = 1) (n : ℕ) :
    |D.trace n| ≤ Fintype.card ι := by
  have h : ‖D.powerSum n‖ ≤ Fintype.card ι := by
    unfold CurveDatum.powerSum
    calc ‖∑ i, D.β i ^ n‖ ≤ ∑ i, ‖D.β i ^ n‖ := norm_sum_le _ _
      _ = ∑ _i : ι, (1 : ℝ) := by simp [norm_pow, hU]
      _ = Fintype.card ι := by simp
  rwa [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The curve proof splits at the abscissa law.** -/
theorem curve_template_split :
    AbscissaLaw (D.curveConfig hD) ∧
      [∃ C : ℝ, ∀ n, 1 ≤ n → |D.pointCount n - (D.q ^ n + 1)| ≤ C * D.sqrtq ^ n,
        ApproachesLine (D.curveConfig hD),
        Pure (D.curveConfig hD),
        ∀ i, ‖D.β i‖ = 1].TFAE := by
  refine ⟨curveConfig_abscissaLaw D hD, ?_⟩
  tfae_have 1 → 4 := by
    rintro ⟨C, hC⟩
    refine CountingHolography.unitary_of_crude_trace_bound D (C := C) fun n hn => ?_
    have h := hC n hn
    rw [CountingHolography.abs_pointCount_sub, mul_comm C] at h
    exact le_of_mul_le_mul_left h (pow_pos D.sqrtq_pos n)
  tfae_have 4 → 1 := by
    intro hU
    refine ⟨Fintype.card ι, fun n _ => ?_⟩
    rw [CountingHolography.abs_pointCount_sub, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_trace_le_card_of_unitary D hU n)
      (pow_pos D.sqrtq_pos n).le
  tfae_have 2 ↔ 4 := curveConfig_approachesLine_iff_unitary D hD
  tfae_have 3 ↔ 4 := curveConfig_pure_iff_unitary D hD
  tfae_finish

end GaloisForLFunctions.ZeroConfigurationGeometry.CurveAbscissa
