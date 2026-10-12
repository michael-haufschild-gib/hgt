import GaloisForLFunctions.HTGeometry.BhattacharyyaRealOverlap

/-! Affinity defect splits into a square and singular mass; equality identifies probabilities. -/

noncomputable section
open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

theorem integrable_sqrt_rnDeriv_sub_one_sq
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => (Real.sqrt ((Q.rnDeriv P x).toReal) - 1) ^ 2) P := by
  have hr : Integrable (fun x => (Q.rnDeriv P x).toReal) P :=
    Measure.integrable_toReal_rnDeriv
  have hs := integrable_sqrt_rnDeriv P Q
  apply ((hr.sub (hs.const_mul (2 : ℝ))).add (integrable_const (1 : ℝ))).congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp
    nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg (a := Q.rnDeriv P x))]

theorem bhattacharyya_defect_decomposition
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    2 * (1 - (bhattacharyya P Q).toReal) =
      (∫ x, (Real.sqrt ((Q.rnDeriv P x).toReal) - 1) ^ 2 ∂P) +
        (Q.singularPart P).real Set.univ := by
  have hr : Integrable (fun x => (Q.rnDeriv P x).toReal) P :=
    Measure.integrable_toReal_rnDeriv
  have hs := integrable_sqrt_rnDeriv P Q
  have he (x : α) : (Real.sqrt ((Q.rnDeriv P x).toReal) - 1) ^ 2 =
      (Q.rnDeriv P x).toReal - 2 * Real.sqrt ((Q.rnDeriv P x).toReal) + 1 := by
    nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg (a := Q.rnDeriv P x))]
  have hsub : Integrable (fun x =>
      (Q.rnDeriv P x).toReal - 2 * Real.sqrt ((Q.rnDeriv P x).toReal)) P :=
    hr.sub (hs.const_mul (2 : ℝ))
  have hRN : (∫ x, (Q.rnDeriv P x).toReal ∂P) =
      1 - (Q.singularPart P).real Set.univ := by
    simpa using (Measure.integral_toReal_rnDeriv' (μ := Q) (ν := P))
  have hconst : (∫ _ : α, (1 : ℝ) ∂P) = 1 := by simp
  rw [bhattacharyya_eq_ofReal_integral_sqrt_rnDeriv,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.sqrt_nonneg _)),
    integral_congr_ae (Filter.Eventually.of_forall he),
    integral_add hsub (integrable_const (1 : ℝ)),
    integral_sub hr (hs.const_mul (2 : ℝ)), integral_const_mul, hRN, hconst]
  ring

theorem bhattacharyya_le_one
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    bhattacharyya P Q ≤ 1 := by
  have h := bhattacharyya_defect_decomposition P Q
  rw [bhattacharyya_eq_ofReal_integral_sqrt_rnDeriv,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.sqrt_nonneg _))] at h
  rw [bhattacharyya_eq_ofReal_integral_sqrt_rnDeriv]
  apply ENNReal.ofReal_le_one.mpr
  have hs : 0 ≤ (Q.singularPart P).real Set.univ := ENNReal.toReal_nonneg
  have hi : 0 ≤ ∫ x, (Real.sqrt ((Q.rnDeriv P x).toReal) - 1) ^ 2 ∂P :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

theorem bhattacharyya_eq_one_iff
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    bhattacharyya P Q = 1 ↔ P = Q := by
  constructor
  · intro h
    have hd := bhattacharyya_defect_decomposition P Q
    rw [h, ENNReal.toReal_one] at hd
    have hs : 0 ≤ (Q.singularPart P).real Set.univ := ENNReal.toReal_nonneg
    have hi : 0 ≤ ∫ x, (Real.sqrt ((Q.rnDeriv P x).toReal) - 1) ^ 2 ∂P :=
      integral_nonneg (fun x => sq_nonneg _)
    have hz : (∫ x, (Real.sqrt ((Q.rnDeriv P x).toReal) - 1) ^ 2 ∂P) = 0 := by
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x : α => sq_nonneg (Real.sqrt ((Q.rnDeriv P x).toReal) - 1)))
      (integrable_sqrt_rnDeriv_sub_one_sq P Q)).mp hz
    have hRN : Q.rnDeriv P =ᵐ[P] 1 := by
      filter_upwards [hae, Measure.rnDeriv_lt_top Q P] with x hx hfin
      have hsqrt : Real.sqrt ((Q.rnDeriv P x).toReal) = 1 :=
        sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx)
      have hu : (Q.rnDeriv P x).toReal = 1 := by
        simpa only [hsqrt, one_pow] using
          (Real.sq_sqrt (ENNReal.toReal_nonneg (a := Q.rnDeriv P x))).symm
      change Q.rnDeriv P x = 1
      rw [← ENNReal.ofReal_toReal hfin.ne, hu, ENNReal.ofReal_one]
    have hle : P ≤ Q := by
      calc
        P = P.withDensity (Q.rnDeriv P) := by
          rw [withDensity_congr_ae hRN, withDensity_one]
        _ ≤ Q := Measure.withDensity_rnDeriv_le Q P
    exact Measure.eq_of_le_of_isProbabilityMeasure hle
  · rintro rfl
    exact bhattacharyya_self _

theorem bhattacharyya_lt_one_iff
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    bhattacharyya P Q < 1 ↔ P ≠ Q := by
  rw [lt_iff_le_and_ne, and_iff_right (bhattacharyya_le_one P Q)]
  exact not_congr (bhattacharyya_eq_one_iff P Q)

end GaloisForLFunctions.HTGeometry
