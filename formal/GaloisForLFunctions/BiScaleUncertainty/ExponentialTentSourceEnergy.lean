import GaloisForLFunctions.BiScaleUncertainty.ExponentialTentMoments

/-! Matching reciprocal-width bounds for the energy of exponential tent sources. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem exponentialTentSource_sq (δ x : ℝ) :
    exponentialTentSource δ x^2 = Real.exp x*(exponentialTentDensity δ x)^2 := by
  rw [exponentialTentSource, mul_pow]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem integrable_exponentialTentSource_sq (δ : ℝ) :
    Integrable (fun x => exponentialTentSource δ x^2) := by
  apply ((continuous_exponentialTentSource δ).pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using
    (hasCompactSupport_exponentialTentSource δ).mul_left (f := exponentialTentSource δ)

theorem integral_exponentialTentSource_sq_eq (δ : ℝ) :
    (∫ x : ℝ, exponentialTentSource δ x^2) =
      ∫ x in Icc 0 (2*δ), exponentialTentSource δ x^2 := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [exponentialTentSource, exponentialTentDensity_zero_of_not_mem δ hx]

theorem exponentialTentDensity_bound {δ x : ℝ} (hδ : 0 ≤ δ) (hx : x ∈ Icc 0 (2*δ)) :
    exponentialTentDensity δ x ≤ δ*Real.exp (2*δ)/(Real.exp δ-1)^2 := by
  unfold exponentialTentDensity
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h := mul_le_mul (Real.exp_le_exp.mpr hx.2) (causalTent_le hδ x)
    (causalTent_nonneg δ x) (Real.exp_pos (2*δ)).le
  nlinarith

/-- The shrinking collar forces a nonzero reciprocal-width source cost. -/
theorem exponentialTentSource_energy_lower {δ : ℝ} (hδ : 0 < δ) :
    1/(2*δ) ≤ ∫ x : ℝ, exponentialTentSource δ x^2 := by
  have hc := continuous_exponentialTentDensity δ
  have hv : 0 ≤ ∫ x in Icc 0 (2*δ), (exponentialTentDensity δ x-1/(2*δ))^2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have hconst : (∫ _x in Icc (0 : ℝ) (2*δ), (1/(2*δ))^2) = 1/(2*δ) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity : 0 ≤ 2*δ),
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp
  have hf : (fun x => (exponentialTentDensity δ x-1/(2*δ))^2) =
      fun x => exponentialTentDensity δ x^2-(1/δ)*exponentialTentDensity δ x+(1/(2*δ))^2 := by
    funext x
    ring
  have hi1 : IntegrableOn (fun x => exponentialTentDensity δ x^2) (Icc 0 (2*δ)) :=
    (hc.pow 2).integrableOn_Icc
  have hi2 : IntegrableOn (fun x => (1/δ)*exponentialTentDensity δ x) (Icc 0 (2*δ)) :=
    (hc.integrableOn_Icc).const_mul _
  have his : IntegrableOn (fun x => exponentialTentDensity δ x^2-(1/δ)*exponentialTentDensity δ x)
      (Icc 0 (2*δ)) := hi1.sub hi2
  rw [hf, integral_add his continuous_const.integrableOn_Icc,
    integral_sub hi1 hi2, integral_const_mul,
    integral_Icc_exponentialTentDensity hδ, hconst] at hv
  have hlo : 1/(2*δ) ≤ ∫ x in Icc 0 (2*δ), exponentialTentDensity δ x^2 := by
    have heq : 1/δ = 2*(1/(2*δ)) := by ring
    rw [heq] at hv
    linarith
  rw [integral_exponentialTentSource_sq_eq]
  apply hlo.trans
  apply setIntegral_mono_on (hc.pow 2).integrableOn_Icc
    ((continuous_exponentialTentSource δ).pow 2).integrableOn_Icc measurableSet_Icc
  intro x hx
  change exponentialTentDensity δ x^2 ≤ exponentialTentSource δ x^2
  rw [exponentialTentSource_sq]
  have he : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx.1
  nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp x-1) (sq_nonneg (exponentialTentDensity δ x))]

/-- The source cost is at most an explicit exponential factor times reciprocal width. -/
theorem exponentialTentSource_energy_upper {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, exponentialTentSource δ x^2) ≤ Real.exp (4*δ)/δ := by
  have hc := continuous_exponentialTentDensity δ
  have heps : δ ≤ Real.exp δ-1 := by linarith [Real.add_one_le_exp δ]
  have heps0 : 0 < Real.exp δ-1 := by linarith
  have hp (x : ℝ) (hx : x ∈ Icc 0 (2*δ)) :
      exponentialTentSource δ x^2 ≤
        (δ*Real.exp (4*δ)/(Real.exp δ-1)^2)*exponentialTentDensity δ x := by
    rw [exponentialTentSource_sq]
    have h0 := exponentialTentDensity_nonneg δ x
    have hb := exponentialTentDensity_bound hδ.le hx
    have he := Real.exp_le_exp.mpr hx.2
    calc
      _ = (Real.exp x*exponentialTentDensity δ x)*exponentialTentDensity δ x := by ring
      _ ≤ (Real.exp (2*δ)*(δ*Real.exp (2*δ)/(Real.exp δ-1)^2))*exponentialTentDensity δ x :=
        mul_le_mul_of_nonneg_right (mul_le_mul he hb h0 (Real.exp_pos _).le) h0
      _ = _ := by
        rw [show 4*δ = 2*δ+2*δ by ring, Real.exp_add]
        ring
  rw [integral_exponentialTentSource_sq_eq]
  calc
    _ ≤ ∫ x in Icc 0 (2*δ),
        (δ*Real.exp (4*δ)/(Real.exp δ-1)^2)*exponentialTentDensity δ x :=
      setIntegral_mono_on ((continuous_exponentialTentSource δ).pow 2).integrableOn_Icc
        (continuous_const.mul hc).integrableOn_Icc measurableSet_Icc hp
    _ = δ*Real.exp (4*δ)/(Real.exp δ-1)^2 := by
      rw [integral_const_mul, integral_Icc_exponentialTentDensity hδ, mul_one]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < (Real.exp δ-1)^2) hδ).2
      have hsq : δ^2 ≤ (Real.exp δ-1)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (Real.exp_pos (4*δ)).le]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
