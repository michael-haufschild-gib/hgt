import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Domination of a standard Gaussian by its positive dilations -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section
variable {ι : Type*} [Fintype ι]

private def scaleEquiv (a : ℝ) (ha : a ≠ 0) : (ι → ℝ) ≃ᵐ (ι → ℝ) where
  toFun x := a • x
  invFun y := a⁻¹ • y
  left_inv x := by change a⁻¹ • (a • x) = x; rw [smul_smul,inv_mul_cancel₀ ha,one_smul]
  right_inv x := by change a • (a⁻¹ • x) = x; rw [smul_smul,mul_inv_cancel₀ ha,one_smul]
  measurable_toFun := measurable_id.const_smul a
  measurable_invFun := measurable_id.const_smul a⁻¹

private theorem density_contraction (x : ι → ℝ) {a : ℝ} (ha : 1 ≤ a) :
    coordinateGaussianDensityReal x ≤ coordinateGaussianDensityReal (a⁻¹ • x) := by
  have hp : 0 < a := zero_lt_one.trans_le ha
  have hinv : a⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr ha
  apply Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _)
  intro i _
  simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one,Pi.smul_apply,smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hinv 2) (sq_nonneg (x i))
  rw [one_pow,one_mul,← mul_pow] at h
  linarith only [h]

/-- Expanding a standard Gaussian by a ≥ 1 lowers its mass on a measurable
set by at most the Jacobian a^m. This compares the full joint laws. -/
theorem gaussian_dilation_comparison {a : ℝ} (ha : 1 ≤ a) (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    μ.real E ≤ a^(Fintype.card ι)*μ.real ((fun x : ι → ℝ => a • x) ⁻¹' E) := by
  intro μ
  have hp : 0 < a := zero_lt_one.trans_le ha
  let e := scaleEquiv (ι := ι) a hp.ne'
  let m := Fintype.card ι
  let ρ (x : ι → ℝ) := ENNReal.ofReal (coordinateGaussianDensityReal x)
  let ν := (volume : Measure (ι → ℝ))
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp measurable_coordinateGaussianDensityReal
  have hv : Measure.map e ν = ENNReal.ofReal ((a^m)⁻¹) • ν := by
    change Measure.map (fun x : ι → ℝ => a • x) ν = _
    simpa only [Module.finrank_fintype_fun_eq_card,abs_of_pos (inv_pos.mpr (pow_pos hp _))] using
        Measure.map_addHaar_smul ν hp.ne'
  have hm : μ ≤ ENNReal.ofReal (a^m) • Measure.map e μ := by
    have hμ : μ = ν.withDensity ρ := measure_pi_gaussianReal_eq_withDensity
    rw [hμ,map_withDensity_measurableEquiv ν e hρ,hv,withDensity_smul_measure,smul_smul,
      ← ENNReal.ofReal_mul (pow_nonneg hp.le _),mul_inv_cancel₀ (pow_ne_zero _ hp.ne'),ENNReal.ofReal_one,one_smul]
    exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (density_contraction x ha))
  have hprob := hm E
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply e.measurable hE] at hprob
  have hf : ENNReal.ofReal (a^m)*μ (e ⁻¹' E) ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have he : (e : (ι → ℝ) → (ι → ℝ)) = (fun x => a • x) := rfl
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hp.le _),he,m] using ENNReal.toReal_mono hf hprob

#print axioms gaussian_dilation_comparison
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
