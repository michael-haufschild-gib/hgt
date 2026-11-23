import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SmallTimeLaw.RelativeDensity
import GaloisForLFunctions.HTGeometry.PowerMeanEssSupLimit

/-! # First-passage probabilities as Gaussian power means -/
open MeasureTheory ProbabilityTheory Filter Set Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
noncomputable section
variable {ι : Type*} [Fintype ι]

private theorem threshold_integral (F : (ι → ℝ) → ℝ) (hf : Measurable F)
    (hom : ∀ a > (0:ℝ), ∀ x, a*F (a • x)=F x) {q : ℝ} (hq : 0 < q) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real {x | F x ≤ q⁻¹} = ∫ x in {x | F x ≤ 1}, likelihood q x ∂μ := by
  intro μ
  let E := {x | F x ≤ 1}
  have hm : MeasurableSet E := measurableSet_le hf measurable_const
  have he : {x | F x ≤ q⁻¹}=(fun x : ι → ℝ => q⁻¹ • x) ⁻¹' E := by
    ext x
    change F x ≤ q⁻¹ ↔ F (q⁻¹ • x) ≤ 1
    calc F x ≤ q⁻¹ ↔ q⁻¹*F (q⁻¹ • x) ≤ q⁻¹*1 := by rw [hom _ (inv_pos.mpr hq),mul_one]
         _ ↔ _ := mul_le_mul_iff_right₀ (inv_pos.mpr hq)
  rw [he,measureReal_def,←Measure.map_apply (f:=fun x : ι → ℝ => q⁻¹ • x) (by fun_prop) hm,
    gaussian_inverse_scale_law hq,withDensity_apply _ hm]
  apply (integral_eq_lintegral_of_nonneg_ae _ (measurable_likelihood q).aestronglyMeasurable).symm
  exact Eventually.of_forall fun x => mul_nonneg (pow_nonneg hq.le _) (exp_pos _).le

/-- On the unit-deadline set, the radial Gaussian exponential records the
energy price of making that passage. Outside the set its contribution is zero. -/
def unitWeight (F : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  {x | F x ≤ 1}.indicator fun x => exp (-energy x/2)

theorem gaussian_passage_power_mean (F : (ι → ℝ) → ℝ) (hf : Measurable F)
    (hom : ∀ a > (0:ℝ), ∀ x, a*F (a • x)=F x) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    Tendsto (fun n : ℕ =>
      (μ.real {x | F x ≤ (sqrt ((n:ℝ)+1))⁻¹}/(sqrt ((n:ℝ)+1))^Fintype.card ι)^((n:ℝ)⁻¹))
      atTop (𝓝 (essSup (unitWeight F) μ)) := by
  intro μ
  let E := {x | F x ≤ 1}
  have hm : MeasurableSet E := measurableSet_le hf measurable_const
  have hfun : Measurable (unitWeight F) :=
    (measurable_exp.comp (measurable_energy.neg.div_const 2)).indicator hm
  have h₀ (x) : 0 ≤ unitWeight F x := indicator_nonneg (fun _ _ => (exp_pos _).le) x
  have h₁ (x) : unitWeight F x ≤ 1 := by
    by_cases hx : x∈E
    · rw [unitWeight,indicator_of_mem hx]
      exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) two_pos.le)
    · rw [unitWeight,indicator_of_notMem hx]; norm_num
  apply (tendsto_rpow_inv_integral_pow μ hfun h₀ h₁).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  let q := sqrt ((n:ℝ)+1)
  have hq : 0 < q := sqrt_pos.mpr (by positivity)
  have hq₂ : q^2-1=(n:ℝ) := by rw [show q^2=(n:ℝ)+1 from sq_sqrt (by positivity)]; ring
  have hprice (x : ι → ℝ) : likelihood q x = q^Fintype.card ι*exp (-energy x/2)^n := by
    rw [likelihood,hq₂,←exp_nat_mul]
    congr 2
    ring
  have hw : (fun x => unitWeight F x^n)=E.indicator (fun x => exp (-energy x/2)^n) := by
    funext x
    by_cases hx : x∈E <;> simp only [unitWeight,indicator_of_mem,indicator_of_notMem,hx,zero_pow hn.ne']
  congr 1
  rw [hw,integral_indicator hm,threshold_integral F hf hom hq]
  simp only [hprice,integral_const_mul, mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]

#print axioms gaussian_passage_power_mean
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
