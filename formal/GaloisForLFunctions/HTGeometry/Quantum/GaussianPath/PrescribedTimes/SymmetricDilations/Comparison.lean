import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation

/-! # Comparing Gaussian event probabilities by opposite precision shifts -/
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SymmetricDilations
noncomputable section
variable {ι : Type*} [Fintype ι]

private def density (a : ℝ) (x : ι → ℝ) :=
  (a^Fintype.card ι)⁻¹*coordinateGaussianDensityReal (a⁻¹ • x)

private theorem paired_density {a b : ℝ} (hp : a⁻¹^2+b⁻¹^2=2) (x : ι → ℝ) :
    coordinateGaussianDensityReal (a⁻¹ • x)*coordinateGaussianDensityReal (b⁻¹ • x)=
      (coordinateGaussianDensityReal x)^2 := by
  have hcoord (z : ℝ) : gaussianPDFReal 0 1 (a⁻¹*z)*gaussianPDFReal 0 1 (b⁻¹*z)=
      gaussianPDFReal 0 1 z*gaussianPDFReal 0 1 z := by
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_mul_mul_comm,mul_mul_mul_comm _ (exp _) _ (exp _),←exp_add,←exp_add]
    congr 2
    nlinarith only [congrArg (fun y : ℝ => y*z^2) hp]
  unfold coordinateGaussianDensityReal
  rw [sq,←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => hcoord (x i)

/-- Choosing scales with opposite inverse-variance shifts cancels the
entire Gaussian exponent. If their combined Jacobian is at most four,
the original probability is at most the sum of the two dilated probabilities. -/
theorem gaussian_pair_mass {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hp : a⁻¹^2+b⁻¹^2=2) (hj : (a*b)^Fintype.card ι ≤ 4)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real E ≤ μ.real ((fun x : ι → ℝ => a • x) ⁻¹' E)+μ.real ((fun x : ι → ℝ => b • x) ⁻¹' E) := by
  intro μ
  let ν := (volume : Measure (ι → ℝ))
  let τ (r : ℝ) (x : ι → ℝ) := ENNReal.ofReal (density r x)
  have hn {r : ℝ} (hr : 0<r) (x : ι → ℝ) : 0≤density r x :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) (coordinateGaussianDensityReal_nonneg _)
  have hd (x : ι → ℝ) : coordinateGaussianDensityReal x ≤ density a x+density b x := by
    let d := Fintype.card ι
    have he : (a*b)^d*(density a x*density b x)=(coordinateGaussianDensityReal x)^2 := by
      rw [←paired_density hp x,mul_pow]
      dsimp only [density,d]
      field_simp [ha.ne',hb.ne']
    have h := mul_le_mul_of_nonneg_right hj (mul_nonneg (hn ha x) (hn hb x))
    apply (sq_le_sq₀ (coordinateGaussianDensityReal_nonneg _) (add_nonneg (hn ha _) (hn hb _))).mp
    nlinarith only [he,h,sq_nonneg (density a x-density b x)]
  have hm : μ ≤ Measure.map (fun x : ι → ℝ => a • x) μ+Measure.map (fun x : ι → ℝ => b • x) μ := by
    dsimp only [μ]
    rw [gaussian_dilation_density ha,gaussian_dilation_density hb,measure_pi_gaussianReal_eq_withDensity]
    change ν.withDensity _ ≤ ν.withDensity (τ a)+ν.withDensity (τ b)
    have hτ : Measurable (τ a) := ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_coordinateGaussianDensityReal.comp (measurable_id.const_smul a⁻¹)))
    rw [←withDensity_add_left hτ]
    apply withDensity_mono
    filter_upwards with x
    simpa only [Pi.add_apply,τ,←ENNReal.ofReal_add (hn ha _) (hn hb _)] using ENNReal.ofReal_le_ofReal (hd x)
  have he := hm E
  rw [Measure.add_apply,Measure.map_apply (f:=fun x : ι→ℝ => a • x) (measurable_id.const_smul a) hE,
    Measure.map_apply (f:=fun x : ι→ℝ => b • x) (measurable_id.const_smul b) hE] at he
  simpa only [measureReal_def,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] using
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) he

#print axioms gaussian_pair_mass
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SymmetricDilations
