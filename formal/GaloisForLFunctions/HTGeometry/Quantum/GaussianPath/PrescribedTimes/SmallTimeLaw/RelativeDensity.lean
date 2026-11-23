import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation

/-! # Likelihood of a time rescaling on Gaussian coupling space -/
open MeasureTheory ProbabilityTheory Real Set
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean radius of the independent real coefficients. -/
def energy (x : ι → ℝ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖^2

theorem measurable_energy : Measurable (energy (ι:=ι)) :=
  (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable.pow_const 2

private theorem density_eq (x : ι → ℝ) :
    coordinateGaussianDensityReal x =
      (sqrt (2*π))⁻¹^Fintype.card ι*exp (-energy x/2) :=
  coordinateGaussianDensityReal_ofLp (WithLp.toLp 2 x : EuclideanSpace ℝ ι)

/-- Likelihood relative to the original law for the map x ↦ x/q. -/
def likelihood (q : ℝ) (x : ι → ℝ) : ℝ :=
  q^Fintype.card ι*exp (-(q^2-1)*energy x/2)

theorem measurable_likelihood (q : ℝ) : Measurable (likelihood (ι:=ι) q) := by
  unfold likelihood
  exact measurable_const.mul (measurable_exp.comp ((measurable_const.mul measurable_energy).div_const 2))

theorem gaussian_inverse_scale_law {q : ℝ} (hq : 0 < q) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.map (fun x : ι → ℝ => q⁻¹ • x) = μ.withDensity (fun x => ENNReal.ofReal (likelihood q x)) := by
  intro μ
  have hg := ENNReal.measurable_ofReal.comp (measurable_likelihood (ι:=ι) q)
  have hρ := ENNReal.measurable_ofReal.comp (measurable_coordinateGaussianDensityReal (ι:=ι))
  dsimp only [μ]
  rw [gaussian_dilation_density (inv_pos.mpr hq),measure_pi_gaussianReal_eq_withDensity,←withDensity_mul _ hρ hg]
  apply congrArg ((volume : Measure (ι → ℝ)).withDensity)
  funext x
  have hE : energy (q • x) = q^2*energy x := by
    change ‖q • (WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖^2=q^2*‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖^2
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq,mul_pow]
  simp only [inv_pow,inv_inv,Pi.mul_apply,←ENNReal.ofReal_mul (coordinateGaussianDensityReal_nonneg x)]
  apply congrArg ENNReal.ofReal
  rw [density_eq,density_eq,likelihood,hE]
  have hex : exp (-energy x/2)*exp (-(q^2-1)*energy x/2)=exp (-(q^2*energy x)/2) := by
    rw [←exp_add]
    congr 1
    ring
  rw [←hex]
  ring

#print axioms gaussian_inverse_scale_law
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
