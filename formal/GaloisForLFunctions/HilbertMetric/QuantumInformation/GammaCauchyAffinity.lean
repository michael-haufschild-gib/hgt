import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchySolitonScattering
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import Mathlib.Probability.Distributions.Gamma

/-!
# Gamma affinities and fractional Cauchy dephasing

The weighted geometric mean of two Gamma densities with common shape is
a scaled Gamma density at the interpolated rate. At weight one half its
mass is exactly the Cauchy coherence raised to the common shape. Thus
every nonnegative real Schur power is a positive correlation kernel.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing.GammaAffinity

abbrev Shape := {a : ℝ // 0<a}
abbrev Weight := {p : ℝ // 0<p ∧ p<1}

/-- The rate parameter of the density is exp s. -/
def density (a : Shape) (s : ℝ) := gammaPDFReal a.val (Real.exp s)

theorem density_mass (a : Shape) (s : ℝ) : (∫ x, density a s x)=1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (gammaPDFReal_nonneg a.property (Real.exp_pos s)))
    (measurable_gammaPDFReal _ _).aestronglyMeasurable]
  exact congrArg ENNReal.toReal (lintegral_gammaPDF_eq_one a.property (Real.exp_pos s)) |>.trans ENNReal.toReal_one

theorem density_integrable (a : Shape) (s : ℝ) : Integrable (density a s) := by
  by_contra h
  exact one_ne_zero ((density_mass a s).symm.trans (integral_undef h))

private def tilt (a s x : ℝ) := a*s+(1-Real.exp s)*x

private theorem density_tilt (a : Shape) (s x : ℝ) :
    density a s x = Real.exp (tilt a.val s x)*density a 0 x := by
  by_cases hx : 0≤x
  · simp only [density,gammaPDFReal,if_pos hx,Real.exp_zero,Real.one_rpow,one_mul,
      Real.rpow_def_of_pos (Real.exp_pos s),Real.log_exp]
    unfold tilt
    have he : Real.exp (a.val*s+(1-Real.exp s)*x)*Real.exp (-x) =
        Real.exp (s*a.val)*Real.exp (-(Real.exp s*x)) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    linear_combination ((x^(a.val-1))/Real.Gamma a.val)*he.symm
  · simp [density,gammaPDFReal,hx]

def mixRate (p : ℝ) (s t : ℝ) := p*Real.exp s+(1-p)*Real.exp t
def logAffinity (p : ℝ) (s t : ℝ) := p*s+(1-p)*t-Real.log (mixRate p s t)

/-- Changing log-rate preserves support and multiplies the density by
an exponential affine in the sample. -/
theorem density_change_rate (a : Shape) (s t x : ℝ) :
    density a s x=Real.exp (a.val*(s-t)+(Real.exp t-Real.exp s)*x)*density a t x := by
  rw [density_tilt a s,density_tilt a t,← mul_assoc,← Real.exp_add]
  congr 2
  unfold tilt
  ring

private theorem mix_pos (p : Weight) (s t : ℝ) : 0<mixRate p.val s t :=
  add_pos (mul_pos p.property.1 (Real.exp_pos s)) (mul_pos (sub_pos.mpr p.property.2) (Real.exp_pos t))

/-- Pointwise Chernoff interpolation, including the common vanishing support. -/
theorem interpolate_density (a : Shape) (p : Weight) (s t x : ℝ) :
    (density a s x)^p.val*(density a t x)^(1-p.val) =
      Real.exp (a.val*logAffinity p.val s t)*density a (Real.log (mixRate p.val s t)) x := by
  let b := density a 0 x
  by_cases hz : b=0
  · rw [density_tilt a s,density_tilt a t,density_tilt a (Real.log _)]
    change (_*b)^p.val*(_*b)^(1-p.val)=_*(_*b)
    simp [hz,Real.zero_rpow p.property.1.ne']
  have hb : 0<b := (lt_of_le_of_ne (gammaPDFReal_nonneg a.property (Real.exp_pos 0) x) hz.symm)
  rw [density_tilt a s,density_tilt a t,density_tilt a (Real.log _)]
  change (Real.exp _*b)^p.val*(Real.exp _*b)^(1-p.val)=_*(Real.exp _*b)
  rw [Real.mul_rpow (Real.exp_pos _).le hb.le,Real.mul_rpow (Real.exp_pos _).le hb.le]
  have hpow : b^p.val*b^(1-p.val)=b := by rw [← Real.rpow_add hb]; simp
  rw [mul_mul_mul_comm, hpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),
    Real.log_exp,Real.log_exp,← Real.exp_add,← mul_assoc,← Real.exp_add]
  congr 2
  simp only [tilt,logAffinity,Real.exp_log (mix_pos p s t),mixRate]
  ring

/-- Exact Chernoff coefficient at every interior weight. -/
theorem chernoff_mass (a : Shape) (p : Weight) (s t : ℝ) :
    (∫ x, (density a s x)^p.val*(density a t x)^(1-p.val))=Real.exp (a.val*logAffinity p.val s t) := by
  simp only [interpolate_density,integral_const_mul,density_mass,mul_one]

private def half : Weight := ⟨1/2,by norm_num,by norm_num⟩

private theorem log_half (s t : ℝ) : logAffinity half.val s t = Real.log (coherence s t) := by
  have h : mixRate half.val s t=(Real.exp s+Real.exp t)/2 := by unfold mixRate half; ring
  rw [logAffinity,h,Real.log_div (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne' (by norm_num)]
  simp only [coherence,Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_exp,half]
  ring

/-- The product of the square-root features factors into the Cauchy
coherence and one normalized Gamma density. -/
theorem hellinger_product (a : Shape) (s t x : ℝ) :
    Real.sqrt (density a s x)*Real.sqrt (density a t x) =
      (coherence s t)^a.val*density a (Real.log ((Real.exp s+Real.exp t)/2)) x := by
  have e := interpolate_density a half s t x
  have hm : mixRate half.val s t=(Real.exp s+Real.exp t)/2 := by unfold mixRate half; ring
  rw [log_half,hm] at e
  change (density a s x)^(1/2:ℝ)*(density a t x)^(1-1/2:ℝ)=_ at e
  rw [show (1-1/2:ℝ)=1/2 by norm_num,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at e
  rwa [Real.rpow_def_of_pos (coherence_pos _ _),mul_comm (Real.log _) a.val]

theorem hellinger_mass (a : Shape) (s t : ℝ) :
    (∫ x, Real.sqrt (density a s x)*Real.sqrt (density a t x))=(coherence s t)^a.val := by
  simp only [hellinger_product,integral_const_mul,density_mass,mul_one]

/-- The correlation symbol of the real-time Cauchy semigroup. -/
def fractionalSymbol {n : ℕ} (a : ℝ) (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ((coherence (r i) (r j))^a : ℝ)

private def feature {n : ℕ} (a : Shape) (r : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℂ :=
  Real.sqrt (density a (r i) x)

private theorem inner_feature {n : ℕ} (a : Shape) (r : Fin n → ℝ) (i j : Fin n) (x : ℝ) :
    feature a r i x*(starRingEnd ℂ) (feature a r j x) =
      ((coherence (r i) (r j))^a.val*density a (Real.log ((Real.exp (r i)+Real.exp (r j))/2)) x : ℝ) := by
  simp only [feature,Complex.conj_ofReal,← Complex.ofReal_mul,hellinger_product]

/-- All nonnegative real powers give positive complex Gram matrices on
arbitrary finite probes, including repeated labels and time zero. -/
theorem fractional_positive {n : ℕ} (t : ℝ≥0) (r : Fin n → ℝ) : (fractionalSymbol t.val r).PosSemidef := by
  rcases eq_or_lt_of_le t.property with h|h
  · have H := symbol_posSemidef (fun _ : Fin n => (0:ℝ))
    change (Matrix.of fun _ _ : Fin n => (coherence 0 0:ℂ)).PosSemidef at H
    simpa only [fractionalSymbol,← h,Real.rpow_zero,coherence_self,Complex.ofReal_one] using H
  let a : Shape := ⟨t.val,h⟩
  have eq : fractionalSymbol t.val r=HTGeometry.complexFeatureGram volume (feature a r) := by
    ext i j
    simp only [fractionalSymbol,Matrix.of_apply,HTGeometry.complexFeatureGram,inner_feature,
      integral_complex_ofReal,integral_const_mul,density_mass,mul_one,a]
  rw [eq]
  apply HTGeometry.complexFeatureGram_posSemidef
  intro i j
  simp only [inner_feature]
  exact ((density_integrable a _).const_mul _).ofReal

#print axioms chernoff_mass
#print axioms hellinger_product
#print axioms hellinger_mass
#print axioms fractional_positive
end GaloisForLFunctions.HilbertMetric.CauchyDephasing.GammaAffinity
