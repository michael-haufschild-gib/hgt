import GaloisForLFunctions.BiScaleUncertainty.Observation.LognormalMellinAmbiguity
import GaloisForLFunctions.HTGeometry.RepairedFrequencyDensityLaplace
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Positive lognormal relaxation laws with a common advance equation

A sinusoidal Gaussian tilt survives Laplace averaging but disappears from
all integer moments. Exponential tilting translates the log-rate by one,
so every member satisfies the same differential–dilation law.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower.WD
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

@[fun_prop] lemma continuous_gaussianSineDensity (θ q : ℝ) :
    Continuous (gaussianSineDensity θ q) := by
  unfold gaussianSineDensity gaussWeight
  fun_prop

/-- The Laplace relaxation profile in logarithmic time. -/
def lognormalRelaxation (θ x : ℝ) : ℝ :=
  ∫ y : ℝ, Real.exp (-Real.exp (x+y)) * gaussianSineDensity θ (2*Real.pi) y

private lemma relaxation_kernel_le_one (x y : ℝ) : Real.exp (-Real.exp (x+y)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (Real.exp_nonneg _)

lemma integrable_lognormalRelaxation (θ x : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-Real.exp (x+y)) * gaussianSineDensity θ (2*Real.pi) y) := by
  apply (integrable_gaussianSineDensity θ (2*Real.pi)).mono' (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (gaussianSineDensity_nonneg _ _ _))]
  exact mul_le_of_le_one_left (gaussianSineDensity_nonneg _ _ _) (relaxation_kernel_le_one x y)

/-- The relaxation is a normalized average of positive contractions. -/
theorem lognormalRelaxation_bounds (θ x : ℝ) : 0 ≤ lognormalRelaxation θ x ∧ lognormalRelaxation θ x ≤ 1 := by
  constructor
  · exact integral_nonneg fun y => mul_nonneg (Real.exp_nonneg _) (gaussianSineDensity_nonneg _ _ _)
  · rw [← integral_gaussianSineDensity θ (2*Real.pi)]
    apply integral_mono (integrable_lognormalRelaxation θ x) (integrable_gaussianSineDensity _ _)
    intro y
    exact mul_le_of_le_one_left (gaussianSineDensity_nonneg _ _ _) (relaxation_kernel_le_one x y)

/-- No finite logarithmic time has zero survival probability. -/
theorem lognormalRelaxation_pos (θ x : ℝ) : 0 < lognormalRelaxation θ x := by
  apply lt_of_le_of_ne (lognormalRelaxation_bounds θ x).1
  intro hz
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun y => mul_nonneg (Real.exp_nonneg _) (gaussianSineDensity_nonneg _ _ _))
    (integrable_lognormalRelaxation θ x)).mp hz.symm
  have hzero : gaussianSineDensity θ (2*Real.pi) =ᵐ[volume] 0 := by
    filter_upwards [hae] with y hy
    exact (mul_eq_zero.mp hy).resolve_left (Real.exp_ne_zero _)
  have h := integral_congr_ae hzero
  rw [integral_gaussianSineDensity] at h
  simp only [Pi.zero_apply,integral_zero] at h
  norm_num at h

/-- Exponential tilting translates the log-rate by one and preserves the periodic tilt. -/
theorem gaussianSineDensity_integer_tilt (θ y : ℝ) :
    Real.exp y * gaussianSineDensity θ (2*Real.pi) y =
      Real.exp (1/2) * gaussianSineDensity θ (2*Real.pi) (y-1) := by
  have hs : Real.sin (2*Real.pi*(y-1)) = Real.sin (2*Real.pi*y) := by
    rw [show 2*Real.pi*(y-1)=2*Real.pi*y-2*Real.pi by ring,Real.sin_sub_two_pi]
  have he : Real.exp y * gaussWeight y = Real.exp (1/2) * gaussWeight (y-1) := by
    unfold gaussWeight
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  unfold gaussianSineDensity
  rw [hs]
  linear_combination ((1+Real.sin θ*Real.sin (2*Real.pi*y))/Real.sqrt (2*Real.pi))*he

private lemma relaxation_derivative_bound (x y : ℝ) :
    Real.exp (x+y) * Real.exp (-Real.exp (x+y)) ≤ 1 := by
  rw [Real.exp_neg,← div_eq_mul_inv]
  apply (div_le_one (Real.exp_pos _)).mpr
  linarith only [Real.add_one_le_exp (Real.exp (x+y))]

/-- Differentiation of the actual Gaussian average is justified by a global integrable bound. -/
theorem lognormalRelaxation_hasDerivAt_integral (θ x : ℝ) :
    HasDerivAt (lognormalRelaxation θ)
      (∫ y : ℝ, -(Real.exp (x+y)*Real.exp (-Real.exp (x+y))) * gaussianSineDensity θ (2*Real.pi) y) x := by
  let F : ℝ → ℝ → ℝ := fun u y => Real.exp (-Real.exp (u+y))*gaussianSineDensity θ (2*Real.pi) y
  let F' : ℝ → ℝ → ℝ := fun u y => -(Real.exp (u+y)*Real.exp (-Real.exp (u+y)))*gaussianSineDensity θ (2*Real.pi) y
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := gaussianSineDensity θ (2*Real.pi))
    (s := univ) (x₀ := x) (by simp)
    (Eventually.of_forall fun u => (show Continuous (F u) by dsimp [F]; fun_prop).aestronglyMeasurable)
    (integrable_lognormalRelaxation θ x)
    (show AEStronglyMeasurable (F' x) volume by dsimp [F']; fun_prop)
    (Eventually.of_forall fun y u _ => by
      dsimp only [F']
      rw [norm_mul,norm_neg,Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)),
        Real.norm_of_nonneg (gaussianSineDensity_nonneg _ _ _)]
      exact mul_le_of_le_one_left (gaussianSineDensity_nonneg _ _ _) (relaxation_derivative_bound u y))
    (integrable_gaussianSineDensity θ (2*Real.pi))
    (Eventually.of_forall fun y u _ => by
      have hd := (((hasDerivAt_id u).add_const y).exp.neg.exp).mul_const
        (gaussianSineDensity θ (2*Real.pi) y)
      convert! hd using 1
      dsimp [F,F']
      ring)
  exact h.2

/-- Every positive perturbation satisfies the same advance equation in logarithmic time. -/
theorem lognormalRelaxation_advance_equation (θ x : ℝ) :
    HasDerivAt (lognormalRelaxation θ) (-Real.exp (x+1/2)*lognormalRelaxation θ (x+1)) x := by
  convert lognormalRelaxation_hasDerivAt_integral θ x using 1
  have he (y : ℝ) :
      -(Real.exp (x+y)*Real.exp (-Real.exp (x+y)))*gaussianSineDensity θ (2*Real.pi) y =
      -Real.exp (x+1/2) * (Real.exp (-Real.exp ((x+1)+(y-1)))*gaussianSineDensity θ (2*Real.pi) (y-1)) := by
    rw [show (x+1)+(y-1)=x+y by ring,Real.exp_add x (1/2)]
    have h := gaussianSineDensity_integer_tilt θ y
    rw [Real.exp_add x y]
    linear_combination -Real.exp x*Real.exp (-(Real.exp x*Real.exp y))*h
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  symm
  exact integral_sub_right_eq_self
    (fun y : ℝ => Real.exp (-Real.exp ((x+1)+y))*gaussianSineDensity θ (2*Real.pi) y) 1

/-- The normalized tilted Gaussian law of the logarithmic rate. -/
def gaussianSineMeasure (θ : ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (gaussianSineDensity θ (2*Real.pi) y))

instance gaussianSineMeasure_finite (θ : ℝ) : IsFiniteMeasure (gaussianSineMeasure θ) :=
  isFiniteMeasure_withDensity_ofReal (integrable_gaussianSineDensity θ (2*Real.pi)).hasFiniteIntegral

instance gaussianSineMeasure_probability (θ : ℝ) : IsProbabilityMeasure (gaussianSineMeasure θ) := by
  constructor
  rw [gaussianSineMeasure,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianSineDensity θ (2*Real.pi))
      (Eventually.of_forall (gaussianSineDensity_nonneg θ (2*Real.pi))),
    integral_gaussianSineDensity,ENNReal.ofReal_one]

lemma integral_gaussianSineMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (θ : ℝ) (g : ℝ → E) :
    (∫ y, g y ∂gaussianSineMeasure θ) = ∫ y, gaussianSineDensity θ (2*Real.pi) y • g y := by
  rw [gaussianSineMeasure,integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gaussianSineDensity_nonneg _ _ _)]

/-- The positive random rate obtained by exponentiating the tilted Gaussian. -/
def lognormalSineMeasure (θ : ℝ) : Measure ℝ := Measure.map Real.exp (gaussianSineMeasure θ)

instance lognormalSineMeasure_finite (θ : ℝ) : IsFiniteMeasure (lognormalSineMeasure θ) :=
  Measure.isFiniteMeasure_map _ _

instance lognormalSineMeasure_probability (θ : ℝ) : IsProbabilityMeasure (lognormalSineMeasure θ) := by
  constructor
  rw [lognormalSineMeasure,Measure.map_apply Real.measurable_exp MeasurableSet.univ]
  simp only [preimage_univ,measure_univ]

lemma lognormalSineMeasure_supported (θ : ℝ) : lognormalSineMeasure θ (Ici (0:ℝ))ᶜ = 0 := by
  rw [lognormalSineMeasure,Measure.map_apply Real.measurable_exp measurableSet_Ici.compl]
  have he : Real.exp ⁻¹' (Ici (0:ℝ))ᶜ = ∅ := by
    ext y
    simp only [mem_preimage,mem_compl_iff,mem_Ici,not_le,mem_empty_iff_false,iff_false]
    exact not_lt.mpr (Real.exp_nonneg y)
  rw [he,measure_empty]

lemma integral_lognormalSineMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (θ : ℝ) (g : ℝ → E) :
    (∫ r, g r ∂lognormalSineMeasure θ) =
      ∫ y, gaussianSineDensity θ (2*Real.pi) y • g (Real.exp y) := by
  have hm : MeasurableEmbedding Real.exp := Real.continuous_exp.measurableEmbedding Real.exp_injective
  rw [lognormalSineMeasure,hm.integral_map,integral_gaussianSineMeasure]

/-- The logarithmic-time profile is the actual probability Laplace transform. -/
theorem laplace_lognormalSineMeasure (θ x : ℝ) :
    (∫ r, Real.exp (-Real.exp x*r) ∂lognormalSineMeasure θ) = lognormalRelaxation θ x := by
  rw [integral_lognormalSineMeasure,lognormalRelaxation]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul,Real.exp_add,neg_mul]
  ring

/-- The same positive rate measure realizes all previously calculated complex moments. -/
theorem complexMoment_lognormalSineMeasure (θ : ℝ) (z : ℂ) :
    (∫ r, Complex.exp (z*Real.log r) ∂lognormalSineMeasure θ) = lognormalSineMoment θ z := by
  rw [integral_lognormalSineMeasure,lognormalSineMoment]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Real.log_exp,Complex.real_smul]
  ring

/-- The full relaxation curve identifies exactly the coefficient invisible to integer moments. -/
theorem lognormalRelaxation_eq_iff (θ φ : ℝ) :
    lognormalRelaxation θ = lognormalRelaxation φ ↔ Real.sin θ=Real.sin φ := by
  constructor
  · intro h
    have hm : lognormalSineMeasure θ=lognormalSineMeasure φ := by
      apply GaloisForLFunctions.HTGeometry.measure_eq_of_laplace_eq
        (lognormalSineMeasure_supported θ) (lognormalSineMeasure_supported φ)
      intro t ht
      have he := congrFun h (Real.log t)
      rw [← laplace_lognormalSineMeasure,← laplace_lognormalSineMeasure,Real.exp_log ht] at he
      exact he
    have hq := congrArg (fun μ : Measure ℝ => ∫ r, Complex.exp ((1/4:ℂ)*Real.log r) ∂μ) hm
    rw [complexMoment_lognormalSineMeasure,complexMoment_lognormalSineMeasure] at hq
    exact (lognormalSineMoment_quarter_eq_iff θ φ).mp hq
  · intro h
    funext x
    unfold lognormalRelaxation gaussianSineDensity
    rw [h]

/-- Positivity and the common advance equation do not determine a unique relaxation law. -/
theorem lognormalRelaxation_distinct :
    lognormalRelaxation 0 ≠ lognormalRelaxation (Real.pi/2) := by
  intro h
  have hs := (lognormalRelaxation_eq_iff 0 (Real.pi/2)).mp h
  norm_num only [Real.sin_zero,Real.sin_pi_div_two] at hs

#print axioms lognormalRelaxation_pos
#print axioms lognormalRelaxation_advance_equation
#print axioms lognormalRelaxation_eq_iff
#print axioms lognormalRelaxation_distinct
end
end GaloisForLFunctions.BiScaleUncertainty.Observation
