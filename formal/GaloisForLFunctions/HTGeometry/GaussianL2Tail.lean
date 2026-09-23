import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier

/-!
# The `L²` tail of the self-dual Gaussian

The self-dual Gaussian `e^{-πx²}` has `L²` mass `2^{-1/2}` and its mass outside a symmetric window
of radius `T` is at most `e^{-πT²}`.  The estimate is elementary: on `|x| ≥ T` one factor of the
squared Gaussian is already smaller than `e^{-πT²}`, and the remaining factor integrates to one.

Because the Gaussian is a fixed point of the `L²` Fourier transform, the same bound controls the
frequency tail, which is what a wave-packet argument needs on both sides at once.
-/

open MeasureTheory Filter Topology Complex

open scoped FourierTransform Real

namespace GaloisForLFunctions.HTGeometry

/-- The self-dual Gaussian as an `L²` class. -/
noncomputable def gaussLp : Lp (α := ℝ) ℂ 2 := gaussianSchwartz.toLp 2

theorem coeFn_gaussLp :
    (gaussLp : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] fun x => Complex.exp (-(π * (x : ℂ) ^ (2 : ℕ))) := by
  have h := SchwartzMap.coeFn_toLp (p := 2) (μ := (volume : Measure ℝ)) gaussianSchwartz
  filter_upwards [h] with x hx
  rw [gaussLp, hx, gaussianSchwartz_eq_cexp]

theorem normSq_gaussLp_apply {x : ℝ} :
    ‖Complex.exp (-(π * (x : ℂ) ^ (2 : ℕ)))‖ ^ (2 : ℕ) = Real.exp (-(2 * π * x ^ (2 : ℕ))) := by
  have hre : (-(π * (x : ℂ) ^ (2 : ℕ))).re = -(π * x ^ (2 : ℕ)) := by
    simp [Complex.neg_re, pow_two, Complex.mul_re]
  rw [Complex.norm_exp, hre, sq, ← Real.exp_add]
  congr 1
  ring


theorem norm_gaussLp_apply (x : ℝ) :
    ‖Complex.exp (-(π * (x : ℂ) ^ (2 : ℕ)))‖ = Real.exp (-(π * x ^ (2 : ℕ))) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.neg_re, pow_two, Complex.mul_re]

/-- **The `L²` mass of the self-dual Gaussian.** -/
theorem norm_gaussLp_sq : ‖gaussLp‖ ^ (2 : ℕ) = Real.sqrt 2⁻¹ := by
  rw [norm_lpTwo_sq]
  have hint : ∫ x : ℝ, ‖(gaussLp : ℝ → ℂ) x‖ ^ (2 : ℕ)
      = ∫ x : ℝ, Real.exp (-(2 * π) * x ^ (2 : ℕ)) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_gaussLp] with x hx
    rw [hx, normSq_gaussLp_apply]
    congr 1
    ring
  rw [hint, integral_gaussian]
  congr 1
  field_simp

/-- **The Gaussian `L²` tail.**  Outside a symmetric window of radius `T` the squared mass is at
most `e^{-πT²}`. -/
theorem gaussLp_tail_le {T : ℝ} (hT : 0 ≤ T) :
    ∫ x in {x : ℝ | T ≤ |x|}, ‖(gaussLp : ℝ → ℂ) x‖ ^ (2 : ℕ) ≤ Real.exp (-(π * T ^ (2 : ℕ))) := by
  have hmeas : MeasurableSet {x : ℝ | T ≤ |x|} :=
    measurableSet_le measurable_const measurable_norm
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(π * T ^ (2 : ℕ))) * Real.exp (-π * x ^ (2 : ℕ))) := by
    exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have hcongr : ∫ x in {x : ℝ | T ≤ |x|}, ‖(gaussLp : ℝ → ℂ) x‖ ^ (2 : ℕ)
      = ∫ x in {x : ℝ | T ≤ |x|}, Real.exp (-(2 * π * x ^ (2 : ℕ))) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae coeFn_gaussLp] with x hx
    rw [hx, normSq_gaussLp_apply]
  rw [hcongr]
  have hbound : ∀ x ∈ {x : ℝ | T ≤ |x|},
      Real.exp (-(2 * π * x ^ (2 : ℕ)))
        ≤ Real.exp (-(π * T ^ (2 : ℕ))) * Real.exp (-π * x ^ (2 : ℕ)) := by
    intro x hx
    have hx' : T ≤ |x| := hx
    have hsq : T ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by
      have : T ^ (2 : ℕ) ≤ |x| ^ (2 : ℕ) := by nlinarith [abs_nonneg x, hT]
      rwa [sq_abs] at this
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [hsq, Real.pi_pos]
  have hstep : ∫ x in {x : ℝ | T ≤ |x|}, Real.exp (-(2 * π * x ^ (2 : ℕ)))
      ≤ ∫ x in {x : ℝ | T ≤ |x|}, Real.exp (-(π * T ^ (2 : ℕ))) * Real.exp (-π * x ^ (2 : ℕ)) := by
    refine setIntegral_mono_on ?_ hgauss.integrableOn hmeas hbound
    exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 * π)).integrableOn.congr_fun
      (fun x _ => by ring_nf) hmeas
  refine le_trans hstep ?_
  have hfull : ∫ x in {x : ℝ | T ≤ |x|},
      Real.exp (-(π * T ^ (2 : ℕ))) * Real.exp (-π * x ^ (2 : ℕ))
      ≤ ∫ x : ℝ, Real.exp (-(π * T ^ (2 : ℕ))) * Real.exp (-π * x ^ (2 : ℕ)) := by
    refine setIntegral_le_integral hgauss (Filter.Eventually.of_forall fun x => ?_)
    positivity
  refine le_trans hfull ?_
  rw [integral_const_mul, integral_gaussian]
  have hpi : Real.sqrt (π / π) = 1 := by
    rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one]
  rw [hpi, mul_one]

/-- **The Gaussian against an exponential weight.**  Completing the square turns a linear
exponential weight into a shift, so the weighted Gaussian integral is again elementary. -/
theorem integral_exp_linear_mul_gauss (s : ℝ) :
    ∫ y : ℝ, Real.exp (4 * π * s * y - 2 * π * y ^ (2 : ℕ))
      = Real.exp (2 * π * s ^ (2 : ℕ)) * Real.sqrt 2⁻¹ := by
  have hpt : ∀ y : ℝ, Real.exp (4 * π * s * y - 2 * π * y ^ (2 : ℕ))
      = Real.exp (2 * π * s ^ (2 : ℕ)) * Real.exp (-(2 * π) * (y - s) ^ (2 : ℕ)) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [funext hpt, integral_const_mul]
  have hshift : ∫ y : ℝ, Real.exp (-(2 * π) * (y - s) ^ (2 : ℕ))
      = ∫ y : ℝ, Real.exp (-(2 * π) * y ^ (2 : ℕ)) :=
    integral_sub_right_eq_self (fun y => Real.exp (-(2 * π) * y ^ (2 : ℕ))) s
  rw [hshift, integral_gaussian]
  congr 2
  field_simp


end GaloisForLFunctions.HTGeometry
