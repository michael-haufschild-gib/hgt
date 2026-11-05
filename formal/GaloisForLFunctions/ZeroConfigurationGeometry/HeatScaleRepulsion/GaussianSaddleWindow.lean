import GaloisForLFunctions.RHTower.Heat.HeatEulerAnchor
import GaloisForLFunctions.RHTower.HeatGaussianScaledModelError

/-!
# Gaussian estimates at a moving horizontal saddle

Completing the square isolates the saddle mass. The lower tail has the
Gaussian cost of its distance from the saddle. Reflection suppresses
the opposite half on every interval separated from the origin.
-/

open Complex MeasureTheory Filter Set
open _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- Relative error for an exponential model with logarithmic slope error `B`. -/
def gaussianSaddleModelError (B t : ℝ) : ℝ :=
  2 * B * Real.sqrt t * Real.exp (t * (1 / Real.sqrt t + B) ^ 2)

theorem gaussianSaddleModelError_nonneg {B t : ℝ} (hB : 0 ≤ B) :
    0 ≤ gaussianSaddleModelError B t := by
  unfold gaussianSaddleModelError
  positivity

/-- The model error is measured at the Gaussian scale `√t`. -/
theorem gaussian_saddle_model_error_le {B t α y N : ℝ}
    (ht : 0 < t) (hB : 0 ≤ B) (hN : 0 ≤ N) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        (∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
          (Real.exp (B * |w - (y + 2 * t * α)|) - 1)) ≤
      N * Real.exp (-(t * α ^ 2)) * gaussianSaddleModelError B t := by
  have hb := integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le_scaled ht y α
    hB (Real.sqrt_pos.mpr ht)
  calc
    _ ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
        (2 * B * Real.sqrt t * Real.exp (t * (1 / Real.sqrt t + B) ^ 2) *
          Real.exp (y * α + t * α ^ 2)) := by gcongr
    _ = N * (Real.exp (-((y + 2 * t * α) * α)) * Real.exp (y * α + t * α ^ 2)) *
        gaussianSaddleModelError B t := by rw [gaussianSaddleModelError]; ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem integrable_gaussian_saddle_envelope {B t α y : ℝ} (ht : 0 < t) (hB : 0 ≤ B) :
    Integrable (fun w => gaussDensity t (w - y) * Real.exp (w * α) *
      Real.exp (B * |w - (y + 2 * t * α)|)) := by
  refine ((integrable_gaussDensity_sub_mul_rexp ht y α).add
    (integrable_modelError ht y α (y + 2 * t * α) B hB)).congr
      (Eventually.of_forall fun w => ?_)
  dsimp only [Pi.add_apply]
  ring

theorem integral_gaussian_saddle_envelope_le {B t α y : ℝ} (ht : 0 < t) (hB : 0 ≤ B) :
    (∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
      Real.exp (B * |w - (y + 2 * t * α)|)) ≤
      Real.exp (y * α + t * α ^ 2) * (1 + gaussianSaddleModelError B t) := by
  have he : (fun w => gaussDensity t (w - y) * Real.exp (w * α) *
      Real.exp (B * |w - (y + 2 * t * α)|)) = fun w =>
      gaussDensity t (w - y) * Real.exp (w * α) +
        gaussDensity t (w - y) * Real.exp (w * α) *
          (Real.exp (B * |w - (y + 2 * t * α)|) - 1) := by
    funext w
    ring
  rw [he, integral_add (integrable_gaussDensity_sub_mul_rexp ht y α)
    (integrable_modelError ht y α (y + 2 * t * α) B hB), integral_gaussDensity_sub_mul_rexp ht]
  have hb := integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le_scaled ht y α
    hB (Real.sqrt_pos.mpr ht)
  unfold gaussianSaddleModelError
  nlinarith only [hb]

/-- The norm mass of the model window is at most the saddle mass times `1 + error`. -/
theorem gaussian_saddle_window_mass_le {F : ℝ → ℂ} (hF : Continuous F)
    {B t α y N b W : ℝ} (ht : 0 < t) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hsource : ∀ w ∈ Ioc b W, ‖F w‖ ≤
      N * Real.exp ((w - (y + 2 * t * α)) * α) * Real.exp (B * |w - (y + 2 * t * α)|)) :
    (∫ w in Ioc b W, gaussDensity t (w - y) * ‖F w‖) ≤
      N * Real.exp (-(t * α ^ 2)) * (1 + gaussianSaddleModelError B t) := by
  have hgc := continuous_gaussDensity t
  have hint := integrable_gaussian_saddle_envelope (α := α) (y := y) ht hB
  have hsplit : ∀ w : ℝ, gaussDensity t (w - y) *
      (N * Real.exp ((w - (y + 2 * t * α)) * α) * Real.exp (B * |w - (y + 2 * t * α)|)) =
        N * Real.exp (-((y + 2 * t * α) * α)) *
          (gaussDensity t (w - y) * Real.exp (w * α) * Real.exp (B * |w - (y + 2 * t * α)|)) := by
    intro w
    rw [show (w - (y + 2 * t * α)) * α = -((y + 2 * t * α) * α) + w * α by ring,
      Real.exp_add]
    ring
  calc
    _ ≤ ∫ w in Ioc b W, N * Real.exp (-((y + 2 * t * α) * α)) *
        (gaussDensity t (w - y) * Real.exp (w * α) * Real.exp (B * |w - (y + 2 * t * α)|)) := by
      refine setIntegral_mono_on ?_ (hint.const_mul _).integrableOn measurableSet_Ioc ?_
      · exact (by fun_prop : Continuous fun w => gaussDensity t (w - y) * ‖F w‖).integrableOn_Ioc
      · intro w hw
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left (hsource w hw) (gaussDensity_pos ht _).le
    _ ≤ ∫ w, N * Real.exp (-((y + 2 * t * α) * α)) *
        (gaussDensity t (w - y) * Real.exp (w * α) * Real.exp (B * |w - (y + 2 * t * α)|)) := by
      exact setIntegral_le_integral (hint.const_mul _)
        (Eventually.of_forall fun w => by
          have hg := (gaussDensity_pos ht (w - y)).le
          positivity)
    _ ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
        (Real.exp (y * α + t * α ^ 2) * (1 + gaussianSaddleModelError B t)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_gaussian_saddle_envelope_le ht hB) (by positivity)
    _ = _ := by
      rw [← mul_assoc, mul_assoc N, ← Real.exp_add]
      congr 2
      ring

/-- Optimizing the Chernoff parameter gives the exact squared-distance exponent. -/
theorem gaussian_saddle_lower_tail_le {t α y N b : ℝ} (ht : 0 < t)
    (hN : 0 ≤ N) (hb : b ≤ y + 2 * t * α) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        (∫ w in Iic b, gaussDensity t (w - y) * Real.exp (w * α)) ≤
      N * Real.exp (-(t * α ^ 2)) * Real.exp (-((y + 2 * t * α - b) ^ 2 / (4 * t))) := by
  let lam := (y + 2 * t * α - b) / (2 * t)
  have hlam : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hb) (by positivity)
  have hh := setIntegral_Iic_gaussDensity_sub_mul_rexp_le ht y α b lam hlam
  calc
    _ ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
        Real.exp (lam * b + y * (α - lam) + t * (α - lam) ^ 2) := by gcongr
    _ = _ := by
      rw [mul_assoc N, ← Real.exp_add, mul_assoc N, ← Real.exp_add]
      congr 2
      dsimp only [lam]
      field_simp
      ring

/-- The same squared-distance gain holds for a source bounded by the exponential model. -/
theorem gaussian_saddle_lower_source_mass_le {F : ℝ → ℂ} (hF : Continuous F)
    {t α y N C b : ℝ} (ht : 0 < t) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hb : b ≤ y + 2 * t * α)
    (hsource : ∀ w ∈ Ioc 0 b, ‖F w‖ ≤ C * N * Real.exp ((w - (y + 2 * t * α)) * α)) :
    (∫ w in Ioc 0 b, gaussDensity t (w - y) * ‖F w‖) ≤
      C * (N * Real.exp (-(t * α ^ 2)) * Real.exp (-((y + 2 * t * α - b) ^ 2 / (4 * t)))) := by
  have hgc := continuous_gaussDensity t
  have hint := integrable_gaussDensity_sub_mul_rexp ht y α
  have hsplit : ∀ w : ℝ,
      gaussDensity t (w - y) * (C * N * Real.exp ((w - (y + 2 * t * α)) * α)) =
        C * (N * Real.exp (-((y + 2 * t * α) * α))) *
          (gaussDensity t (w - y) * Real.exp (w * α)) := by
    intro w
    rw [show (w - (y + 2 * t * α)) * α = -((y + 2 * t * α) * α) + w * α by ring,
      Real.exp_add]
    ring
  calc
    _ ≤ ∫ w in Ioc 0 b, C * (N * Real.exp (-((y + 2 * t * α) * α))) *
        (gaussDensity t (w - y) * Real.exp (w * α)) := by
      refine setIntegral_mono_on ?_ (hint.const_mul _).integrableOn measurableSet_Ioc ?_
      · exact (by fun_prop : Continuous fun w => gaussDensity t (w - y) * ‖F w‖).integrableOn_Ioc
      · intro w hw
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left (hsource w hw) (gaussDensity_pos ht _).le
    _ ≤ ∫ w in Iic b, C * (N * Real.exp (-((y + 2 * t * α) * α))) *
        (gaussDensity t (w - y) * Real.exp (w * α)) := by
      refine setIntegral_mono_set (hint.const_mul _).integrableOn
        (Eventually.of_forall fun w => ?_) (Eventually.of_forall fun w hw => hw.2)
      have hg := gaussDensity_sub_mul_rexp_nonneg ht y α w
      positivity
    _ ≤ _ := by
      rw [integral_const_mul, mul_assoc C]
      exact mul_le_mul_of_nonneg_left (gaussian_saddle_lower_tail_le ht hN hb) hC

/-- The lower endpoint carries its Gaussian distance from the saddle exactly. -/
theorem gaussian_saddle_lower_endpoint_le {F : ℝ → ℂ} {t α y N C b : ℝ}
    (ht : 0 < t)
    (hsource : ‖F b‖ ≤ C * N * Real.exp ((b - (y + 2 * t * α)) * α)) :
    gaussDensity t (b - y) * ‖F b‖ ≤
      C * (N * Real.exp (-(t * α ^ 2))) * gaussDensity t (b - (y + 2 * t * α)) := by
  calc
    _ ≤ gaussDensity t (b - y) * (C * N * Real.exp ((b - (y + 2 * t * α)) * α)) :=
      mul_le_mul_of_nonneg_left hsource (gaussDensity_pos ht _).le
    _ = C * N * (gaussDensity t (b - y) * Real.exp ((b - (y + 2 * t * α)) * α)) := by ring
    _ = _ := by rw [gaussDensity_tilt_scale ht]; ring

/-- The slope weight is bounded on the lower source interval. -/
theorem gaussian_lower_interval_slope_mass_le {F : ℝ → ℂ} (hF : Continuous F)
    {t b y : ℝ} (ht : 0 < t) (a : ℂ) :
    (∫ w in Ioc 0 b, (|(w - y) / (2 * t)| + ‖a‖) * gaussDensity t (w - y) * ‖F w‖) ≤
      ((b + |y|) / (2 * t) + ‖a‖) * (∫ w in Ioc 0 b, gaussDensity t (w - y) * ‖F w‖) := by
  have hgc := continuous_gaussDensity t
  rw [← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
  · exact (by fun_prop : Continuous fun w =>
      (|(w - y) / (2 * t)| + ‖a‖) * gaussDensity t (w - y) * ‖F w‖).integrableOn_Ioc
  · exact (by fun_prop : Continuous fun w =>
      ((b + |y|) / (2 * t) + ‖a‖) * (gaussDensity t (w - y) * ‖F w‖)).integrableOn_Ioc
  · intro w hw
    have hab : |w - y| ≤ b + |y| := abs_le.mpr
      ⟨by linarith only [hw.1, hw.2, le_abs_self y],
        by linarith only [hw.2, neg_abs_le y]⟩
    have hweight : |(w - y) / (2 * t)| + ‖a‖ ≤ (b + |y|) / (2 * t) + ‖a‖ := by
      rw [abs_div, abs_of_pos (show 0 < 2 * t by positivity)]
      gcongr
    have hm := mul_le_mul_of_nonneg_right hweight
      (mul_nonneg (gaussDensity_pos ht (w - y)).le (norm_nonneg (F w)))
    simpa only [mul_assoc] using hm

/-- Reflection changes the Gaussian by the exact factor `exp(-wy/t)`. -/
theorem gaussDensity_add_eq_reflected {t : ℝ} (ht : 0 < t) (w y : ℝ) :
    gaussDensity t (w + y) = Real.exp (-(w * y / t)) * gaussDensity t (w - y) := by
  have he : -((w + y) ^ 2 / (4 * t)) = -(w * y / t) + -((w - y) ^ 2 / (4 * t)) := by
    field_simp
    ring
  unfold gaussDensity
  rw [he, Real.exp_add]
  ring

theorem gaussDensity_add_le_of_lower_bound {t b w y : ℝ} (ht : 0 < t)
    (hy : 0 ≤ y) (hw : b ≤ w) :
    gaussDensity t (w + y) ≤ Real.exp (-(b * y / t)) * gaussDensity t (w - y) := by
  rw [gaussDensity_add_eq_reflected ht]
  have hg := (gaussDensity_pos ht (w - y)).le
  gcongr

/-- Reflection suppresses the entire middle window uniformly. -/
theorem opposite_window_mass_le {F : ℝ → ℂ} (hF : Continuous F)
    {t b W y : ℝ} (ht : 0 < t) (hy : 0 ≤ y) :
    (∫ w in Ioc b W, gaussDensity t (w + y) * ‖F w‖) ≤
      Real.exp (-(b * y / t)) * (∫ w in Ioc b W, gaussDensity t (w - y) * ‖F w‖) := by
  have hgc := continuous_gaussDensity t
  rw [← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
  · exact (by fun_prop : Continuous fun w => gaussDensity t (w + y) * ‖F w‖).integrableOn_Ioc
  · exact (by fun_prop : Continuous fun w =>
      Real.exp (-(b * y / t)) * (gaussDensity t (w - y) * ‖F w‖)).integrableOn_Ioc
  · intro w hw
    have hm := mul_le_mul_of_nonneg_right
      (gaussDensity_add_le_of_lower_bound ht hy hw.1.le) (norm_nonneg (F w))
    simpa only [mul_assoc] using hm

/-- A source controlled by an exponential has a suppressed opposite lower interval. -/
theorem opposite_lower_interval_mass_le {F : ℝ → ℂ} (hF : Continuous F)
    {t α y N C b : ℝ} (ht : 0 < t) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hsource : ∀ w ∈ Ioc 0 b,
      ‖F w‖ ≤ C * N * Real.exp ((w - (y + 2 * t * α)) * α)) :
    (∫ w in Ioc 0 b, gaussDensity t (w + y) * ‖F w‖) ≤
      C * (N * Real.exp (-(t * α ^ 2))) * Real.exp (-(2 * α * y)) := by
  have hgc := continuous_gaussDensity t
  have hint := integrable_gaussDensity_sub_mul_rexp ht (-y) α
  have hsplit : ∀ w : ℝ,
      gaussDensity t (w + y) * (C * N * Real.exp ((w - (y + 2 * t * α)) * α)) =
        C * N * Real.exp (-((y + 2 * t * α) * α)) *
          (gaussDensity t (w - -y) * Real.exp (w * α)) := by
    intro w
    rw [show (w - (y + 2 * t * α)) * α = -((y + 2 * t * α) * α) + w * α by ring,
      Real.exp_add, sub_neg_eq_add]
    ring
  calc
    _ ≤ ∫ w in Ioc 0 b, C * N * Real.exp (-((y + 2 * t * α) * α)) *
        (gaussDensity t (w - -y) * Real.exp (w * α)) := by
      refine setIntegral_mono_on ?_ (hint.const_mul _).integrableOn measurableSet_Ioc ?_
      · exact (by fun_prop : Continuous fun w => gaussDensity t (w + y) * ‖F w‖).integrableOn_Ioc
      · intro w hw
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left (hsource w hw) (gaussDensity_pos ht _).le
    _ ≤ ∫ w, C * N * Real.exp (-((y + 2 * t * α) * α)) *
        (gaussDensity t (w - -y) * Real.exp (w * α)) := by
      exact setIntegral_le_integral (hint.const_mul _)
        (Eventually.of_forall fun w => by
          have hg := gaussDensity_sub_mul_rexp_nonneg ht (-y) α w
          positivity)
    _ = _ := by
      rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp ht]
      rw [mul_assoc (C * N), ← Real.exp_add]
      have he : -((y + 2 * t * α) * α) + -y * α + t * α ^ 2 =
          -(t * α ^ 2) + -(2 * α * y) := by ring
      rw [show -((y + 2 * t * α) * α) + (-y * α + t * α ^ 2) =
        -(t * α ^ 2) + -(2 * α * y) by linarith only [he], Real.exp_add]
      ring

/-- Splitting the half transform bounds its norm by the three corresponding source masses. -/
theorem norm_halfGaussTransform_le_three_masses {F : ℝ → ℂ} (hF : Continuous F)
    {t y b W : ℝ} (ht : 0 < t) (hb : 0 ≤ b) (hbW : b ≤ W)
    (hint : Integrable (fun w => Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖)) :
    ‖halfGaussTransform t F y‖ ≤
      (∫ w in Ioc 0 b, gaussDensity t (w - y) * ‖F w‖) +
      (∫ w in Ioc b W, gaussDensity t (w - y) * ‖F w‖) +
      (∫ w in Ioi W, gaussDensity t (w - y) * ‖F w‖) := by
  have hn : ∀ S : Set ℝ,
      ‖∫ w in S, (gaussDensity t (w - y) : ℂ) * F w‖ ≤
        ∫ w in S, gaussDensity t (w - y) * ‖F w‖ := by
    intro S
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext w
    exact norm_gauss_mul t y w ht _
  unfold halfGaussTransform
  rw [setIntegral_Ioi_split hb hbW (integrable_gaussDensity_sub_mul ht hF hint y).integrableOn]
  calc
    _ ≤ ‖∫ w in Ioc 0 b, (gaussDensity t (w - y) : ℂ) * F w‖ +
        ‖∫ w in Ioc b W, (gaussDensity t (w - y) : ℂ) * F w‖ +
        ‖∫ w in Ioi W, (gaussDensity t (w - y) : ℂ) * F w‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (hn _) (hn _)) (hn _)

#print axioms gaussian_saddle_lower_tail_le
#print axioms opposite_lower_interval_mass_le

end

end GaloisForLFunctions.ZeroConfigurationGeometry
