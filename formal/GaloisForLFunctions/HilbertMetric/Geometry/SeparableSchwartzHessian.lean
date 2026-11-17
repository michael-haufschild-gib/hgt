import GaloisForLFunctions.RHTower.ReversalSupBound
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic
import GaloisForLFunctions.HilbertMetric.Geometry.TrigonometricHessianSeed
import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzProducts

/-!
# A Schwartz potential with nowhere-scalar Hessian

Multiply the periodic trigonometric seed by the reciprocal cosh in each
coordinate, at scale `1/1024`. Every derivative of either damping factor
is that factor times a polynomial in a bounded hyperbolic tangent. This
gives joint Schwartz decay. The first two logarithmic derivatives are
small enough to preserve the seed's trace-free Hessian gap everywhere.
-/

namespace GaloisForLFunctions.HilbertMetric.Geometry.SeparableHessian
open Real TrigonometricHessian
open scoped ContDiff
noncomputable section

def scale : ℝ := 1 / 1024

def axisWeight (t : ℝ) : ℝ := (cosh (scale * t))⁻¹

def axisLogSlope (t : ℝ) : ℝ := -scale * tanh (scale * t)

def axisRelativeSecond (t : ℝ) : ℝ := scale ^ 2 * (2 * tanh (scale * t) ^ 2 - 1)

theorem axisWeight_pos (t : ℝ) : 0 < axisWeight t := inv_pos.mpr (cosh_pos _)

theorem axisWeight_hasDerivAt (t : ℝ) :
    HasDerivAt axisWeight (axisWeight t * axisLogSlope t) t := by
  have h := ((hasDerivAt_cosh (scale * t)).comp t
    ((hasDerivAt_id t).const_mul scale)).inv (cosh_pos _).ne'
  change HasDerivAt axisWeight (-(sinh (scale * t) * (scale * 1)) / cosh (scale * t) ^ 2) t at h
  have he : -(sinh (scale * t) * (scale * 1)) / cosh (scale * t) ^ 2 =
      axisWeight t * axisLogSlope t := by
    rw [axisWeight, axisLogSlope, tanh_eq_sinh_div_cosh]
    field_simp
  rwa [he] at h

private theorem axisLogSlope_hasDerivAt (t : ℝ) :
    HasDerivAt axisLogSlope (-scale ^ 2 * (cosh (scale * t))⁻¹ ^ 2) t := by
  have h : HasDerivAt axisLogSlope
      (-scale * ((cosh (scale * t))⁻¹ ^ 2 * (scale * 1))) t :=
    ((_root_.RHTower.hasDerivAt_tanh (scale * t)).comp t
      ((hasDerivAt_id t).const_mul scale)).const_mul (-scale)
  have he : -scale * ((cosh (scale * t))⁻¹ ^ 2 * (scale * 1)) =
      -scale ^ 2 * (cosh (scale * t))⁻¹ ^ 2 := by ring
  rwa [he] at h

theorem axisWeight_second_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => axisWeight s * axisLogSlope s)
      (axisWeight t * axisRelativeSecond t) t := by
  have h : HasDerivAt (fun s => axisWeight s * axisLogSlope s)
      (axisWeight t * axisLogSlope t * axisLogSlope t +
        axisWeight t * (-scale ^ 2 * (cosh (scale * t))⁻¹ ^ 2)) t :=
    (axisWeight_hasDerivAt t).mul (axisLogSlope_hasDerivAt t)
  have hid : (cosh (scale * t))⁻¹ ^ 2 = 1 - tanh (scale * t) ^ 2 := by
    rw [tanh_eq_sinh_div_cosh]
    field_simp [(cosh_pos (scale * t)).ne']
    nlinarith only [cosh_sq_sub_sinh_sq (scale * t)]
  have he : axisWeight t * axisLogSlope t * axisLogSlope t +
      axisWeight t * (-scale ^ 2 * (cosh (scale * t))⁻¹ ^ 2) =
      axisWeight t * axisRelativeSecond t := by
    rw [hid]
    unfold axisLogSlope axisRelativeSecond
    ring
  rwa [he] at h

theorem axisLogSlope_abs_le (t : ℝ) : |axisLogSlope t| ≤ scale := by
  rw [axisLogSlope, abs_mul, abs_neg, abs_of_pos (by norm_num [scale] : 0 < scale)]
  exact mul_le_of_le_one_right (by norm_num [scale]) (abs_tanh_lt_one _).le

theorem axisRelativeSecond_abs_le (t : ℝ) : |axisRelativeSecond t| ≤ scale ^ 2 := by
  rw [axisRelativeSecond, abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_of_le_one_right (sq_nonneg _)
  apply abs_le.mpr
  constructor
  · nlinarith only [sq_nonneg (tanh (scale * t))]
  · nlinarith only [tanh_sq_lt_one (scale * t)]

/-- Reciprocal cosh is bounded by an explicit decaying exponential. -/
theorem axisWeight_exp_bound (t : ℝ) :
    axisWeight t ≤ 2 * exp (-(scale * |t|)) := by
  have hscale : 0 < scale := by norm_num [scale]
  have he : cosh (scale * t) = cosh (scale * |t|) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, mul_neg, cosh_neg]
  have hc : exp (scale * |t|) / 2 ≤ cosh (scale * t) := by
    rw [he, cosh_eq]
    linarith only [exp_pos (-(scale * |t|))]
  have hmul := mul_le_mul_of_nonneg_right hc (exp_nonneg (-(scale * |t|)))
  have hcancel : exp (scale * |t|) * exp (-(scale * |t|)) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  have hprod : 1 ≤ (2 * exp (-(scale * |t|))) * cosh (scale * t) := by
    nlinarith only [hmul, hcancel]
  change (cosh (scale * t))⁻¹ ≤ _
  simpa only [one_div] using (div_le_iff₀ (cosh_pos (scale * t))).mpr hprod

/-- Every polynomial weight is absorbed by the reciprocal-cosh decay. -/
theorem axisWeight_power_bound (k : ℕ) (t : ℝ) :
    |t| ^ k * axisWeight t ≤ 2 * (2 / scale) ^ k * (k.factorial : ℝ) := by
  have hscale : 0 < scale := by norm_num [scale]
  have h := _root_.RHTower.pow_abs_mul_exp_neg_le hscale k t
  have he : exp (-(scale / 2 * |t|)) ≤ 1 :=
    exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have htail := mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ (2 / scale) ^ k * (k.factorial : ℝ))
  have hw := mul_le_mul_of_nonneg_left (axisWeight_exp_bound t) (pow_nonneg (abs_nonneg t) k)
  nlinarith only [hw, h, htail]

/-- Every derivative is the original positive decay factor times a polynomial in a bounded variable. -/
theorem axisWeight_iteratedDeriv_polynomial (n : ℕ) :
    ∃ P : Polynomial ℝ, ∀ t : ℝ,
      iteratedDeriv n axisWeight t = axisWeight t * P.eval (tanh (scale * t)) := by
  induction n with
  | zero =>
      refine ⟨1, fun t => ?_⟩
      simp only [iteratedDeriv_zero, Polynomial.eval_one, mul_one]
  | succ n ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨Polynomial.C scale * ((1 - Polynomial.X ^ 2) * P.derivative - Polynomial.X * P), ?_⟩
      intro t
      have ht : HasDerivAt (fun s : ℝ => tanh (scale * s))
          ((cosh (scale * t))⁻¹ ^ 2 * (scale * 1)) t :=
        (_root_.RHTower.hasDerivAt_tanh (scale * t)).comp t
          ((hasDerivAt_id t).const_mul scale)
      have hp : HasDerivAt (fun s : ℝ => P.eval s)
          (P.derivative.eval (tanh (scale * t))) (tanh (scale * t)) :=
        P.hasDerivAt (tanh (scale * t))
      have hc := hp.comp t ht
      change HasDerivAt (fun s : ℝ => P.eval (tanh (scale * s)))
        (P.derivative.eval (tanh (scale * t)) *
          ((cosh (scale * t))⁻¹ ^ 2 * (scale * 1))) t at hc
      have hd : HasDerivAt (fun s => axisWeight s * P.eval (tanh (scale * s)))
          (axisWeight t * axisLogSlope t * P.eval (tanh (scale * t)) +
            axisWeight t * (P.derivative.eval (tanh (scale * t)) *
              ((cosh (scale * t))⁻¹ ^ 2 * (scale * 1)))) t :=
        (axisWeight_hasDerivAt t).mul hc
      have hid : (cosh (scale * t))⁻¹ ^ 2 = 1 - tanh (scale * t) ^ 2 := by
        rw [tanh_eq_sinh_div_cosh]
        field_simp [(cosh_pos (scale * t)).ne']
        nlinarith only [cosh_sq_sub_sinh_sq (scale * t)]
      rw [iteratedDeriv_succ, show iteratedDeriv n axisWeight =
        (fun t => axisWeight t * P.eval (tanh (scale * t))) from funext hP, hd.deriv]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hid, axisLogSlope]
      ring

/-- Reciprocal-cosh damping is an actual Schwartz function, including all derivative orders. -/
def axisSchwartz : SchwartzMap ℝ ℝ where
  toFun := axisWeight
  smooth' := by
    have hc : ContDiff ℝ (∞ : ℕ∞ω) (fun t : ℝ => cosh (scale * t)) :=
      contDiff_cosh.comp (contDiff_const.mul contDiff_id)
    exact hc.inv (fun t => (cosh_pos (scale * t)).ne')
  decay' k n := by
    have hscale : 0 < scale := by norm_num [scale]
    obtain ⟨P, hP⟩ := axisWeight_iteratedDeriv_polynomial n
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      P.continuous.continuousOn
    refine ⟨(2 * (2 / scale) ^ k * (k.factorial : ℝ)) * max C 0, fun t => ?_⟩
    have hp : |P.eval (tanh (scale * t))| ≤ max C 0 :=
      (hC _ ⟨(neg_one_lt_tanh _).le, (tanh_lt_one _).le⟩).trans (le_max_left _ _)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hP, norm_mul]
    simp only [Real.norm_eq_abs, abs_of_pos (axisWeight_pos t)]
    have h := mul_le_mul (axisWeight_power_bound k t) hp (abs_nonneg _)
      (by positivity : 0 ≤ 2 * (2 / scale) ^ k * (k.factorial : ℝ))
    nlinarith only [h]

@[simp] theorem axisSchwartz_apply (t : ℝ) : axisSchwartz t = axisWeight t := rfl

/-- A separably damped periodic potential. -/
def dampedSeed (x y : ℝ) : ℝ := axisWeight x * axisWeight y * seed x y

private theorem seedAxis_hasTemperateGrowth : Function.HasTemperateGrowth seedAxis := by
  have h := SchwartzProducts.sin_hasTemperateGrowth
  exact (h.pow 4).add ((Function.HasTemperateGrowth.const (3 : ℝ)).mul (h.pow 2))

private def axisSeedSchwartz : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ seedAxis axisSchwartz

private def axisSinSchwartz : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ sin axisSchwartz

/-- The damped trigonometric potential is Schwartz in both variables jointly. -/
def dampedSeedSchwartz : SchwartzMap (ℝ × ℝ) ℝ :=
  SchwartzProducts.externalProduct axisSeedSchwartz axisSchwartz -
    SchwartzProducts.externalProduct axisSchwartz axisSeedSchwartz +
    SchwartzProducts.externalProduct axisSinSchwartz axisSinSchwartz

@[simp] theorem dampedSeedSchwartz_apply (p : ℝ × ℝ) :
    dampedSeedSchwartz p = dampedSeed p.1 p.2 := by
  change SchwartzProducts.externalProduct axisSeedSchwartz axisSchwartz p -
    SchwartzProducts.externalProduct axisSchwartz axisSeedSchwartz p +
    SchwartzProducts.externalProduct axisSinSchwartz axisSinSchwartz p = _
  simp only [SchwartzProducts.externalProduct_apply, axisSeedSchwartz, axisSinSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply seedAxis_hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply SchwartzProducts.sin_hasTemperateGrowth,
    smul_eq_mul, axisSchwartz_apply]
  unfold dampedSeed seed
  ring

theorem dampedSeed_contDiff : ContDiff ℝ (∞ : ℕ∞ω) (fun p : ℝ × ℝ => dampedSeed p.1 p.2) := by
  have he : (dampedSeedSchwartz : (ℝ × ℝ) → ℝ) = fun p => dampedSeed p.1 p.2 :=
    funext dampedSeedSchwartz_apply
  rw [← he]
  exact dampedSeedSchwartz.smooth'

def seedSlopeX (x y : ℝ) : ℝ := axisSlope x + cos x * sin y

def seedSlopeY (x y : ℝ) : ℝ := -axisSlope y + sin x * cos y

def errorAnisotropy (x y : ℝ) : ℝ :=
  (axisRelativeSecond x - axisRelativeSecond y) * seed x y +
    2 * axisLogSlope x * seedSlopeX x y - 2 * axisLogSlope y * seedSlopeY x y

def errorShear (x y : ℝ) : ℝ :=
  2 * axisLogSlope x * axisLogSlope y * seed x y +
    2 * axisLogSlope x * seedSlopeY x y + 2 * axisLogSlope y * seedSlopeX x y

theorem dampedSeed_x_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t => dampedSeed t y)
      (axisWeight x * axisWeight y * (axisLogSlope x * seed x y + seedSlopeX x y)) x := by
  have h : HasDerivAt (fun t => dampedSeed t y)
      (axisWeight x * axisLogSlope x * axisWeight y * seed x y +
        axisWeight x * axisWeight y * (axisSlope x + cos x * sin y)) x :=
    ((axisWeight_hasDerivAt x).mul_const (axisWeight y)).mul (seed_x_hasDerivAt x y)
  have he : axisWeight x * axisLogSlope x * axisWeight y * seed x y +
      axisWeight x * axisWeight y * (axisSlope x + cos x * sin y) =
      axisWeight x * axisWeight y * (axisLogSlope x * seed x y + seedSlopeX x y) := by
    unfold seedSlopeX
    ring
  rwa [he] at h

theorem dampedSeed_y_hasDerivAt (x y : ℝ) :
    HasDerivAt (dampedSeed x)
      (axisWeight x * axisWeight y * (axisLogSlope y * seed x y + seedSlopeY x y)) y := by
  have h : HasDerivAt (dampedSeed x)
      (axisWeight x * (axisWeight y * axisLogSlope y) * seed x y +
        axisWeight x * axisWeight y * (-axisSlope y + sin x * cos y)) y :=
    ((axisWeight_hasDerivAt y).const_mul (axisWeight x)).mul (seed_y_hasDerivAt x y)
  have he : axisWeight x * (axisWeight y * axisLogSlope y) * seed x y +
      axisWeight x * axisWeight y * (-axisSlope y + sin x * cos y) =
      axisWeight x * axisWeight y * (axisLogSlope y * seed x y + seedSlopeY x y) := by
    unfold seedSlopeY
    ring
  rwa [he] at h

private theorem seedSlopeX_x_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t => seedSlopeX t y) (6 - 16 * sin x ^ 4 - sin x * sin y) x := by
  have h : HasDerivAt (fun t => seedSlopeX t y)
      ((6 - 16 * sin x ^ 4) + (-sin x) * sin y) x :=
    (axisSlope_hasDerivAt x).add ((hasDerivAt_cos x).mul_const (sin y))
  convert h using 1
  ring

private theorem seedSlopeY_y_hasDerivAt (x y : ℝ) :
    HasDerivAt (seedSlopeY x) (-(6 - 16 * sin y ^ 4) - sin x * sin y) y := by
  have h : HasDerivAt (seedSlopeY x)
      (-(6 - 16 * sin y ^ 4) + sin x * (-sin y)) y :=
    (axisSlope_hasDerivAt y).neg.add ((hasDerivAt_cos y).const_mul (sin x))
  convert h using 1
  ring

private theorem seedSlopeX_y_hasDerivAt (x y : ℝ) :
    HasDerivAt (seedSlopeX x) (cos x * cos y) y :=
  ((hasDerivAt_sin y).const_mul (cos x)).const_add (axisSlope x)

/-- The actual Hessian factors into the positive damping and a controlled trace-free perturbation. -/
theorem dampedSeed_hessian (x y : ℝ) :
    deriv (deriv (fun t => dampedSeed t y)) x = axisWeight x * axisWeight y *
        (axisRelativeSecond x * seed x y + 2 * axisLogSlope x * seedSlopeX x y +
          (6 - 16 * sin x ^ 4 - sin x * sin y)) ∧
      deriv (deriv (dampedSeed x)) y = axisWeight x * axisWeight y *
        (axisRelativeSecond y * seed x y + 2 * axisLogSlope y * seedSlopeY x y +
          (-(6 - 16 * sin y ^ 4) - sin x * sin y)) ∧
      deriv (fun t => deriv (fun s => dampedSeed s t) x) y =
        axisWeight x * axisWeight y *
          (axisLogSlope x * axisLogSlope y * seed x y + axisLogSlope x * seedSlopeY x y +
            axisLogSlope y * seedSlopeX x y + cos x * cos y) := by
  have hx (y : ℝ) : deriv (fun t => dampedSeed t y) = fun t =>
      (axisWeight t * axisLogSlope t) * axisWeight y * seed t y +
        axisWeight t * axisWeight y * seedSlopeX t y := by
    funext t
    rw [(dampedSeed_x_hasDerivAt t y).deriv]
    ring
  have hy : deriv (dampedSeed x) = fun t =>
      axisWeight x * (axisWeight t * axisLogSlope t) * seed x t +
        axisWeight x * axisWeight t * seedSlopeY x t := by
    funext t
    rw [(dampedSeed_y_hasDerivAt x t).deriv]
    ring
  constructor
  · rw [hx]
    have h : HasDerivAt (fun t =>
        (axisWeight t * axisLogSlope t) * axisWeight y * seed t y +
          axisWeight t * axisWeight y * seedSlopeX t y) _ x :=
      (((axisWeight_second_hasDerivAt x).mul_const (axisWeight y)).mul
      (seed_x_hasDerivAt x y)).add
      (((axisWeight_hasDerivAt x).mul_const (axisWeight y)).mul
        (seedSlopeX_x_hasDerivAt x y))
    rw [h.deriv]
    unfold seedSlopeX
    ring
  constructor
  · rw [hy]
    have h : HasDerivAt (fun t =>
        axisWeight x * (axisWeight t * axisLogSlope t) * seed x t +
          axisWeight x * axisWeight t * seedSlopeY x t) _ y :=
      (((axisWeight_second_hasDerivAt y).const_mul (axisWeight x)).mul
      (seed_y_hasDerivAt x y)).add
      (((axisWeight_hasDerivAt y).const_mul (axisWeight x)).mul
        (seedSlopeY_y_hasDerivAt x y))
    rw [h.deriv]
    unfold seedSlopeY
    ring
  · simp only [hx]
    have h : HasDerivAt (fun t =>
        (axisWeight x * axisLogSlope x) * axisWeight t * seed x t +
          axisWeight x * axisWeight t * seedSlopeX x t) _ y :=
      (((axisWeight_hasDerivAt y).const_mul (axisWeight x * axisLogSlope x)).mul
      (seed_y_hasDerivAt x y)).add
      (((axisWeight_hasDerivAt y).const_mul (axisWeight x)).mul
        (seedSlopeX_y_hasDerivAt x y))
    rw [h.deriv]
    unfold seedSlopeY
    ring

theorem dampedSeed_hessian_coordinates (x y : ℝ) :
    deriv (deriv (fun t => dampedSeed t y)) x - deriv (deriv (dampedSeed x)) y =
        axisWeight x * axisWeight y * (anisotropy x y + errorAnisotropy x y) ∧
      2 * deriv (fun t => deriv (fun s => dampedSeed s t) x) y =
        axisWeight x * axisWeight y * (shear x y + errorShear x y) := by
  obtain ⟨hxx, hyy, hxy⟩ := dampedSeed_hessian x y
  rw [hxx, hyy, hxy]
  constructor
  · unfold anisotropy errorAnisotropy
    ring
  · unfold shear errorShear
    ring

private theorem seedAxis_bounds (t : ℝ) : 0 ≤ seedAxis t ∧ seedAxis t ≤ 4 := by
  have hs : sin t ^ 2 ≤ 1 := by nlinarith only [sin_sq_add_cos_sq t, sq_nonneg (cos t)]
  have hp := mul_le_mul hs hs (sq_nonneg (sin t)) (by norm_num : (0 : ℝ) ≤ 1)
  constructor
  · unfold seedAxis
    positivity
  · unfold seedAxis
    nlinarith only [hs, hp]

private theorem axisSlope_abs_le (t : ℝ) : |axisSlope t| ≤ 10 := by
  have hs3 : |sin t| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_sin_le_one _) 
  have hsc : |sin t| * |cos t| ≤ 1 :=
    mul_le_one₀ (abs_sin_le_one _) (abs_nonneg _) (abs_cos_le_one _)
  have h3c : |sin t| ^ 3 * |cos t| ≤ 1 :=
    mul_le_one₀ hs3 (abs_nonneg _) (abs_cos_le_one _)
  have ht := abs_add_le (4 * sin t ^ 3 * cos t) (6 * sin t * cos t)
  rw [axisSlope]
  norm_num [abs_mul, abs_pow] at ht
  nlinarith only [ht, hsc, h3c]

theorem seed_abs_le (x y : ℝ) : |seed x y| ≤ 5 := by
  have hx := seedAxis_bounds x
  have hy := seedAxis_bounds y
  have ha : |seedAxis x - seedAxis y| ≤ 4 := abs_le.mpr
    ⟨by linarith only [hx.1, hy.2], by linarith only [hx.2, hy.1]⟩
  have hsc : |sin x * sin y| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (abs_sin_le_one _) (abs_nonneg _) (abs_sin_le_one _)
  exact (abs_add_le _ _).trans (by linarith only [ha, hsc])

theorem seedSlopeX_abs_le (x y : ℝ) : |seedSlopeX x y| ≤ 11 := by
  have hsc : |cos x * sin y| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (abs_cos_le_one _) (abs_nonneg _) (abs_sin_le_one _)
  exact (abs_add_le _ _).trans (by linarith only [axisSlope_abs_le x, hsc])

theorem seedSlopeY_abs_le (x y : ℝ) : |seedSlopeY x y| ≤ 11 := by
  have hsc : |sin x * cos y| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (abs_sin_le_one _) (abs_nonneg _) (abs_cos_le_one _)
  have h := abs_add_le (-axisSlope y) (sin x * cos y)
  rw [abs_neg] at h
  exact h.trans (by linarith only [axisSlope_abs_le y, hsc])

private theorem double_logSlope_product_bound (x z : ℝ) (hz : |z| ≤ 11) :
    |2 * axisLogSlope x * z| ≤ 22 * scale := by
  have h := mul_le_mul (axisLogSlope_abs_le x) hz (abs_nonneg z)
    (by norm_num [scale] : 0 ≤ scale)
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith only [h]

theorem errorAnisotropy_abs_le (x y : ℝ) :
    |errorAnisotropy x y| ≤ 44 * scale + 10 * scale ^ 2 := by
  have hr : |axisRelativeSecond x - axisRelativeSecond y| ≤ 2 * scale ^ 2 :=
    (abs_sub _ _).trans (by linarith only [axisRelativeSecond_abs_le x, axisRelativeSecond_abs_le y])
  have h0 := mul_le_mul hr (seed_abs_le x y) (abs_nonneg (seed x y)) (by positivity)
  have hx := double_logSlope_product_bound x (seedSlopeX x y) (seedSlopeX_abs_le x y)
  have hy := double_logSlope_product_bound y (seedSlopeY x y) (seedSlopeY_abs_le x y)
  have ht := (abs_sub ((axisRelativeSecond x - axisRelativeSecond y) * seed x y +
    2 * axisLogSlope x * seedSlopeX x y) (2 * axisLogSlope y * seedSlopeY x y)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  rw [← abs_mul] at h0
  change |errorAnisotropy x y| ≤ _ at ht
  linarith only [ht, h0, hx, hy]

theorem errorShear_abs_le (x y : ℝ) :
    |errorShear x y| ≤ 44 * scale + 10 * scale ^ 2 := by
  have hq : |axisLogSlope x * axisLogSlope y| ≤ scale ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (axisLogSlope_abs_le x) (axisLogSlope_abs_le y)
      (abs_nonneg _) (by norm_num [scale])
  have h0 := mul_le_mul hq (seed_abs_le x y) (abs_nonneg (seed x y)) (sq_nonneg scale)
  have h0' : |2 * axisLogSlope x * axisLogSlope y * seed x y| ≤ 10 * scale ^ 2 := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h0 ⊢
    nlinarith only [h0]
  have hx := double_logSlope_product_bound x (seedSlopeY x y) (seedSlopeY_abs_le x y)
  have hy := double_logSlope_product_bound y (seedSlopeX x y) (seedSlopeX_abs_le x y)
  have ht := (abs_add_le (2 * axisLogSlope x * axisLogSlope y * seed x y +
    2 * axisLogSlope x * seedSlopeY x y) (2 * axisLogSlope y * seedSlopeX x y)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  change |errorShear x y| ≤ _ at ht
  linarith only [ht, h0', hx, hy]

/-- Damping leaves a positive quantitative gap after dividing out its positive square. -/
theorem normalized_gap (x y : ℝ) :
    (3 / 128 : ℝ) ≤ (anisotropy x y + errorAnisotropy x y) ^ 2 +
      (shear x y + errorShear x y) ^ 2 := by
  have ha : |errorAnisotropy x y| ≤ 1 / 16 := (errorAnisotropy_abs_le x y).trans (by norm_num [scale])
  have hb : |errorShear x y| ≤ 1 / 16 := (errorShear_abs_le x y).trans (by norm_num [scale])
  have ha2 := mul_le_mul ha ha (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hb2 := mul_le_mul hb hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have h := perturbed_gap_lower_bound x y (errorAnisotropy x y) (errorShear x y)
  nlinarith only [h, ha2, hb2, sq_abs (errorAnisotropy x y), sq_abs (errorShear x y)]

/-- The genuinely decaying potential has no scalar Hessian anywhere in the plane. -/
theorem dampedSeed_hessian_nowhere_scalar (x y : ℝ) :
    ¬ (deriv (deriv (fun t => dampedSeed t y)) x = deriv (deriv (dampedSeed x)) y ∧
      deriv (fun t => deriv (fun s => dampedSeed s t) x) y = 0) := by
  rintro ⟨hd, hm⟩
  obtain ⟨ha, hb⟩ := dampedSeed_hessian_coordinates x y
  rw [hd, sub_self] at ha
  rw [hm, mul_zero] at hb
  have hw : axisWeight x * axisWeight y ≠ 0 :=
    (mul_pos (axisWeight_pos x) (axisWeight_pos y)).ne'
  have hA := (mul_eq_zero.mp ha.symm).resolve_left hw
  have hB := (mul_eq_zero.mp hb.symm).resolve_left hw
  have h := normalized_gap x y
  rw [hA, hB] at h
  norm_num at h

/-- Rapid decay of every derivative is compatible with distinct Hessian eigenvalues everywhere. -/
theorem exists_schwartz_hessian_nowhere_scalar :
    ∃ f : SchwartzMap (ℝ × ℝ) ℝ, ∀ x y : ℝ,
      ¬ (deriv (deriv (fun t => f (t, y))) x = deriv (deriv (fun t => f (x, t))) y ∧
        deriv (fun t => deriv (fun s => f (s, t)) x) y = 0) := by
  refine ⟨dampedSeedSchwartz, fun x y => ?_⟩
  simp only [dampedSeedSchwartz_apply]
  exact dampedSeed_hessian_nowhere_scalar x y

#print axioms exists_schwartz_hessian_nowhere_scalar
#print axioms axisSchwartz
#print axioms dampedSeedSchwartz
#print axioms dampedSeedSchwartz_apply
#print axioms dampedSeed_contDiff
#print axioms axisWeight_iteratedDeriv_polynomial
#print axioms axisWeight_exp_bound
#print axioms dampedSeed_hessian
#print axioms normalized_gap
#print axioms dampedSeed_hessian_nowhere_scalar
#print axioms axisWeight_hasDerivAt
#print axioms axisWeight_second_hasDerivAt
#print axioms axisLogSlope_abs_le
#print axioms axisRelativeSecond_abs_le
end
end GaloisForLFunctions.HilbertMetric.Geometry.SeparableHessian
