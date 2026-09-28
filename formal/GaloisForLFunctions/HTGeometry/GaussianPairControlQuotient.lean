import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# A positive Gaussian control for relative-source rigidity

For `k_G(x) = [e^{-(x-a)²} + e^{-(x+a)²}]/2` (positive, even) and `u_G = k_G cos(ωx)`
(`|u_G| ≤ k_G`) with `aω = 2π`, the Gaussian integrals give
`F_G(z) = √π e^{-z²/4} cos(az)` and `H_G(z) = e^{-ω²/4} F_G(z) cosh(ωz/2)`.
The quotient `e^{-ω²/4} cosh(ωz/2)` is even, entire, of exponential type `|ω|/2`, bounded on the
imaginary axis, and not constant; `F_G` has the periodic zeros of `cos(az)`. Along the rays
`R(sin δ - i cos δ)` it grows like `sinh(|ω| R |sin δ|/2)`: a linear angular cusp, which the
theta source's sectorial Gamma bound excludes.
-/

open MeasureTheory Complex Real

namespace HTGeometry

noncomputable section

/-- The two-bump Gaussian control source `k_G(x) = [e^{-(x-a)²} + e^{-(x+a)²}]/2`. -/
def gaussPairSource (a x : ℝ) : ℝ := (Real.exp (-(x - a) ^ 2) + Real.exp (-(x + a) ^ 2)) / 2

theorem gaussPairSource_pos (a x : ℝ) : 0 < gaussPairSource a x := by
  unfold gaussPairSource; positivity

theorem gaussPairSource_neg (a x : ℝ) : gaussPairSource a (-x) = gaussPairSource a x := by
  unfold gaussPairSource; ring_nf

/-- The oscillating companion `u_G(x) = k_G(x) cos(ωx)`, with `|u_G| ≤ k_G`. -/
def gaussPairCosSource (a ω x : ℝ) : ℝ := gaussPairSource a x * Real.cos (ω * x)

theorem abs_gaussPairCosSource_le (a ω x : ℝ) :
    |gaussPairCosSource a ω x| ≤ gaussPairSource a x := by
  rw [gaussPairCosSource, abs_mul, abs_of_pos (gaussPairSource_pos a x)]
  exact mul_le_of_le_one_right (gaussPairSource_pos a x).le (Real.abs_cos_le_one _)

/-- `∫ e^{-x² + c x + d} dx = √π e^{d + c²/4}`. -/
theorem integral_cexp_neg_sq_add (c d : ℂ) :
    ∫ x : ℝ, cexp (-(x : ℂ) ^ 2 + c * x + d) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * cexp (d + c ^ 2 / 4) := by
  have h := integral_cexp_quadratic (b := -1) (by simp) c d
  simp only [neg_neg, div_one] at h
  rw [show (fun x : ℝ => cexp (-(x : ℂ) ^ 2 + c * x + d)) =
    fun x : ℝ => cexp (-1 * (x : ℂ) ^ 2 + c * x + d) by funext x; ring_nf, h]
  congr 2; ring

theorem integrable_cexp_neg_sq_add (c d : ℂ) :
    Integrable (fun x : ℝ => cexp (-(x : ℂ) ^ 2 + c * x + d)) := by
  have h := integrable_cexp_quadratic' (b := -1) (by simp) c d
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring_nf

/-- The control transform `F_G(z) = √π e^{-z²/4} cos(az)`. -/
def gaussPairTransform (a : ℝ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (1 / 2 : ℂ) * cexp (-z ^ 2 / 4) * Complex.cos (a * z)

theorem cexp_ofReal_neg_sq (x c : ℝ) :
    ((Real.exp (-(x - c) ^ 2) : ℝ) : ℂ) = cexp (-(x : ℂ) ^ 2 + (2 * c) * x + -(c : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]; congr 1; push_cast; ring

/-- **The Gaussian control transform.** `∫ e^{-izx} k_G(x) dx = √π e^{-z²/4} cos(az)`. -/
theorem integral_cexp_mul_gaussPairSource (a : ℝ) (z : ℂ) :
    ∫ x : ℝ, cexp (-I * z * x) * (gaussPairSource a x : ℂ) = gaussPairTransform a z := by
  have hpt : ∀ x : ℝ, cexp (-I * z * x) * (gaussPairSource a x : ℂ) =
      (1 / 2 : ℂ) * (cexp (-(x : ℂ) ^ 2 + (2 * a - I * z) * x + -(a : ℂ) ^ 2) +
        cexp (-(x : ℂ) ^ 2 + (2 * (-a) - I * z) * x + -((-a : ℝ) : ℂ) ^ 2)) := by
    intro x
    have h1 := cexp_ofReal_neg_sq x a
    have h2 := cexp_ofReal_neg_sq x (-a)
    rw [show x - -a = x + a by ring] at h2
    rw [gaussPairSource, Complex.ofReal_div, Complex.ofReal_add, h1, h2, mul_div_assoc', mul_add,
      ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add (integrable_cexp_neg_sq_add _ _) (integrable_cexp_neg_sq_add _ _),
    integral_cexp_neg_sq_add, integral_cexp_neg_sq_add, gaussPairTransform, Complex.cos]
  have e1 : -(a : ℂ) ^ 2 + (2 * a - I * z) ^ 2 / 4 = -z ^ 2 / 4 + -(a * z) * I := by
    linear_combination (z ^ 2 / 4) * Complex.I_sq
  have e2 : -((-a : ℝ) : ℂ) ^ 2 + (2 * (-a) - I * z) ^ 2 / 4 = -z ^ 2 / 4 + (a * z) * I := by
    push_cast
    linear_combination (z ^ 2 / 4) * Complex.I_sq
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  rw [show -(↑a * z) * I = -(↑a * z * I) by ring]
  ring_nf

theorem cexp_add_two_pi_mul_I (X : ℂ) : cexp (X + 2 * Real.pi * I) = cexp X := by
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem cexp_sub_two_pi_mul_I (X : ℂ) : cexp (X - 2 * Real.pi * I) = cexp X := by
  rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

/-- **The companion transform.** With `aω = 2π`,
`∫ e^{-izx} k_G(x) cos(ωx) dx = e^{-ω²/4} F_G(z) cosh(ωz/2)`. -/
theorem integral_cexp_mul_gaussPairCosSource {a ω : ℝ} (hω : a * ω = 2 * Real.pi) (z : ℂ) :
    ∫ x : ℝ, cexp (-I * z * x) * (gaussPairCosSource a ω x : ℂ) =
      cexp (-(ω : ℂ) ^ 2 / 4) * gaussPairTransform a z * Complex.cosh (ω * z / 2) := by
  have hpt : ∀ x : ℝ, cexp (-I * z * x) * (gaussPairCosSource a ω x : ℂ) =
      (1 / 4 : ℂ) * ((cexp (-(x : ℂ) ^ 2 + (2 * a + I * (ω - z)) * x + -(a : ℂ) ^ 2) +
        cexp (-(x : ℂ) ^ 2 + (2 * a + I * (-ω - z)) * x + -(a : ℂ) ^ 2)) +
        (cexp (-(x : ℂ) ^ 2 + (-2 * a + I * (ω - z)) * x + -(a : ℂ) ^ 2) +
        cexp (-(x : ℂ) ^ 2 + (-2 * a + I * (-ω - z)) * x + -(a : ℂ) ^ 2))) := by
    intro x
    have h1 := cexp_ofReal_neg_sq x a
    have h2 := cexp_ofReal_neg_sq x (-a)
    rw [show x - -a = x + a by ring] at h2
    rw [gaussPairCosSource, gaussPairSource, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_add, h1, h2, Complex.ofReal_cos, Complex.cos]
    have hA : ∀ (c₁ c₂ : ℂ), cexp (-(x : ℂ) ^ 2 + (c₁ + I * (c₂ - z)) * x + -(a : ℂ) ^ 2) =
        cexp (-I * z * x) * cexp (-(x : ℂ) ^ 2 + c₁ * x + -(a : ℂ) ^ 2) * cexp (c₂ * x * I) := by
      intro c₁ c₂
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    rw [hA, hA, hA, hA]
    push_cast
    ring_nf
  have hI : ∀ c : ℂ, Integrable (fun x : ℝ => cexp (-(x : ℂ) ^ 2 + c * x + -(a : ℂ) ^ 2)) :=
    fun c => integrable_cexp_neg_sq_add _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add, integral_add, integral_add]
  · simp only [integral_cexp_neg_sq_add]
    have hωc : (a : ℂ) * ω = 2 * Real.pi := by exact_mod_cast hω
    have e11 : -(a : ℂ) ^ 2 + (2 * a + I * (ω - z)) ^ 2 / 4 =
        (-(ω : ℂ) ^ 2 / 4 + -z ^ 2 / 4 + ω * z / 2 + -(a * z * I)) + 2 * Real.pi * I := by
      linear_combination ((ω - z) ^ 2 / 4) * Complex.I_sq + I * hωc
    have e1m : -(a : ℂ) ^ 2 + (2 * a + I * (-ω - z)) ^ 2 / 4 =
        (-(ω : ℂ) ^ 2 / 4 + -z ^ 2 / 4 + -(ω * z / 2) + -(a * z * I)) - 2 * Real.pi * I := by
      linear_combination ((-ω - z) ^ 2 / 4) * Complex.I_sq - I * hωc
    have em1 : -(a : ℂ) ^ 2 + (-2 * a + I * (ω - z)) ^ 2 / 4 =
        (-(ω : ℂ) ^ 2 / 4 + -z ^ 2 / 4 + ω * z / 2 + a * z * I) - 2 * Real.pi * I := by
      linear_combination ((ω - z) ^ 2 / 4) * Complex.I_sq - I * hωc
    have emm : -(a : ℂ) ^ 2 + (-2 * a + I * (-ω - z)) ^ 2 / 4 =
        (-(ω : ℂ) ^ 2 / 4 + -z ^ 2 / 4 + -(ω * z / 2) + a * z * I) + 2 * Real.pi * I := by
      linear_combination ((-ω - z) ^ 2 / 4) * Complex.I_sq + I * hωc
    rw [e11, e1m, em1, emm, cexp_add_two_pi_mul_I, cexp_sub_two_pi_mul_I, cexp_sub_two_pi_mul_I,
      cexp_add_two_pi_mul_I, gaussPairTransform, Complex.cos, Complex.cosh]
    simp only [neg_mul, Complex.exp_add, Complex.exp_neg]
    have h1 := Complex.exp_ne_zero ((a : ℂ) * z * I)
    have h2 := Complex.exp_ne_zero ((ω : ℂ) * z / 2)
    generalize cexp ((a : ℂ) * z * I) = X at *
    generalize cexp ((ω : ℂ) * z / 2) = Y at *
    field_simp
    ring
  all_goals first | exact hI _ | exact (hI _).add (hI _)

/-- The control quotient `q_G(z) = e^{-ω²/4} cosh(ωz/2) = H_G/F_G`. -/
def gaussPairQuotient (ω : ℝ) (z : ℂ) : ℂ := cexp (-(ω : ℂ) ^ 2 / 4) * Complex.cosh (ω * z / 2)

theorem gaussPairQuotient_neg (ω : ℝ) (z : ℂ) : gaussPairQuotient ω (-z) = gaussPairQuotient ω z := by
  rw [gaussPairQuotient, gaussPairQuotient, show (ω : ℂ) * -z / 2 = -(ω * z / 2) by ring,
    Complex.cosh_neg]

theorem differentiable_gaussPairQuotient (ω : ℝ) : Differentiable ℂ (gaussPairQuotient ω) :=
  (differentiable_const _).mul (Complex.differentiable_cosh.comp
    (((differentiable_const _).mul differentiable_id).div_const 2))

/-- On the imaginary axis the quotient is bounded: `q_G(iy) = e^{-ω²/4} cos(ωy/2)`. -/
theorem norm_gaussPairQuotient_I_mul_le (ω y : ℝ) :
    ‖gaussPairQuotient ω (I * y)‖ ≤ Real.exp (-ω ^ 2 / 4) := by
  rw [gaussPairQuotient, norm_mul, show (ω : ℂ) * (I * y) / 2 = ((ω * y / 2 : ℝ) : ℂ) * I by
    push_cast; ring, Complex.cosh_mul_I, ← Complex.ofReal_cos, Complex.norm_real,
    show -(ω : ℂ) ^ 2 / 4 = ((-ω ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- The quotient has finite exponential type `|ω|/2`. -/
theorem norm_gaussPairQuotient_le (ω : ℝ) (z : ℂ) :
    ‖gaussPairQuotient ω z‖ ≤ Real.exp (-ω ^ 2 / 4) * Real.exp (|ω| * ‖z‖ / 2) := by
  rw [gaussPairQuotient, norm_mul, show -(ω : ℂ) ^ 2 / 4 = ((-ω ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [Complex.cosh]
  calc ‖(cexp (ω * z / 2) + cexp (-(ω * z / 2))) / 2‖ ≤
        (‖cexp (ω * z / 2)‖ + ‖cexp (-(ω * z / 2))‖) / 2 := by
        rw [norm_div, Complex.norm_ofNat]; gcongr; exact norm_add_le _ _
    _ ≤ (Real.exp (|ω| * ‖z‖ / 2) + Real.exp (|ω| * ‖z‖ / 2)) / 2 := by
        gcongr <;> rw [Complex.norm_exp] <;> refine Real.exp_le_exp.mpr ?_ <;>
        · have := Complex.abs_re_le_norm ((ω : ℂ) * z / 2)
          rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat] at this
          try simp only [Complex.neg_re]
          linarith [(abs_le.mp this).1, (abs_le.mp this).2]
    _ = Real.exp (|ω| * ‖z‖ / 2) := by ring

/-- The quotient is not constant for `ω ≠ 0`. -/
theorem gaussPairQuotient_ne_const {ω : ℝ} (hω : ω ≠ 0) :
    gaussPairQuotient ω (2 * Real.pi * I / ω) ≠ gaussPairQuotient ω 0 := by
  have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  rw [gaussPairQuotient, gaussPairQuotient, mul_zero, zero_div, Complex.cosh_zero, mul_one,
    show (ω : ℂ) * (2 * Real.pi * I / ω) / 2 = (Real.pi : ℂ) * I by
      field_simp, Complex.cosh_mul_I, Complex.cos_pi]
  intro h
  have := Complex.exp_ne_zero (-(ω : ℂ) ^ 2 / 4)
  have h2 : cexp (-(ω : ℂ) ^ 2 / 4) * 2 = 0 := by linear_combination -h
  simp at h2

/-- **The linear angular cusp.** Along `z_R = R(sin δ - i cos δ)` the control quotient grows at
least like `e^{-ω²/4} sinh(|ω| R |sin δ| / 2)`: its indicator is linear in `|sin δ|` near the
imaginary axis. -/
theorem sinh_le_norm_gaussPairQuotient_ray (ω R δ : ℝ) :
    Real.exp (-ω ^ 2 / 4) * Real.sinh (|ω * R * Real.sin δ| / 2) ≤
      ‖gaussPairQuotient ω (R * (Real.sin δ - Real.cos δ * I))‖ := by
  rw [gaussPairQuotient, norm_mul, show -(ω : ℂ) ^ 2 / 4 = ((-ω ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  set x : ℝ := ω * R * Real.sin δ / 2
  set y : ℝ := -(ω * R * Real.cos δ / 2)
  have hw : (ω : ℂ) * (R * (Real.sin δ - Real.cos δ * I)) / 2 = (x : ℂ) + (y : ℂ) * I := by
    simp only [x, y]; push_cast; ring
  rw [hw, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hx : |ω * R * Real.sin δ| / 2 = |x| := by simp only [x]; rw [abs_div, abs_two]
  rw [hx, ← Real.abs_sinh]
  have hsq : Real.sinh x ^ 2 ≤ ‖(Real.cosh x : ℂ) * (Real.cos y : ℂ) + (Real.sinh x : ℂ) * ((Real.sin y : ℂ) * I)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.mul_im]
    have hc := Real.cosh_sq x
    have hs := Real.sin_sq_add_cos_sq y
    nlinarith [sq_nonneg (Real.sinh x * Real.cos y), sq_nonneg (Real.cos y)]
  exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |>.2 |> fun h => by
    rw [← abs_norm]; exact sq_le_sq.mp hsq

/-- The control transform has the periodic zeros of `cos(az)`. -/
theorem gaussPairTransform_eq_zero_iff (a : ℝ) (z : ℂ) :
    gaussPairTransform a z = 0 ↔ ∃ k : ℤ, (a : ℂ) * z = (2 * k + 1) * Real.pi / 2 := by
  have hπ : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not
    exact fun h => absurd h (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [gaussPairTransform, mul_eq_zero, mul_eq_zero, or_iff_right (by
    push Not; exact ⟨hπ, Complex.exp_ne_zero _⟩), Complex.cos_eq_zero_iff]

end

end HTGeometry
