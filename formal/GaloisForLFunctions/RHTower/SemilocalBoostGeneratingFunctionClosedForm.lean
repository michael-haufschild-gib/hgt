import GaloisForLFunctions.RHTower.SemilocalBoostCoefficientInterchange
import GaloisForLFunctions.RHTower.ScalarPowerSeriesUniqueness

/-!
# The two-variable boost generating function in closed form, and its `w`-expansion

For real `|w|, |z| < 1/4` and real `t`, with `τ = tanh t`,

`∫ G_s(w) G_s(z) e^{its} dμ(s) = (cosh t)^{-1/2} (1 − wz − iτ(w + z))^{-1/2}`.

The kernel factors as `(1 − iτz)(1 − q(z) w)` with `q(z) = (z + iτ)/(1 − iτz)`, so the closed form is
a binomial series in `w`; comparing with the term-by-term integration of the generating function
(real-axis uniqueness of power-series coefficients) identifies the boost row coefficients

`∫ c_m p_m(s) G_s(z) e^{its} dμ = (cosh t)^{-1/2} (1 − iτz)^{-1/2} · (−1/2 choose m) · (−q(z))^m`.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

namespace MeixnerPollaczek

open ComplexRapidity PowerSeriesUniqueness

/-! ## cpow helpers -/

theorem ofReal_pos_mul_cpow {r : ℝ} (hr : 0 < r) {X : ℂ} (hX : X ≠ 0) (c : ℂ) :
    ((r : ℂ) * X) ^ c = (r : ℂ) ^ c * X ^ c := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hX), cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hX,
    Complex.log_ofReal_mul hr hX, Complex.ofReal_log hr.le, add_mul, Complex.exp_add]

theorem mul_cpow_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (c : ℂ) :
    (x * y) ^ c = x ^ c * y ^ c := by
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp at hy
  have hargx := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hargy := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have hsum : x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [(abs_lt.mp hargx).1, (abs_lt.mp hargx).2, (abs_lt.mp hargy).1,
      (abs_lt.mp hargy).2]
  rw [cpow_def_of_ne_zero (mul_ne_zero hx0 hy0), cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hy0,
    (Complex.log_mul_eq_add_log_iff hx0 hy0).mpr hsum, add_mul, Complex.exp_add]

/-! ## The boost kernel -/

/-- The boost kernel `1 − wz − i tanh t (w + z)`. -/
noncomputable def boostKernel (t : ℝ) (w z : ℂ) : ℂ :=
  1 - w * z - I * (Real.tanh t : ℂ) * (w + z)

theorem boostKernel_re (t : ℝ) (w z : ℝ) : (boostKernel t w z).re = 1 - w * z := by
  simp [boostKernel]

theorem boostKernel_re_pos (t : ℝ) {w z : ℝ} (hw : |w| < 1) (hz : |z| < 1) :
    0 < (boostKernel t w z).re := by
  rw [boostKernel_re]
  have : |w * z| < 1 := by
    rw [abs_mul]
    calc |w| * |z| < 1 * 1 := mul_lt_mul'' hw hz (abs_nonneg _) (abs_nonneg _)
      _ = 1 := by ring
  linarith [(abs_lt.mp this).2]

theorem boostKernel_ne_zero (t : ℝ) {w z : ℝ} (hw : |w| < 1) (hz : |z| < 1) :
    boostKernel t w z ≠ 0 := by
  intro h
  have := boostKernel_re_pos t hw hz
  rw [h] at this
  simp at this

/-- `cos(arctan w + arctan z + it) = (cosh t / (√(1+w²) √(1+z²))) · boostKernel`. -/
theorem cos_arctan_add_arctan_add_mul_I (t w z : ℝ) :
    Complex.cos (((Real.arctan w + Real.arctan z : ℝ) : ℂ) + (t : ℂ) * I) =
      ((Real.cosh t / (Real.sqrt (1 + w ^ 2) * Real.sqrt (1 + z ^ 2)) : ℝ) : ℂ) *
        boostKernel t w z := by
  rw [cos_eq_re_im]
  have hre : (((Real.arctan w + Real.arctan z : ℝ) : ℂ) + (t : ℂ) * I).re =
      Real.arctan w + Real.arctan z := by simp [-Complex.ofReal_arctan]
  have him : (((Real.arctan w + Real.arctan z : ℝ) : ℂ) + (t : ℂ) * I).im = t := by
    simp [-Complex.ofReal_arctan]
  rw [hre, him, Real.cos_add, Real.sin_add, Real.cos_arctan, Real.sin_arctan, Real.cos_arctan,
    Real.sin_arctan]
  have hu : 0 < Real.sqrt (1 + w ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hv : 0 < Real.sqrt (1 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hch : 0 < Real.cosh t := Real.cosh_pos t
  unfold boostKernel
  rw [Real.tanh_eq_sinh_div_cosh]
  apply Complex.ext
  · simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      one_re, add_re, mul_im, add_im, zero_mul, sub_self, add_zero]
    field_simp
  · simp only [sub_im, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      add_re, mul_im, one_im, add_im, zero_mul, sub_self, zero_sub, add_zero]
    field_simp
    ring

/-- **Closed form of the two-variable boost generating function.** -/
theorem integral_boost_eq_closedForm {w z : ℝ} (hw : |w| < 1) (hz : |z| < 1) (t : ℝ) :
    (∫ s : ℝ, mpGeneratingFunction s w * mpGeneratingFunction s z *
        cexp (((t * s : ℝ) : ℂ) * I) ∂semilocalArchimedeanGammaMeasure) =
      ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boostKernel t w z ^ (-(1 / 2 : ℂ)) := by
  rw [integral_mpGeneratingFunction_mul_cexp hw hz t, cos_arctan_add_arctan_add_mul_I]
  have hu : 0 < Real.sqrt (1 + w ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hv : 0 < Real.sqrt (1 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hch : 0 < Real.cosh t := Real.cosh_pos t
  have hr : 0 < Real.cosh t / (Real.sqrt (1 + w ^ 2) * Real.sqrt (1 + z ^ 2)) := by positivity
  rw [ofReal_pos_mul_cpow hr (boostKernel_ne_zero t hw hz), ← mul_assoc]
  congr 1
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr.le,
    ← Complex.ofReal_mul]
  congr 1
  rw [Real.div_rpow hch.le (by positivity), Real.mul_rpow hu.le hv.le,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity)]
  have h1 : (1 + w ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + z ^ 2) ^ (-(1 / 4 : ℝ)) *
      (Real.cosh t ^ (-(1 / 2 : ℝ)) / ((1 + w ^ 2) ^ (1 / 2 * -(1 / 2 : ℝ)) *
        (1 + z ^ 2) ^ (1 / 2 * -(1 / 2 : ℝ)))) = Real.cosh t ^ (-(1 / 2 : ℝ)) := by
    rw [show (1 / 2 * -(1 / 2 : ℝ)) = -(1 / 4 : ℝ) by norm_num]
    have ha : 0 < (1 + w ^ 2) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    have hb : 0 < (1 + z ^ 2) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    field_simp
  exact h1

/-! ## The `w`-expansion -/

/-- The Möbius ratio `q(z) = (z + iτ)/(1 − iτz)`. -/
noncomputable def boostRatio (t : ℝ) (z : ℂ) : ℂ :=
  (z + I * (Real.tanh t : ℂ)) / (1 - I * (Real.tanh t : ℂ) * z)

theorem one_sub_I_tanh_mul_re (t : ℝ) (z : ℝ) : (1 - I * (Real.tanh t : ℂ) * z).re = 1 := by
  simp

theorem one_sub_I_tanh_mul_ne_zero (t : ℝ) (z : ℝ) : (1 - I * (Real.tanh t : ℂ) * z) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [one_sub_I_tanh_mul_re] at this
  simp at this

theorem boostKernel_eq_mul (t : ℝ) (z : ℝ) (w : ℂ) :
    boostKernel t w z = (1 - I * (Real.tanh t : ℂ) * z) * (1 - boostRatio t z * w) := by
  have h := one_sub_I_tanh_mul_ne_zero t z
  have hcancel : (1 - I * (Real.tanh t : ℂ) * z) * boostRatio t z = (z : ℂ) + I * (Real.tanh t : ℂ) := by
    unfold boostRatio
    field_simp
  unfold boostKernel
  rw [mul_sub, mul_one, ← mul_assoc, hcancel]
  ring

theorem norm_boostRatio_lt (t : ℝ) {z : ℝ} (hz : |z| < 1 / 4) : ‖boostRatio t z‖ < 5 / 3 := by
  unfold boostRatio
  have hτ := Real.abs_tanh_lt_one t
  have hnum : ‖(z : ℂ) + I * (Real.tanh t : ℂ)‖ < 5 / 4 := by
    calc ‖(z : ℂ) + I * (Real.tanh t : ℂ)‖ ≤ ‖(z : ℂ)‖ + ‖I * (Real.tanh t : ℂ)‖ := norm_add_le _ _
      _ = |z| + |Real.tanh t| := by
          rw [norm_mul, norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ < 1 / 4 + 1 := add_lt_add hz hτ
      _ = 5 / 4 := by norm_num
  have hden : 3 / 4 < ‖1 - I * (Real.tanh t : ℂ) * z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (I * (Real.tanh t : ℂ) * z)
    rw [norm_one, norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs] at h
    have : |Real.tanh t| * |z| < 1 / 4 := by
      calc |Real.tanh t| * |z| ≤ 1 * |z| :=
            mul_le_mul_of_nonneg_right hτ.le (abs_nonneg _)
        _ = |z| := one_mul _
        _ < 1 / 4 := hz
    linarith
  rw [norm_div, div_lt_iff₀ (by linarith)]
  calc ‖(z : ℂ) + I * (Real.tanh t : ℂ)‖ < 5 / 4 := hnum
    _ ≤ 5 / 3 * ‖1 - I * (Real.tanh t : ℂ) * z‖ := by linarith

theorem norm_boostRatio_mul_lt (t : ℝ) {z : ℝ} (hz : |z| < 1 / 4) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    ‖boostRatio t z * w‖ < 1 := by
  rw [norm_mul]
  have h1 := norm_boostRatio_lt t hz
  calc ‖boostRatio t z‖ * ‖w‖ ≤ 5 / 3 * ‖w‖ :=
        mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
    _ < 5 / 3 * (1 / 4) := by
        have : (0 : ℝ) < 5 / 3 := by norm_num
        exact mul_lt_mul_of_pos_left hw this
    _ < 1 := by norm_num

/-- The closed form as a function of `w` (real `z`). -/
noncomputable def boostClosedForm (t : ℝ) (z : ℝ) (w : ℂ) : ℂ :=
  ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (1 - I * (Real.tanh t : ℂ) * z) ^ (-(1 / 2 : ℂ)) *
    (1 - boostRatio t z * w) ^ (-(1 / 2 : ℂ))

/-- The closed form agrees with `(cosh t)^{-1/2} boostKernel^{-1/2}` for real `w`. -/
theorem boostClosedForm_ofReal (t : ℝ) {z : ℝ} (hz : |z| < 1 / 4) {w : ℝ} (hw : |w| < 1 / 4) :
    boostClosedForm t z w =
      ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boostKernel t w z ^ (-(1 / 2 : ℂ)) := by
  unfold boostClosedForm
  rw [boostKernel_eq_mul, mul_cpow_of_re_pos, mul_assoc]
  · rw [one_sub_I_tanh_mul_re]; exact one_pos
  · have h := norm_boostRatio_mul_lt t hz (w := (w : ℂ)) (by simpa using hw)
    have := abs_re_le_norm (boostRatio t (z : ℂ) * (w : ℂ))
    simp only [sub_re, one_re]
    linarith [(abs_le.mp this).2]

/-- The `w`-coefficients of the closed form. -/
noncomputable def boostClosedCoefficient (t : ℝ) (z : ℝ) (m : ℕ) : ℂ :=
  ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (1 - I * (Real.tanh t : ℂ) * z) ^ (-(1 / 2 : ℂ)) *
    (Ring.choose (-(1 / 2 : ℂ)) m * (-boostRatio t z) ^ m)

theorem hasSum_boostClosedForm (t : ℝ) {z : ℝ} (hz : |z| < 1 / 4) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    HasSum (fun m : ℕ => boostClosedCoefficient t z m * w ^ m) (boostClosedForm t z w) := by
  have h := hasSum_one_sub_cpow_neg (1 / 2 : ℂ) (norm_boostRatio_mul_lt t hz hw)
  have h' := h.mul_left (((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (1 - I * (Real.tanh t : ℂ) * z) ^ (-(1 / 2 : ℂ)))
  unfold boostClosedForm boostClosedCoefficient
  refine h'.congr_fun fun m => ?_
  rw [neg_mul_eq_neg_mul, mul_pow]
  ring

/-- The boost row coefficient `∫ c_m p_m(s) G_s(z) e^{its} dμ`. -/
noncomputable def boostRowCoefficient (t : ℝ) (z : ℝ) (m : ℕ) : ℂ :=
  ∫ s : ℝ, (mpCoefficient s m : ℂ) * (mpGeneratingFunction s z * cexp (((t * s : ℝ) : ℂ) * I))
    ∂semilocalArchimedeanGammaMeasure

theorem hasSum_boostRowCoefficient (t : ℝ) {z : ℝ} (hz : |z| < 1 / 4) {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    HasSum (fun m : ℕ => boostRowCoefficient t z m * w ^ m)
      (∫ s : ℝ, mpGeneratingFunction s w *
        (mpGeneratingFunction s z * cexp (((t * s : ℝ) : ℂ) * I)) ∂semilocalArchimedeanGammaMeasure) := by
  have h := hasSum_integral_mpCoefficient_mul_boostRow (hz.trans (by norm_num)) t hw
  refine h.congr_fun fun m => ?_
  unfold boostRowCoefficient
  rw [← integral_mul_const]
  congr 1
  funext s
  ring

/-- **Identification of the boost row coefficients.**
`∫ c_m p_m(s) G_s(z) e^{its} dμ = (cosh t)^{-1/2} (1 − iτz)^{-1/2} (−1/2 choose m) (−q(z))^m`. -/
theorem boostRowCoefficient_eq (t : ℝ) {z : ℝ} (hz : |z| < 1 / 4) (m : ℕ) :
    boostRowCoefficient t z m = boostClosedCoefficient t z m := by
  have hFH : ∀ x : ℝ, |x| < 1 / 4 →
      (∫ s : ℝ, mpGeneratingFunction s x *
        (mpGeneratingFunction s z * cexp (((t * s : ℝ) : ℂ) * I)) ∂semilocalArchimedeanGammaMeasure) =
      boostClosedForm t z x := by
    intro x hx
    rw [boostClosedForm_ofReal t hz hx, ← integral_boost_eq_closedForm (hx.trans (by norm_num))
      (hz.trans (by norm_num)) t]
    congr 1
    funext s
    ring
  exact congrFun (eq_of_hasSum_mul_pow_eq_of_ofReal (by norm_num : (0 : ℝ) < 1 / 4)
    (fun w hw => hasSum_boostRowCoefficient t hz hw)
    (fun w hw => hasSum_boostClosedForm t hz hw) hFH) m

end MeixnerPollaczek

end RHTower
