import GaloisForLFunctions.RHTower.StripHorizontalShift
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Pairing a deviation with a strip test: the critical-line representation

Let `w : ℕ → ℝ` with `Σ |w(n)| n^{−7/4} < ∞`, and suppose its Dirichlet series continues to a
function `E` on the strip `½ ≤ Re s ≤ 7/4` with linear growth `‖E(s)‖ ≤ C(1 + |Im s|)`. Let `G`
be holomorphic on the strip `|Im z| ≤ c₀ = 5/(8π)` with `‖G(z)‖ ≤ C/(1 + |Re z|)³`, and let
`g(u) = ∫ G(ξ) e^{2πiξu} dξ`.

**Theorem** (`tsum_deviation_mul_pair_eq`). For every real `y`,
`Σ_n (w(n)/√n)(g(y − log n) + g(y + log n)) = ∫ G(ξ) e^{2πiξy} (E(½ + 2πiξ) + E(½ − 2πiξ)) dξ`.

**Proof.** In `g(y − log n)` move the line of integration down by `c₀`. The factor
`e^{2πi(ξ − ic₀)(−log n)}` becomes `n^{−5/4 − 2πiξ}`, so the `n`-sum converges absolutely and
sums to `E(7/4 + 2πiξ) = E(½ + 2πi(ξ − ic₀))`. Moving the line back up gives
`∫ G(ξ)e^{2πiξy}E(½ + 2πiξ)dξ`. The term `g(y + log n)` is symmetric, with the line moved up.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace RHTower.WeilRegular

noncomputable section

/-! ## The shift height -/

/-- The shift height `c₀ = 5/(8π)`, chosen so that `2πc₀ = 5/4`. -/
def shiftHeight : ℝ := 5 / (8 * π)

theorem shiftHeight_pos : 0 < shiftHeight := by unfold shiftHeight; positivity

theorem two_pi_mul_shiftHeight : 2 * π * shiftHeight = 5 / 4 := by
  unfold shiftHeight; field_simp; ring

theorem two_pi_mul_shiftHeight_complex : (2 : ℂ) * π * shiftHeight = 5 / 4 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) two_pi_mul_shiftHeight
  push_cast at h
  exact h

/-! ## Horizontal shifts with quadratic decay -/

/-- **Lower horizontal shift with quadratic decay.** -/
theorem integral_shift_lower_of_decay {F : ℂ → ℂ} {c C : ℝ} (hc : 0 ≤ c)
    (hF : ∀ z : ℂ, -c ≤ z.im → z.im ≤ 0 → DifferentiableAt ℂ F z)
    (hbound : ∀ z : ℂ, -c ≤ z.im → z.im ≤ 0 → ‖F z‖ ≤ C * (1 + z.re ^ (2 : ℕ))⁻¹) :
    (∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I)) = ∫ x : ℝ, F (x : ℂ) := by
  have h := RHTower.integral_horizontal_shift_of_upper_inv_one_add_sq_decay
    (F := fun z => F (z - (c : ℂ) * I)) hc
    (fun z h0 h1 => (hF _ (by simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; linarith) (by simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; linarith)).comp z
      (differentiableAt_id.sub_const _))
    (fun z h0 h1 => by
      simpa using hbound (z - (c : ℂ) * I) (by simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; linarith) (by simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; linarith))
  simp only [add_sub_cancel_right] at h
  exact h.symm

/-! ## Elementary bounds -/

theorem norm_cexp_two_pi_I_mul (z : ℂ) (u : ℝ) :
    ‖cexp (2 * π * I * z * u)‖ = Real.exp (-(2 * π * z.im * u)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

theorem inv_one_add_abs_pow_three_le (x : ℝ) : ((1 + |x|) ^ 3)⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
  have h0 := abs_nonneg x
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  apply inv_anti₀ (by positivity)
  rw [hx2]; nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

theorem one_add_two_pi_abs_le (x : ℝ) : 1 + 2 * π * |x| ≤ 2 * π * (1 + |x|) := by
  have := Real.pi_gt_three; nlinarith [abs_nonneg x]

theorem inv_one_add_abs_pow_three_mul_le (x : ℝ) :
    ((1 + |x|) ^ 3)⁻¹ * (1 + 2 * π * |x|) ≤ 2 * π * (1 + x ^ 2)⁻¹ := by
  have h0 := abs_nonneg x
  have hp : 0 < 1 + |x| := by positivity
  calc ((1 + |x|) ^ 3)⁻¹ * (1 + 2 * π * |x|) ≤ ((1 + |x|) ^ 3)⁻¹ * (2 * π * (1 + |x|)) :=
        mul_le_mul_of_nonneg_left (one_add_two_pi_abs_le x) (by positivity)
    _ = 2 * π * ((1 + |x|) ^ 2)⁻¹ := by field_simp
    _ ≤ 2 * π * (1 + x ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (by positivity)
        rw [show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]; nlinarith

/-! ## The strip data -/

variable {w : ℕ → ℝ} {E G : ℂ → ℂ} {g : ℝ → ℂ} {CE CG : ℝ}

/-- `g(u)` on the lowered line. -/
theorem g_eq_lower (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹)
    (hg : ∀ u : ℝ, g u = ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * u)) (u : ℝ) :
    g u = ∫ ξ : ℝ, G (ξ - shiftHeight * I) * cexp (2 * π * I * (ξ - shiftHeight * I) * u) := by
  rw [hg]
  symm
  refine integral_shift_lower_of_decay (F := fun z => G z * cexp (2 * π * I * z * u))
    (C := CG * Real.exp (2 * π * shiftHeight * |u|)) shiftHeight_pos.le ?_ ?_
  · intro z h0 h1
    exact (hGd z (abs_le.mpr ⟨h0, by linarith [shiftHeight_pos]⟩)).mul (by fun_prop)
  · intro z h0 h1
    have hz : |z.im| ≤ shiftHeight := abs_le.mpr ⟨h0, by linarith [shiftHeight_pos]⟩
    rw [norm_mul, norm_cexp_two_pi_I_mul]
    have hG := hGb z hz
    have hCG : 0 ≤ CG := by
      have hp : 0 < ((1 + |z.re|) ^ 3)⁻¹ := by positivity
      nlinarith [norm_nonneg (G z)]
    have he : Real.exp (-(2 * π * z.im * u)) ≤ Real.exp (2 * π * shiftHeight * |u|) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(z.im * u) ≤ shiftHeight * |u| := by
        have := abs_mul z.im u
        have h2 : |z.im| * |u| ≤ shiftHeight * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg u)
        linarith [neg_abs_le (z.im * u)]
      nlinarith [Real.pi_pos]
    calc ‖G z‖ * Real.exp (-(2 * π * z.im * u))
        ≤ CG * ((1 + |z.re|) ^ 3)⁻¹ * Real.exp (2 * π * shiftHeight * |u|) :=
          mul_le_mul hG he (Real.exp_pos _).le (by positivity)
      _ ≤ CG * (1 + z.re ^ (2 : ℕ))⁻¹ * Real.exp (2 * π * shiftHeight * |u|) := by
          gcongr
          rw [show z.re ^ 2 = |z.re| ^ 2 from (sq_abs _).symm]
          nlinarith [abs_nonneg z.re, mul_nonneg (abs_nonneg z.re) (abs_nonneg z.re)]
      _ = CG * Real.exp (2 * π * shiftHeight * |u|) * (1 + z.re ^ (2 : ℕ))⁻¹ := by ring

/-- `g(u)` on the raised line. -/
theorem g_eq_upper (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹)
    (hg : ∀ u : ℝ, g u = ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * u)) (u : ℝ) :
    g u = ∫ ξ : ℝ, G (ξ + shiftHeight * I) * cexp (2 * π * I * (ξ + shiftHeight * I) * u) := by
  rw [hg]
  symm
  refine RHTower.integral_horizontal_shift_of_upper_inv_one_add_sq_decay
    (F := fun z => G z * cexp (2 * π * I * z * u))
    (C := CG * Real.exp (2 * π * shiftHeight * |u|)) shiftHeight_pos.le ?_ ?_
  · intro z h0 h1
    exact (hGd z (abs_le.mpr ⟨by linarith [shiftHeight_pos], h1⟩)).mul (by fun_prop)
  · intro z h0 h1
    have hz : |z.im| ≤ shiftHeight := abs_le.mpr ⟨by linarith [shiftHeight_pos], h1⟩
    rw [norm_mul, norm_cexp_two_pi_I_mul]
    have hG := hGb z hz
    have hCG : 0 ≤ CG := by
      have hp : 0 < ((1 + |z.re|) ^ 3)⁻¹ := by positivity
      nlinarith [norm_nonneg (G z)]
    have he : Real.exp (-(2 * π * z.im * u)) ≤ Real.exp (2 * π * shiftHeight * |u|) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(z.im * u) ≤ shiftHeight * |u| := by
        have := abs_mul z.im u
        have h2 : |z.im| * |u| ≤ shiftHeight * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg u)
        linarith [neg_abs_le (z.im * u)]
      nlinarith [Real.pi_pos]
    calc ‖G z‖ * Real.exp (-(2 * π * z.im * u))
        ≤ CG * ((1 + |z.re|) ^ 3)⁻¹ * Real.exp (2 * π * shiftHeight * |u|) :=
          mul_le_mul hG he (Real.exp_pos _).le (by positivity)
      _ ≤ CG * (1 + z.re ^ (2 : ℕ))⁻¹ * Real.exp (2 * π * shiftHeight * |u|) := by
          gcongr
          rw [show z.re ^ 2 = |z.re| ^ 2 from (sq_abs _).symm]
          nlinarith [abs_nonneg z.re, mul_nonneg (abs_nonneg z.re) (abs_nonneg z.re)]
      _ = CG * Real.exp (2 * π * shiftHeight * |u|) * (1 + z.re ^ (2 : ℕ))⁻¹ := by ring

/-! ## The exponent algebra -/

theorem sqrt_inv_eq_cexp {n : ℕ} (hn : 0 < n) :
    (((Real.sqrt n)⁻¹ : ℝ) : ℂ) = cexp (-(Real.log n / 2 : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn', ← Real.exp_neg, Complex.ofReal_exp]
  congr 1; push_cast; ring

theorem natCast_cpow_eq_cexp {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ s = cexp ((Real.log n : ℂ) * s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hn'.le]

/-- `n^{−½} e^{2πi(ξ − ic₀)(y − log n)} = e^{2πi(ξ − ic₀)y} n^{−(7/4 + 2πiξ)}`. -/
theorem sqrt_inv_mul_cexp_lower {n : ℕ} (hn : 0 < n) (ξ y : ℝ) :
    (((Real.sqrt n)⁻¹ : ℝ) : ℂ) *
        cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * ((y - Real.log n : ℝ) : ℂ)) =
      cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * y) *
        (n : ℂ) ^ (-(7 / 4 + 2 * π * I * ξ)) := by
  rw [sqrt_inv_eq_cexp hn, natCast_cpow_eq_cexp hn, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hc := two_pi_mul_shiftHeight_complex
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
  linear_combination (-(Real.log n : ℂ)) * hc + (2 * π * shiftHeight * Real.log n : ℂ) * I_sq

/-- `n^{−½} e^{2πi(ξ + ic₀)(y + log n)} = e^{2πi(ξ + ic₀)y} n^{−(7/4 − 2πiξ)}`. -/
theorem sqrt_inv_mul_cexp_upper {n : ℕ} (hn : 0 < n) (ξ y : ℝ) :
    (((Real.sqrt n)⁻¹ : ℝ) : ℂ) *
        cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * ((y + Real.log n : ℝ) : ℂ)) =
      cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * y) *
        (n : ℂ) ^ (-(7 / 4 - 2 * π * I * ξ)) := by
  rw [sqrt_inv_eq_cexp hn, natCast_cpow_eq_cexp hn, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hc := two_pi_mul_shiftHeight_complex
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat]
  linear_combination (-(Real.log n : ℂ)) * hc + (2 * π * shiftHeight * Real.log n : ℂ) * I_sq

theorem lower_argument (ξ : ℝ) :
    (1 / 2 : ℂ) + 2 * π * I * ((ξ : ℂ) - shiftHeight * I) = 7 / 4 + 2 * π * I * ξ := by
  have hc := two_pi_mul_shiftHeight_complex
  linear_combination hc - (2 * π * shiftHeight : ℂ) * I_sq

theorem upper_argument (ξ : ℝ) :
    (1 / 2 : ℂ) - 2 * π * I * ((ξ : ℂ) + shiftHeight * I) = 7 / 4 - 2 * π * I * ξ := by
  have hc := two_pi_mul_shiftHeight_complex
  linear_combination hc - (2 * π * shiftHeight : ℂ) * I_sq

/-! ## Norms of the Dirichlet terms -/

theorem norm_w_mul_cpow (hw0 : w 0 = 0) (n : ℕ) {s : ℂ} (hs : s.re = -(7 / 4)) :
    ‖(w n : ℂ) * (n : ℂ) ^ s‖ = |w n| * (n : ℝ) ^ (-(7 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hw0]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos hn, hs]

theorem continuous_natCast_cpow_line (n : ℕ) (a b : ℂ) (ha : a.re ≠ 0) (hb : b.im = 0) :
    Continuous fun ξ : ℝ => (n : ℂ) ^ (-(a + b * I * ξ)) := by
  refine Continuous.const_cpow (by fun_prop) (Or.inr fun ξ h => ha ?_)
  have := congrArg Complex.re h
  simp [hb] at this
  linarith

/-! ## The lower sum -/

theorem lower_sum (hw0 : w 0 = 0) (hwsum : Summable fun n : ℕ => |w n| * (n : ℝ) ^ (-(7 / 4 : ℝ)))
    (hEser : ∀ s : ℂ, s.re = 7 / 4 → E s = ∑' n : ℕ, (w n : ℂ) * (n : ℂ) ^ (-s))
    (hCG : 0 ≤ CG) (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹)
    (hg : ∀ u : ℝ, g u = ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * u)) (y : ℝ) :
    (Summable fun n : ℕ => ((w n / Real.sqrt n : ℝ) : ℂ) * g (y - Real.log n)) ∧
      ∑' n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) * g (y - Real.log n) =
        ∫ ξ : ℝ, G ((ξ : ℂ) - shiftHeight * I) *
          cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * y) * E (7 / 4 + 2 * π * I * ξ) := by
  set H : ℝ → ℂ := fun ξ => G ((ξ : ℂ) - shiftHeight * I) *
    cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * y) with hH
  have him : ∀ ξ : ℝ, |((ξ : ℂ) - shiftHeight * I).im| ≤ shiftHeight := fun ξ => by
    simp [abs_of_pos shiftHeight_pos]
  have hHc : Continuous H := by
    refine Continuous.mul ?_ (by fun_prop)
    exact continuous_iff_continuousAt.mpr fun ξ =>
      (hGd _ (him ξ)).continuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) - shiftHeight * I)
        (by fun_prop)
  have hHb : ∀ ξ : ℝ, ‖H ξ‖ ≤ CG * Real.exp (2 * π * shiftHeight * y) * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    rw [hH, norm_mul, norm_cexp_two_pi_I_mul]
    have hG := hGb _ (him ξ)
    have hre : ((ξ : ℂ) - shiftHeight * I).re = ξ := by simp
    have himv : ((ξ : ℂ) - shiftHeight * I).im = -shiftHeight := by simp
    rw [hre] at hG
    rw [himv]
    have h3 := inv_one_add_abs_pow_three_le ξ
    calc ‖G ((ξ : ℂ) - shiftHeight * I)‖ * Real.exp (-(2 * π * -shiftHeight * y))
        ≤ CG * ((1 + |ξ|) ^ 3)⁻¹ * Real.exp (2 * π * shiftHeight * y) := by
          rw [show -(2 * π * -shiftHeight * y) = 2 * π * shiftHeight * y by ring]
          exact mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le
      _ ≤ CG * (1 + ξ ^ 2)⁻¹ * Real.exp (2 * π * shiftHeight * y) := by gcongr
      _ = CG * Real.exp (2 * π * shiftHeight * y) * (1 + ξ ^ 2)⁻¹ := by ring
  have hHi : Integrable H :=
    (integrable_inv_one_add_sq.const_mul _).mono' hHc.aestronglyMeasurable
      (Eventually.of_forall hHb)
  set F : ℕ → ℝ → ℂ := fun n ξ => H ξ * ((w n : ℂ) * (n : ℂ) ^ (-(7 / 4 + 2 * π * I * ξ)))
    with hF
  have hFn : ∀ n ξ, ‖F n ξ‖ = ‖H ξ‖ * (|w n| * (n : ℝ) ^ (-(7 / 4 : ℝ))) := by
    intro n ξ
    rw [hF, norm_mul, norm_w_mul_cpow hw0 n]
    simp
  have hFc : ∀ n, Continuous (F n) := fun n =>
    hHc.mul (continuous_const.mul
      (continuous_natCast_cpow_line n (7 / 4) (2 * π) (by norm_num) (by simp)))
  have hFi : ∀ n, Integrable (F n) := fun n =>
    (hHi.norm.mul_const (|w n| * (n : ℝ) ^ (-(7 / 4 : ℝ)))).mono' (hFc n).aestronglyMeasurable
      (Eventually.of_forall fun ξ => le_of_eq (hFn n ξ))
  have hterm : ∀ n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) * g (y - Real.log n) = ∫ ξ, F n ξ := by
    intro n
    rw [g_eq_lower hGd hGb hg (y - Real.log n), ← integral_const_mul]
    congr 1; funext ξ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, hw0]
    have hcast : ((w n / Real.sqrt n : ℝ) : ℂ) = (w n : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, hF, hH]
    simp only
    calc (w n : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * (G ((ξ : ℂ) - shiftHeight * I) *
          cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * ((y - Real.log n : ℝ) : ℂ)))
        = (w n : ℂ) * G ((ξ : ℂ) - shiftHeight * I) * ((((Real.sqrt n)⁻¹ : ℝ) : ℂ) *
          cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * ((y - Real.log n : ℝ) : ℂ))) := by
          ring
      _ = (w n : ℂ) * G ((ξ : ℂ) - shiftHeight * I) *
          (cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * y) *
            (n : ℂ) ^ (-(7 / 4 + 2 * π * I * ξ))) := by rw [sqrt_inv_mul_cexp_lower hn]
      _ = _ := by ring
  have hint : ∀ n, ∫ ξ, ‖F n ξ‖ = (|w n| * (n : ℝ) ^ (-(7 / 4 : ℝ))) * ∫ ξ, ‖H ξ‖ := by
    intro n
    simp_rw [hFn]
    rw [integral_mul_const]; ring
  have hsum : Summable fun n => ∫ ξ, ‖F n ξ‖ := by
    simp_rw [hint]; exact hwsum.mul_right _
  refine ⟨Summable.of_norm_bounded hsum fun n => ?_, ?_⟩
  · rw [hterm n]; exact norm_integral_le_integral_norm _
  · rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hsum]
    congr 1; funext ξ
    simp only [hF]
    rw [tsum_mul_left, hEser _ (by simp)]

/-- **Back to the real line (lower half).** -/
theorem lower_shift_back
    (hEd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → DifferentiableAt ℂ E s)
    (hCE : 0 ≤ CE) (hEb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → ‖E s‖ ≤ CE * (1 + |s.im|))
    (hCG : 0 ≤ CG) (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹) (y : ℝ) :
    ∫ ξ : ℝ, G ((ξ : ℂ) - shiftHeight * I) *
        cexp (2 * π * I * ((ξ : ℂ) - shiftHeight * I) * y) * E (7 / 4 + 2 * π * I * ξ) =
      ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * y) * E (1 / 2 + 2 * π * I * ξ) := by
  have h2c := two_pi_mul_shiftHeight
  have h := integral_shift_lower_of_decay
    (F := fun z => G z * cexp (2 * π * I * z * y) * E (1 / 2 + 2 * π * I * z))
    (C := CG * Real.exp (2 * π * shiftHeight * |y|) * CE * (2 * π)) shiftHeight_pos.le ?_ ?_
  · rw [← h]
    congr 1; funext ξ
    rw [lower_argument]
  · intro z h0 h1
    have hz : |z.im| ≤ shiftHeight := abs_le.mpr ⟨h0, by linarith [shiftHeight_pos]⟩
    refine ((hGd z hz).mul (by fun_prop)).mul ?_
    refine (hEd _ ?_ ?_).comp z (by fun_prop)
    · simp; nlinarith [Real.pi_pos]
    · simp; nlinarith [Real.pi_pos]
  · intro z h0 h1
    have hz : |z.im| ≤ shiftHeight := abs_le.mpr ⟨h0, by linarith [shiftHeight_pos]⟩
    rw [norm_mul, norm_mul, norm_cexp_two_pi_I_mul]
    have hG := hGb z hz
    have hE := hEb (1 / 2 + 2 * π * I * z) (by simp; nlinarith [Real.pi_pos])
      (by simp; nlinarith [Real.pi_pos])
    have himE : |(1 / 2 + 2 * π * I * z : ℂ).im| = 2 * π * |z.re| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rw [himE] at hE
    have he : Real.exp (-(2 * π * z.im * y)) ≤ Real.exp (2 * π * shiftHeight * |y|) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(z.im * y) ≤ shiftHeight * |y| := by
        have := abs_mul z.im y
        have h2 : |z.im| * |y| ≤ shiftHeight * |y| := mul_le_mul_of_nonneg_right hz (abs_nonneg y)
        linarith [neg_abs_le (z.im * y)]
      nlinarith [Real.pi_pos]
    have hk := inv_one_add_abs_pow_three_mul_le z.re
    calc ‖G z‖ * Real.exp (-(2 * π * z.im * y)) * ‖E (1 / 2 + 2 * π * I * z)‖
        ≤ CG * ((1 + |z.re|) ^ 3)⁻¹ * Real.exp (2 * π * shiftHeight * |y|) *
            (CE * (1 + 2 * π * |z.re|)) := by gcongr
      _ = CG * Real.exp (2 * π * shiftHeight * |y|) * CE *
            (((1 + |z.re|) ^ 3)⁻¹ * (1 + 2 * π * |z.re|)) := by ring
      _ ≤ CG * Real.exp (2 * π * shiftHeight * |y|) * CE * (2 * π * (1 + z.re ^ 2)⁻¹) := by
          gcongr
      _ = CG * Real.exp (2 * π * shiftHeight * |y|) * CE * (2 * π) * (1 + z.re ^ (2 : ℕ))⁻¹ := by
          ring

/-! ## The upper sum -/

theorem upper_sum (hw0 : w 0 = 0) (hwsum : Summable fun n : ℕ => |w n| * (n : ℝ) ^ (-(7 / 4 : ℝ)))
    (hEser : ∀ s : ℂ, s.re = 7 / 4 → E s = ∑' n : ℕ, (w n : ℂ) * (n : ℂ) ^ (-s))
    (hCG : 0 ≤ CG) (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹)
    (hg : ∀ u : ℝ, g u = ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * u)) (y : ℝ) :
    (Summable fun n : ℕ => ((w n / Real.sqrt n : ℝ) : ℂ) * g (y + Real.log n)) ∧
      ∑' n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) * g (y + Real.log n) =
        ∫ ξ : ℝ, G ((ξ : ℂ) + shiftHeight * I) *
          cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * y) * E (7 / 4 - 2 * π * I * ξ) := by
  set H : ℝ → ℂ := fun ξ => G ((ξ : ℂ) + shiftHeight * I) *
    cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * y) with hH
  have him : ∀ ξ : ℝ, |((ξ : ℂ) + shiftHeight * I).im| ≤ shiftHeight := fun ξ => by
    simp [abs_of_pos shiftHeight_pos]
  have hHc : Continuous H := by
    refine Continuous.mul ?_ (by fun_prop)
    exact continuous_iff_continuousAt.mpr fun ξ =>
      (hGd _ (him ξ)).continuousAt.comp (f := fun ξ : ℝ => (ξ : ℂ) + shiftHeight * I)
        (by fun_prop)
  have hHb : ∀ ξ : ℝ, ‖H ξ‖ ≤ CG * Real.exp (-(2 * π * shiftHeight * y)) * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    rw [hH, norm_mul, norm_cexp_two_pi_I_mul]
    have hG := hGb _ (him ξ)
    have hre : ((ξ : ℂ) + shiftHeight * I).re = ξ := by simp
    have himv : ((ξ : ℂ) + shiftHeight * I).im = shiftHeight := by simp
    rw [hre] at hG
    rw [himv]
    have h3 := inv_one_add_abs_pow_three_le ξ
    calc ‖G ((ξ : ℂ) + shiftHeight * I)‖ * Real.exp (-(2 * π * shiftHeight * y))
        ≤ CG * ((1 + |ξ|) ^ 3)⁻¹ * Real.exp (-(2 * π * shiftHeight * y)) :=
          mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le
      _ ≤ CG * (1 + ξ ^ 2)⁻¹ * Real.exp (-(2 * π * shiftHeight * y)) := by gcongr
      _ = CG * Real.exp (-(2 * π * shiftHeight * y)) * (1 + ξ ^ 2)⁻¹ := by ring
  have hHi : Integrable H :=
    (integrable_inv_one_add_sq.const_mul _).mono' hHc.aestronglyMeasurable
      (Eventually.of_forall hHb)
  set F : ℕ → ℝ → ℂ := fun n ξ => H ξ * ((w n : ℂ) * (n : ℂ) ^ (-(7 / 4 - 2 * π * I * ξ)))
    with hF
  have hFn : ∀ n ξ, ‖F n ξ‖ = ‖H ξ‖ * (|w n| * (n : ℝ) ^ (-(7 / 4 : ℝ))) := by
    intro n ξ
    rw [hF, norm_mul, norm_w_mul_cpow hw0 n]
    simp
  have hFc : ∀ n, Continuous (F n) := by
    intro n
    have hc : Continuous fun ξ : ℝ => (n : ℂ) ^ (-(7 / 4 - 2 * π * I * ξ)) := by
      have h := continuous_natCast_cpow_line n (7 / 4) (-(2 * π)) (by norm_num) (by simp)
      convert h using 3 with ξ
      ring
    exact hHc.mul (continuous_const.mul hc)
  have hFi : ∀ n, Integrable (F n) := fun n =>
    (hHi.norm.mul_const (|w n| * (n : ℝ) ^ (-(7 / 4 : ℝ)))).mono' (hFc n).aestronglyMeasurable
      (Eventually.of_forall fun ξ => le_of_eq (hFn n ξ))
  have hterm : ∀ n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) * g (y + Real.log n) = ∫ ξ, F n ξ := by
    intro n
    rw [g_eq_upper hGd hGb hg (y + Real.log n), ← integral_const_mul]
    congr 1; funext ξ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, hw0]
    have hcast : ((w n / Real.sqrt n : ℝ) : ℂ) = (w n : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, hF, hH]
    simp only
    calc (w n : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * (G ((ξ : ℂ) + shiftHeight * I) *
          cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * ((y + Real.log n : ℝ) : ℂ)))
        = (w n : ℂ) * G ((ξ : ℂ) + shiftHeight * I) * ((((Real.sqrt n)⁻¹ : ℝ) : ℂ) *
          cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * ((y + Real.log n : ℝ) : ℂ))) := by
          ring
      _ = (w n : ℂ) * G ((ξ : ℂ) + shiftHeight * I) *
          (cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * y) *
            (n : ℂ) ^ (-(7 / 4 - 2 * π * I * ξ))) := by rw [sqrt_inv_mul_cexp_upper hn]
      _ = _ := by ring
  have hint : ∀ n, ∫ ξ, ‖F n ξ‖ = (|w n| * (n : ℝ) ^ (-(7 / 4 : ℝ))) * ∫ ξ, ‖H ξ‖ := by
    intro n
    simp_rw [hFn]
    rw [integral_mul_const]; ring
  have hsum : Summable fun n => ∫ ξ, ‖F n ξ‖ := by
    simp_rw [hint]; exact hwsum.mul_right _
  refine ⟨Summable.of_norm_bounded hsum fun n => ?_, ?_⟩
  · rw [hterm n]; exact norm_integral_le_integral_norm _
  · rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hsum]
    congr 1; funext ξ
    simp only [hF]
    rw [tsum_mul_left, hEser _ (by simp)]

/-- **Back to the real line (upper half).** -/
theorem upper_shift_back
    (hEd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → DifferentiableAt ℂ E s)
    (hCE : 0 ≤ CE) (hEb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → ‖E s‖ ≤ CE * (1 + |s.im|))
    (hCG : 0 ≤ CG) (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹) (y : ℝ) :
    ∫ ξ : ℝ, G ((ξ : ℂ) + shiftHeight * I) *
        cexp (2 * π * I * ((ξ : ℂ) + shiftHeight * I) * y) * E (7 / 4 - 2 * π * I * ξ) =
      ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * y) * E (1 / 2 - 2 * π * I * ξ) := by
  have h2c := two_pi_mul_shiftHeight
  have h := RHTower.integral_horizontal_shift_of_upper_inv_one_add_sq_decay
    (F := fun z => G z * cexp (2 * π * I * z * y) * E (1 / 2 - 2 * π * I * z))
    (C := CG * Real.exp (2 * π * shiftHeight * |y|) * CE * (2 * π)) shiftHeight_pos.le ?_ ?_
  · rw [← h]
    congr 1; funext ξ
    rw [upper_argument]
  · intro z h0 h1
    have hz : |z.im| ≤ shiftHeight := abs_le.mpr ⟨by linarith [shiftHeight_pos], h1⟩
    refine ((hGd z hz).mul (by fun_prop)).mul ?_
    refine (hEd _ ?_ ?_).comp z (by fun_prop)
    · simp; nlinarith [Real.pi_pos]
    · simp; nlinarith [Real.pi_pos]
  · intro z h0 h1
    have hz : |z.im| ≤ shiftHeight := abs_le.mpr ⟨by linarith [shiftHeight_pos], h1⟩
    rw [norm_mul, norm_mul, norm_cexp_two_pi_I_mul]
    have hG := hGb z hz
    have hE := hEb (1 / 2 - 2 * π * I * z) (by simp; nlinarith [Real.pi_pos])
      (by simp; nlinarith [Real.pi_pos])
    have himE : |(1 / 2 - 2 * π * I * z : ℂ).im| = 2 * π * |z.re| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rw [himE] at hE
    have he : Real.exp (-(2 * π * z.im * y)) ≤ Real.exp (2 * π * shiftHeight * |y|) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(z.im * y) ≤ shiftHeight * |y| := by
        have := abs_mul z.im y
        have h2 : |z.im| * |y| ≤ shiftHeight * |y| := mul_le_mul_of_nonneg_right hz (abs_nonneg y)
        linarith [neg_abs_le (z.im * y)]
      nlinarith [Real.pi_pos]
    have hk := inv_one_add_abs_pow_three_mul_le z.re
    calc ‖G z‖ * Real.exp (-(2 * π * z.im * y)) * ‖E (1 / 2 - 2 * π * I * z)‖
        ≤ CG * ((1 + |z.re|) ^ 3)⁻¹ * Real.exp (2 * π * shiftHeight * |y|) *
            (CE * (1 + 2 * π * |z.re|)) := by gcongr
      _ = CG * Real.exp (2 * π * shiftHeight * |y|) * CE *
            (((1 + |z.re|) ^ 3)⁻¹ * (1 + 2 * π * |z.re|)) := by ring
      _ ≤ CG * Real.exp (2 * π * shiftHeight * |y|) * CE * (2 * π * (1 + z.re ^ 2)⁻¹) := by
          gcongr
      _ = CG * Real.exp (2 * π * shiftHeight * |y|) * CE * (2 * π) * (1 + z.re ^ (2 : ℕ))⁻¹ := by
          ring

/-! ## The representation -/

theorem integrable_line (hEd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → DifferentiableAt ℂ E s)
    (hCE : 0 ≤ CE) (hEb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → ‖E s‖ ≤ CE * (1 + |s.im|))
    (hCG : 0 ≤ CG) (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹) (y : ℝ)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Integrable fun ξ : ℝ => G ξ * cexp (2 * π * I * ξ * y) * E (1 / 2 + ε * (2 * π * I * ξ)) := by
  have hre : ∀ ξ : ℝ, (1 / 2 + ε * (2 * π * I * ξ) : ℂ).re = 1 / 2 := by
    intro ξ; simp
  have him : ∀ ξ : ℝ, |(1 / 2 + ε * (2 * π * I * ξ) : ℂ).im| = 2 * π * |ξ| := by
    intro ξ
    rcases hε with rfl | rfl <;> simp [abs_mul, abs_of_pos Real.pi_pos]
  have hGc : Continuous fun ξ : ℝ => G ξ :=
    continuous_iff_continuousAt.mpr fun ξ =>
      (hGd _ (by simp [shiftHeight_pos.le])).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hEc : Continuous fun ξ : ℝ => E (1 / 2 + ε * (2 * π * I * ξ)) :=
    continuous_iff_continuousAt.mpr fun ξ =>
      (hEd _ (by rw [hre]) (by rw [hre]; norm_num)).continuousAt.comp
        (f := fun ξ : ℝ => (1 / 2 + ε * (2 * π * I * ξ) : ℂ)) (by fun_prop)
  refine (integrable_inv_one_add_sq.const_mul (CG * CE * (2 * π))).mono'
    ((hGc.mul (by fun_prop)).mul hEc).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_mul, norm_cexp_two_pi_I_mul]
  have hG := hGb (ξ : ℂ) (by simp [shiftHeight_pos.le])
  have hE := hEb (1 / 2 + (ε : ℂ) * (2 * π * I * ξ)) (by rw [hre]) (by rw [hre]; norm_num)
  rw [him] at hE
  simp only [Complex.ofReal_re] at hG
  simp only [Complex.ofReal_im, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
  have hk := inv_one_add_abs_pow_three_mul_le ξ
  calc ‖G ξ‖ * ‖E (1 / 2 + ε * (2 * π * I * ξ))‖
      ≤ CG * ((1 + |ξ|) ^ 3)⁻¹ * (CE * (1 + 2 * π * |ξ|)) := by gcongr
    _ = CG * CE * (((1 + |ξ|) ^ 3)⁻¹ * (1 + 2 * π * |ξ|)) := by ring
    _ ≤ CG * CE * (2 * π * (1 + ξ ^ 2)⁻¹) := by gcongr
    _ = CG * CE * (2 * π) * (1 + ξ ^ 2)⁻¹ := by ring

/-- **The critical-line representation of a deviation pairing.** -/
theorem tsum_deviation_mul_pair_eq (hw0 : w 0 = 0)
    (hwsum : Summable fun n : ℕ => |w n| * (n : ℝ) ^ (-(7 / 4 : ℝ)))
    (hEser : ∀ s : ℂ, s.re = 7 / 4 → E s = ∑' n : ℕ, (w n : ℂ) * (n : ℂ) ^ (-s))
    (hEd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → DifferentiableAt ℂ E s)
    (hCE : 0 ≤ CE) (hEb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → ‖E s‖ ≤ CE * (1 + |s.im|))
    (hCG : 0 ≤ CG) (hGd : ∀ z : ℂ, |z.im| ≤ shiftHeight → DifferentiableAt ℂ G z)
    (hGb : ∀ z : ℂ, |z.im| ≤ shiftHeight → ‖G z‖ ≤ CG * ((1 + |z.re|) ^ 3)⁻¹)
    (hg : ∀ u : ℝ, g u = ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * u)) (y : ℝ) :
    ∑' n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) * (g (y - Real.log n) + g (y + Real.log n)) =
      ∫ ξ : ℝ, G ξ * cexp (2 * π * I * ξ * y) *
        (E (1 / 2 + 2 * π * I * ξ) + E (1 / 2 - 2 * π * I * ξ)) := by
  obtain ⟨hs1, he1⟩ := lower_sum hw0 hwsum hEser hCG hGd hGb hg y
  obtain ⟨hs2, he2⟩ := upper_sum hw0 hwsum hEser hCG hGd hGb hg y
  simp_rw [mul_add]
  rw [hs1.tsum_add hs2, he1, he2, lower_shift_back hEd hCE hEb hCG hGd hGb,
    upper_shift_back hEd hCE hEb hCG hGd hGb]
  have i1 := integrable_line hEd hCE hEb hCG hGd hGb y 1 (Or.inl rfl)
  have i2 := integrable_line hEd hCE hEb hCG hGd hGb y (-1) (Or.inr rfl)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul] at i1 i2
  simp only [← sub_eq_add_neg] at i2
  rw [← integral_add i1 i2]

end

end RHTower.WeilRegular
