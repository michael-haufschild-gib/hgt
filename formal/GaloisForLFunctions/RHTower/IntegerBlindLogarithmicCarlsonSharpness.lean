import GaloisForLFunctions.RHTower.IntegerBlindLogarithmicCarlsonThreshold
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.HTGeometry.GammaReciprocalExpBound

/-!
# Sharpness of the logarithmic Carlson threshold for integer blindness

Call `w ∈ L¹(ℝ)` *blind* at the integers if `∫ w(t) n^{-it} dt = 0` for every `n ≥ 1`.  With
room `e^{(π/2)|t| − K|t|/log(|t|+3)}`, blindness forces `ŵ ≡ 0` when `K < π/2`
(`fourier_eq_zero_of_integerMoment_eq_zero_logRoom`).  This file proves the converse half.

**Theorem** (`exists_integerBlind_logRoom`, `logRoom_integerBlind_threshold`).  For every
`K > π/2` there is a continuous integrable `w`, blind at every integer, with
`∫ |w(t)| e^{(π/2)|t| − K|t|/log(|t|+3)} dt < ∞` and `ŵ ≢ 0`.  Hence `π/2` is the exact constant at
the scale `t/log t`.

**Construction.**  `F_c(z) = sin(π e^z) e^{−π c z e^z}` is entire and vanishes at `z = log n`.
On the strip `|Im z| ≤ π/2` with `cos(Im z) ≥ s`, `|F_c(z)| ≤ C(c,s) e^{−|Re z|}`, where
`log C(c,s) ≍ π c s e^{A/(cs)}` and `A = 1 + cπ/2` (left half-line: `sin(πe^z) ≍ πe^z`; right
half-line: `max_x e^x(A − Bx) = B e^{A/B − 1}`).  Put `w_c = 𝓕⁻(F_c(2π·))`, so that
`∫ w_c(t) e^{−itx} dt = F_c(x)`.  Shifting `∫ F_c(x) e^{ixt} dx` to `Im x = π/2 − δ` with
`δ = κ/log(t+3)` gives

`|w_c(t)| e^{(π/2)t − Kt/log(t+3)} ≤ Q exp(D(t+3)^θ + 2θ log(t+3) − (K − κ)t/log(t+3))`

with `θ = A/(cκ)`.  The choice `c = 4/(K − π/2)`, `κ = (K + π/2)/2` gives `θ < 1` and
`κ < K`, so the right side is `O((1+t²)^{-1})`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform Real

noncomputable section

namespace RHTower.PrimeBlindCarlson

/-- The extremal entire function `F_c(z) = sin(π e^z) e^{-π c z e^z}`. -/
def blindExtremal (c : ℝ) (z : ℂ) : ℂ :=
  Complex.sin ((π : ℂ) * cexp z) * cexp (-((π * c : ℝ) : ℂ) * (z * cexp z))

theorem differentiable_blindExtremal (c : ℝ) : Differentiable ℂ (blindExtremal c) := by
  unfold blindExtremal; fun_prop

theorem norm_sin_le_of_norm_le_half {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.sin w‖ ≤ 4 * ‖w‖ := by
  have hsin : Complex.sin w = cexp (w * I) * (cexp (-2 * w * I) - 1) * I / 2 := by
    rw [Complex.sin, mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  rw [hsin, norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h1 : ‖cexp (w * I)‖ ≤ 2 := by
    rw [Complex.norm_exp]
    have : (w * I).re = -w.im := by simp
    rw [this]
    have him : -w.im ≤ 1 / 2 := (neg_le_abs w.im).trans ((Complex.abs_im_le_norm w).trans hw)
    calc Real.exp (-w.im) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr him
      _ ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h := Real.exp_le_exp.mpr (show (1 / 2 : ℝ) ≤ 1 by norm_num)
        have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
  have h2 : ‖cexp (-2 * w * I) - 1‖ ≤ 4 * ‖w‖ := by
    have hn : ‖-2 * w * I‖ = 2 * ‖w‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_two]
    have h := Complex.norm_exp_sub_one_le (x := -2 * w * I) (by rw [hn]; linarith)
    rw [hn] at h; linarith
  calc ‖cexp (w * I)‖ * ‖cexp (-2 * w * I) - 1‖ / 2 ≤ 2 * (4 * ‖w‖) / 2 := by
        gcongr
    _ = 4 * ‖w‖ := by ring

theorem norm_blindExtremal_eq (c : ℝ) (z : ℂ) :
    ‖blindExtremal c z‖ = ‖Complex.sin ((π : ℂ) * cexp z)‖ *
      Real.exp (π * c * (Real.exp z.re * (z.im * Real.sin z.im - z.re * Real.cos z.im))) := by
  unfold blindExtremal
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, Complex.mul_im]
  ring

theorem norm_pi_mul_cexp (z : ℂ) : ‖(π : ℂ) * cexp z‖ = π * Real.exp z.re := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem im_pi_mul_cexp (z : ℂ) : ((π : ℂ) * cexp z).im = π * (Real.exp z.re * Real.sin z.im) := by
  simp [Complex.mul_im, Complex.exp_im]

theorem mul_sin_le_of_abs_le {y : ℝ} (hy : |y| ≤ π / 2) : y * Real.sin y ≤ π / 2 := by
  have h1 : |y * Real.sin y| ≤ |y| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one y)
  linarith [le_abs_self (y * Real.sin y)]

theorem cos_nonneg_of_abs_le {y : ℝ} (hy : |y| ≤ π / 2) : 0 ≤ Real.cos y :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩

/-- `M₀(c) = 4π e^{π+2} e^{πc(π/2+1)}`, the constant on the left half-line. -/
def blindLeftConst (c : ℝ) : ℝ :=
  4 * π * Real.exp (π + 2) * Real.exp (π * c * (π / 2 + 1))

theorem blindLeftConst_pos (c : ℝ) : 0 < blindLeftConst c := by
  unfold blindLeftConst; have := Real.pi_pos; positivity

theorem norm_sin_pi_mul_cexp_le_of_re_nonpos {z : ℂ} (hx : z.re ≤ 0) :
    ‖Complex.sin ((π : ℂ) * cexp z)‖ ≤ 4 * π * Real.exp (π + 2) * Real.exp z.re := by
  have hpi := Real.pi_pos
  have hex := Real.exp_pos z.re
  rcases le_or_gt z.re (-2) with h2 | h2
  · have hsmall : ‖(π : ℂ) * cexp z‖ ≤ 1 / 2 := by
      rw [norm_pi_mul_cexp]
      have he : Real.exp z.re ≤ Real.exp (-2) := Real.exp_le_exp.mpr h2
      have he2 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
      have hE : (7 : ℝ) ≤ Real.exp 2 := by
        have := Real.exp_one_gt_d9
        have hsq : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [hsq]; nlinarith
      have hp := Real.pi_lt_d2
      nlinarith [Real.exp_pos (-2)]
    have h := norm_sin_le_of_norm_le_half hsmall
    rw [norm_pi_mul_cexp] at h
    have h1 : (1 : ℝ) ≤ Real.exp (π + 2) := Real.one_le_exp (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * π * Real.exp z.re)
    nlinarith
  · have h := GaloisForLFunctions.HTGeometry.norm_sin_le_exp_abs_im ((π : ℂ) * cexp z)
    rw [im_pi_mul_cexp] at h
    have hle : |π * (Real.exp z.re * Real.sin z.im)| ≤ π := by
      rw [abs_mul, abs_of_pos hpi, abs_mul, abs_of_pos hex]
      have : Real.exp z.re ≤ 1 := Real.exp_le_one_iff.mpr hx
      have hs := Real.abs_sin_le_one z.im
      have : Real.exp z.re * |Real.sin z.im| ≤ 1 := by nlinarith [abs_nonneg (Real.sin z.im)]
      nlinarith
    have h3 : Real.exp π ≤ Real.exp (π + 2) * Real.exp z.re := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    calc ‖Complex.sin ((π : ℂ) * cexp z)‖ ≤ Real.exp π := h.trans (Real.exp_le_exp.mpr hle)
      _ ≤ Real.exp (π + 2) * Real.exp z.re := h3
      _ ≤ 4 * π * Real.exp (π + 2) * Real.exp z.re := by
          have : (1 : ℝ) ≤ 4 * π := by nlinarith [Real.pi_gt_three]
          have h0 : 0 ≤ Real.exp (π + 2) * Real.exp z.re := by positivity
          nlinarith

/-- **Left half-line bound.**  For `Re z ≤ 0` and `|Im z| ≤ π/2`, `‖F_c(z)‖ ≤ M₀(c) e^{Re z}`. -/
theorem norm_blindExtremal_le_left {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hx : z.re ≤ 0)
    (hy : |z.im| ≤ π / 2) : ‖blindExtremal c z‖ ≤ blindLeftConst c * Real.exp z.re := by
  rw [norm_blindExtremal_eq]
  have hpi := Real.pi_pos
  have hs := norm_sin_pi_mul_cexp_le_of_re_nonpos hx
  have hexp : Real.exp (π * c * (Real.exp z.re * (z.im * Real.sin z.im - z.re * Real.cos z.im)))
      ≤ Real.exp (π * c * (π / 2 + 1)) := by
    apply Real.exp_le_exp.mpr
    have hys := mul_sin_le_of_abs_le hy
    have hcos := cos_nonneg_of_abs_le hy
    have hcos1 := Real.cos_le_one z.im
    have hex := Real.exp_pos z.re
    have hex1 : Real.exp z.re ≤ 1 := Real.exp_le_one_iff.mpr hx
    have hxe : Real.exp z.re * (-z.re) ≤ 1 := by
      have := Real.add_one_le_exp (-z.re)
      have hm : Real.exp z.re * Real.exp (-z.re) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have hin : Real.exp z.re * (z.im * Real.sin z.im - z.re * Real.cos z.im) ≤ π / 2 + 1 := by
      have h1 : z.im * Real.sin z.im - z.re * Real.cos z.im ≤ π / 2 + (-z.re) := by nlinarith
      calc Real.exp z.re * (z.im * Real.sin z.im - z.re * Real.cos z.im)
          ≤ Real.exp z.re * (π / 2 + (-z.re)) := mul_le_mul_of_nonneg_left h1 hex.le
        _ = Real.exp z.re * (π / 2) + Real.exp z.re * (-z.re) := by ring
        _ ≤ π / 2 + 1 := by nlinarith
    exact mul_le_mul_of_nonneg_left hin (by positivity)
  unfold blindLeftConst
  calc ‖Complex.sin ((π : ℂ) * cexp z)‖ *
        Real.exp (π * c * (Real.exp z.re * (z.im * Real.sin z.im - z.re * Real.cos z.im)))
      ≤ (4 * π * Real.exp (π + 2) * Real.exp z.re) * Real.exp (π * c * (π / 2 + 1)) :=
        mul_le_mul hs hexp (by positivity) (by positivity)
    _ = 4 * π * Real.exp (π + 2) * Real.exp (π * c * (π / 2 + 1)) * Real.exp z.re := by ring

/-- `A(c) = 1 + cπ/2`. -/
def blindA (c : ℝ) : ℝ := 1 + c * π / 2

/-- **Right half-line bound.**  For `0 ≤ Re z` and `|Im z| ≤ π/2`,
`‖F_c(z)‖ ≤ exp(π e^x (A(c) − c x cos y))`. -/
theorem norm_blindExtremal_le_right {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hy : |z.im| ≤ π / 2) :
    ‖blindExtremal c z‖ ≤
      Real.exp (π * Real.exp z.re * (blindA c - c * z.re * Real.cos z.im)) := by
  rw [norm_blindExtremal_eq]
  have hpi := Real.pi_pos
  have hex := Real.exp_pos z.re
  have hs := GaloisForLFunctions.HTGeometry.norm_sin_le_exp_abs_im ((π : ℂ) * cexp z)
  rw [im_pi_mul_cexp] at hs
  have hle : |π * (Real.exp z.re * Real.sin z.im)| ≤ π * Real.exp z.re := by
    rw [abs_mul, abs_of_pos hpi, abs_mul, abs_of_pos hex]
    have := Real.abs_sin_le_one z.im
    have : Real.exp z.re * |Real.sin z.im| ≤ Real.exp z.re := mul_le_of_le_one_right hex.le this
    nlinarith
  have hys := mul_sin_le_of_abs_le hy
  calc ‖Complex.sin ((π : ℂ) * cexp z)‖ *
        Real.exp (π * c * (Real.exp z.re * (z.im * Real.sin z.im - z.re * Real.cos z.im)))
      ≤ Real.exp (π * Real.exp z.re) *
          Real.exp (π * c * (Real.exp z.re * (π / 2 - z.re * Real.cos z.im))) := by
        apply mul_le_mul (hs.trans (Real.exp_le_exp.mpr hle)) _ (by positivity) (by positivity)
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hex.le
        linarith
    _ = Real.exp (π * Real.exp z.re * (blindA c - c * z.re * Real.cos z.im)) := by
        rw [← Real.exp_add]; unfold blindA; ring_nf

/-- `e^x (A − B x) ≤ B e^{A/B − 1}`. -/
theorem exp_mul_sub_le {A B : ℝ} (hB : 0 < B) (x : ℝ) :
    Real.exp x * (A - B * x) ≤ B * Real.exp (A / B - 1) := by
  have h := Real.add_one_le_exp (A / B - 1 - x)
  have hm : Real.exp x * Real.exp (A / B - 1 - x) = Real.exp (A / B - 1) := by
    rw [← Real.exp_add]; ring_nf
  have hex := Real.exp_pos x
  have hAB : A - B * x = B * (A / B - 1 - x + 1) := by field_simp; ring
  rw [hAB]
  calc Real.exp x * (B * (A / B - 1 - x + 1)) = B * (Real.exp x * (A / B - 1 - x + 1)) := by ring
    _ ≤ B * (Real.exp x * Real.exp (A / B - 1 - x)) := by gcongr
    _ = B * Real.exp (A / B - 1) := by rw [hm]

/-- Past `2A/B` the exponent `π e^x (A − Bx)` is below `−x`. -/
theorem pi_exp_mul_sub_le_neg {A B x : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (hx : 2 * A / B ≤ x) :
    π * Real.exp x * (A - B * x) ≤ -x := by
  have hpi := Real.pi_gt_three
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hBx : 2 * A ≤ B * x := by rw [div_le_iff₀ hB] at hx; linarith
  have hex : x + 1 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hBe : 2 ≤ B * Real.exp x := by nlinarith
  have h1 : A - B * x ≤ -(B * x) / 2 := by linarith
  have hE := Real.exp_pos x
  calc π * Real.exp x * (A - B * x) ≤ π * Real.exp x * (-(B * x) / 2) := by
        apply mul_le_mul_of_nonneg_left h1; positivity
    _ = -(x * (π * (B * Real.exp x) / 2)) := by ring
    _ ≤ -x := by
        have : 1 ≤ π * (B * Real.exp x) / 2 := by nlinarith
        nlinarith

/-- The strip constant `C(c, s) = M₀(c) + exp(π c s e^{A/(cs) − 1} + 2A/(cs))`. -/
def blindStripConst (c s : ℝ) : ℝ :=
  blindLeftConst c + Real.exp (π * (c * s) * Real.exp (blindA c / (c * s) - 1) +
    2 * blindA c / (c * s))

/-- **Strip bound.**  If `|Im z| ≤ π/2` and `cos(Im z) ≥ s > 0`, then `‖F_c(z)‖ ≤ C(c,s) e^{-|Re z|}`. -/
theorem norm_blindExtremal_le_strip {c s : ℝ} (hc : 0 < c) (hs : 0 < s) {z : ℂ}
    (hy : |z.im| ≤ π / 2) (hcos : s ≤ Real.cos z.im) :
    ‖blindExtremal c z‖ ≤ blindStripConst c s * Real.exp (-|z.re|) := by
  have hpi := Real.pi_pos
  have hE : 0 < Real.exp (π * (c * s) * Real.exp (blindA c / (c * s) - 1) +
      2 * blindA c / (c * s)) := Real.exp_pos _
  have hA : 1 ≤ blindA c := by unfold blindA; have := hc.le; nlinarith
  rcases le_or_gt z.re 0 with hx | hx
  · have h := norm_blindExtremal_le_left hc.le hx hy
    rw [abs_of_nonpos hx, neg_neg]
    unfold blindStripConst
    have := Real.exp_pos z.re
    nlinarith
  · have h := norm_blindExtremal_le_right hc.le hy
    have hB : 0 < c * s := mul_pos hc hs
    have hmono : π * Real.exp z.re * (blindA c - c * z.re * Real.cos z.im) ≤
        π * Real.exp z.re * (blindA c - c * s * z.re) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : c * s * z.re ≤ c * z.re * Real.cos z.im := by
        have := mul_le_mul_of_nonneg_left hcos (mul_nonneg hc.le hx.le); nlinarith
      linarith
    rw [abs_of_pos hx]
    unfold blindStripConst
    rcases le_or_gt (2 * blindA c / (c * s)) z.re with hbig | hsmall
    · have ht := pi_exp_mul_sub_le_neg hA hB hbig
      have : ‖blindExtremal c z‖ ≤ Real.exp (-z.re) :=
        h.trans (Real.exp_le_exp.mpr (hmono.trans ht))
      have h1 : (1 : ℝ) ≤ Real.exp (π * (c * s) * Real.exp (blindA c / (c * s) - 1) +
          2 * blindA c / (c * s)) := Real.one_le_exp (by positivity)
      have := blindLeftConst_pos c
      have := Real.exp_pos (-z.re)
      nlinarith
    · have hmax := exp_mul_sub_le hB (A := blindA c) z.re
      have hexp : π * Real.exp z.re * (blindA c - c * s * z.re) ≤
          π * (c * s) * Real.exp (blindA c / (c * s) - 1) := by
        have := mul_le_mul_of_nonneg_left hmax hpi.le; linarith
      have : ‖blindExtremal c z‖ ≤ Real.exp (π * (c * s) * Real.exp (blindA c / (c * s) - 1) +
          2 * blindA c / (c * s) + -z.re) := by
        refine h.trans (Real.exp_le_exp.mpr ?_)
        linarith
      rw [Real.exp_add] at this
      have := blindLeftConst_pos c
      have := Real.exp_pos (-z.re)
      nlinarith

/-- `∫ e^{-|x|} dx`, the total mass of the strip majorant. -/
def blindMass : ℝ := ∫ x : ℝ, Real.exp (-(1 * |x|))

theorem blindMass_nonneg : 0 ≤ blindMass :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- The oscillatory line integral `∫ F_c(x) e^{ixt} dx`. -/
def blindLine (c t : ℝ) : ℂ := ∫ x : ℝ, blindExtremal c x * cexp (I * x * t)

theorem cos_le_cos_im_of_abs_le {z : ℂ} {y₀ : ℝ} (hy₀ : y₀ ≤ π) (hz : |z.im| ≤ y₀) :
    Real.cos y₀ ≤ Real.cos z.im := by
  rw [← Real.cos_abs z.im]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hy₀ hz

/-- **Contour shift.**  For `t ≥ 0` and `0 ≤ y₀ ≤ π/2` with `cos y₀ ≥ s > 0`,
`‖∫ F_c(x) e^{ixt} dx‖ ≤ C(c,s) · (∫ e^{-|x|}) · e^{-t y₀}`. -/
theorem norm_blindLine_le {c s y₀ t : ℝ} (hc : 0 < c) (hs : 0 < s) (hy₀ : 0 ≤ y₀)
    (hy₀' : y₀ ≤ π / 2) (hcos : s ≤ Real.cos y₀) (ht : 0 ≤ t) :
    ‖blindLine c t‖ ≤ blindStripConst c s * blindMass * Real.exp (-(t * y₀)) := by
  have hpi := Real.pi_pos
  set Φ : ℂ → ℂ := fun z => blindExtremal c z * cexp (I * z * t) with hΦ
  have hΦd : ∀ z : ℂ, |z.im| ≤ y₀ → DifferentiableAt ℂ Φ z := fun z _ =>
    ((differentiable_blindExtremal c) z).mul (by fun_prop)
  have hexpI : ∀ z : ℂ, ‖cexp (I * z * t)‖ = Real.exp (-(t * z.im)) := by
    intro z; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]; ring
  have hstrip : ∀ z : ℂ, |z.im| ≤ y₀ →
      ‖blindExtremal c z‖ ≤ blindStripConst c s * Real.exp (-|z.re|) := fun z hz =>
    norm_blindExtremal_le_strip hc hs (hz.trans hy₀')
      (hcos.trans (cos_le_cos_im_of_abs_le (by linarith) hz))
  have hC0 : 0 ≤ blindStripConst c s := by
    unfold blindStripConst; have := blindLeftConst_pos c; positivity
  have hbound : ∀ z : ℂ, |z.im| ≤ y₀ →
      ‖Φ z‖ ≤ (blindStripConst c s * Real.exp (t * y₀)) * Real.exp (-(1 * |z.re|)) := by
    intro z hz
    rw [hΦ]; simp only
    rw [norm_mul, hexpI]
    have h1 := hstrip z hz
    have h2 : Real.exp (-(t * z.im)) ≤ Real.exp (t * y₀) := by
      apply Real.exp_le_exp.mpr
      have : -z.im ≤ y₀ := (neg_le_abs z.im).trans hz
      nlinarith
    rw [one_mul]
    calc ‖blindExtremal c z‖ * Real.exp (-(t * z.im))
        ≤ (blindStripConst c s * Real.exp (-|z.re|)) * Real.exp (t * y₀) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = blindStripConst c s * Real.exp (t * y₀) * Real.exp (-|z.re|) := by ring
  have hshift := integral_horizontal_shift_of_decay hy₀ one_pos hΦd hbound
  have hline : blindLine c t = ∫ x : ℝ, Φ ((x : ℂ) + (y₀ : ℂ) * I) := by
    rw [hshift]; rfl
  rw [hline]
  have hint : Integrable (fun x : ℝ => blindStripConst c s * Real.exp (-(1 * |x|)) *
      Real.exp (-(t * y₀))) :=
    ((integrable_exp_neg_mul_abs' one_pos).const_mul _).mul_const _
  calc ‖∫ x : ℝ, Φ ((x : ℂ) + (y₀ : ℂ) * I)‖
      ≤ ∫ x : ℝ, blindStripConst c s * Real.exp (-(1 * |x|)) * Real.exp (-(t * y₀)) := by
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)
        rw [hΦ]; simp only
        rw [norm_mul, hexpI]
        have hz : |((x : ℂ) + (y₀ : ℂ) * I).im| ≤ y₀ := by simp [abs_of_nonneg hy₀]
        have h1 := hstrip _ hz
        have hre : ((x : ℂ) + (y₀ : ℂ) * I).re = x := by simp
        have him : ((x : ℂ) + (y₀ : ℂ) * I).im = y₀ := by simp
        rw [hre] at h1; rw [him, one_mul]
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = blindStripConst c s * blindMass * Real.exp (-(t * y₀)) := by
        rw [integral_mul_const, integral_const_mul]; rfl

theorem one_div_sin_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 / Real.sin δ ≤ 1 / δ + 1 / 3 := by
  have h := Real.sin_gt_sub_cube hδ
  have h3 : δ ^ 3 ≤ δ := by
    have : δ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hspos : 0 < Real.sin δ := by linarith
  rw [div_le_iff₀ hspos]
  have hkey : 3 * δ ≤ (3 + δ) * Real.sin δ := by
    have h1 : 3 * δ ≤ (3 + δ) * (δ - δ ^ 3 / 6) := by nlinarith [sq_nonneg δ, pow_pos hδ 3]
    nlinarith
  have : (1 / δ + 1 / 3) * Real.sin δ = (3 + δ) * Real.sin δ / (3 * δ) := by field_simp
  rw [this, le_div_iff₀ (by positivity)]
  linarith

/-- Exponent of the Gamma-side growth: `θ = A(c)/(cκ)`. -/
def blindTheta (c κ : ℝ) : ℝ := blindA c / (c * κ)

/-- `D = π c e^{A/(3c) − 1}`. -/
def blindD (c : ℝ) : ℝ := π * c * Real.exp (blindA c / (3 * c) - 1)

/-- **The optimized contour bound.**  With `δ = κ/log(t+3)`,
`‖∫ F_c e^{ixt}‖ · e^{(π/2)t − Kt/log(t+3)} ≤ Q e^{D(t+3)^θ + 2θ log(t+3) + 2A/(3c) − (K−κ)t/log(t+3)}`. -/
theorem norm_blindLine_mul_logRoom_le {c κ K t : ℝ} (hc : 0 < c) (hκ : 0 < κ) (ht : 0 ≤ t)
    (hL : κ ≤ Real.log (t + 3)) :
    ‖blindLine c t‖ * logRoomWeight K t ≤
      (blindLeftConst c + 1) * blindMass *
        Real.exp (blindD c * (t + 3) ^ blindTheta c κ + 2 * blindTheta c κ * Real.log (t + 3) +
          2 * blindA c / (3 * c) - (K - κ) * t / Real.log (t + 3)) := by
  have hpi := Real.pi_pos
  set L := Real.log (t + 3) with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le hκ hL
  set δ := κ / L with hδdef
  have hδ0 : 0 < δ := div_pos hκ hL0
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hL0]; exact hL
  have hsin0 : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith [Real.pi_gt_three])
  have hsin1 : Real.sin δ ≤ 1 := Real.sin_le_one δ
  have hy0 : 0 ≤ π / 2 - δ := by linarith [Real.pi_gt_three]
  have hcosy : Real.sin δ ≤ Real.cos (π / 2 - δ) := by rw [Real.cos_pi_div_two_sub]
  have hmain := norm_blindLine_le hc hsin0 hy0 (by linarith) hcosy ht
  set A := blindA c with hAdef
  have hA : 1 ≤ A := by rw [hAdef]; unfold blindA; nlinarith
  -- `A/(c sin δ) ≤ θ L + A/(3c)`
  have hinv := one_div_sin_le hδ0 hδ1
  have hAB : A / (c * Real.sin δ) ≤ blindTheta c κ * L + A / (3 * c) := by
    have e1 : A / (c * Real.sin δ) = (A / c) * (1 / Real.sin δ) := by field_simp
    have e2 : blindTheta c κ * L + A / (3 * c) = (A / c) * (1 / δ + 1 / 3) := by
      unfold blindTheta; rw [hδdef]; field_simp; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hcs : c * Real.sin δ ≤ c := by nlinarith
  have hpow : Real.exp (blindTheta c κ * L) = (t + 3) ^ blindTheta c κ := by
    rw [hLdef, Real.rpow_def_of_pos (by linarith), mul_comm]
  have hterm1 : π * (c * Real.sin δ) * Real.exp (A / (c * Real.sin δ) - 1) ≤
      blindD c * (t + 3) ^ blindTheta c κ := by
    unfold blindD
    rw [← hAdef, ← hpow]
    have h1 : Real.exp (A / (c * Real.sin δ) - 1) ≤
        Real.exp (blindTheta c κ * L) * Real.exp (A / (3 * c) - 1) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    calc π * (c * Real.sin δ) * Real.exp (A / (c * Real.sin δ) - 1)
        ≤ π * c * (Real.exp (blindTheta c κ * L) * Real.exp (A / (3 * c) - 1)) := by
          have hc' : π * (c * Real.sin δ) ≤ π * c := by nlinarith
          exact mul_le_mul hc' h1 (Real.exp_pos _).le (by positivity)
      _ = π * c * Real.exp (A / (3 * c) - 1) * Real.exp (blindTheta c κ * L) := by ring
  have hterm2 : 2 * A / (c * Real.sin δ) ≤ 2 * blindTheta c κ * L + 2 * A / (3 * c) := by
    have e1 : 2 * A / (c * Real.sin δ) = 2 * (A / (c * Real.sin δ)) := by ring
    have e2 : 2 * A / (3 * c) = 2 * (A / (3 * c)) := by ring
    rw [e1, e2]; linarith
  have hC : blindStripConst c (Real.sin δ) ≤ (blindLeftConst c + 1) *
      Real.exp (blindD c * (t + 3) ^ blindTheta c κ + 2 * blindTheta c κ * L + 2 * A / (3 * c)) := by
    unfold blindStripConst
    rw [← hAdef]
    have hE : Real.exp (π * (c * Real.sin δ) * Real.exp (A / (c * Real.sin δ) - 1) +
        2 * A / (c * Real.sin δ)) ≤ Real.exp (blindD c * (t + 3) ^ blindTheta c κ +
          2 * blindTheta c κ * L + 2 * A / (3 * c)) := Real.exp_le_exp.mpr (by linarith)
    have h1 : (1 : ℝ) ≤ Real.exp (blindD c * (t + 3) ^ blindTheta c κ +
          2 * blindTheta c κ * L + 2 * A / (3 * c)) := by
      apply Real.one_le_exp
      have : 0 ≤ blindD c := by unfold blindD; positivity
      have : 0 ≤ blindTheta c κ := by unfold blindTheta; rw [← hAdef]; positivity
      have : 0 ≤ L := hL0.le
      positivity
    have := blindLeftConst_pos c
    nlinarith
  have hroom : logRoomWeight K t = Real.exp (π / 2 * t - K * t / L) := by
    unfold logRoomWeight; rw [abs_of_nonneg ht, hLdef]
  rw [hroom]
  have hmass := blindMass_nonneg
  calc ‖blindLine c t‖ * Real.exp (π / 2 * t - K * t / L)
      ≤ (blindStripConst c (Real.sin δ) * blindMass * Real.exp (-(t * (π / 2 - δ)))) *
          Real.exp (π / 2 * t - K * t / L) :=
        mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
    _ ≤ ((blindLeftConst c + 1) * Real.exp (blindD c * (t + 3) ^ blindTheta c κ +
          2 * blindTheta c κ * L + 2 * A / (3 * c)) * blindMass * Real.exp (-(t * (π / 2 - δ)))) *
          Real.exp (π / 2 * t - K * t / L) := by gcongr
    _ = (blindLeftConst c + 1) * blindMass *
        Real.exp (blindD c * (t + 3) ^ blindTheta c κ + 2 * blindTheta c κ * L +
          2 * A / (3 * c) - (K - κ) * t / L) := by
        have : t * δ = κ * t / L := by rw [hδdef]; ring
        have e : blindD c * (t + 3) ^ blindTheta c κ + 2 * blindTheta c κ * L + 2 * A / (3 * c) -
              (K - κ) * t / L =
            (blindD c * (t + 3) ^ blindTheta c κ + 2 * blindTheta c κ * L + 2 * A / (3 * c)) +
            (-(t * (π / 2 - δ))) + (π / 2 * t - K * t / L) := by
          rw [show -(t * (π / 2 - δ)) = t * δ - π / 2 * t by ring, this]
          ring
        rw [e]
        generalize blindD c * (t + 3) ^ blindTheta c κ + 2 * blindTheta c κ * L + 2 * A / (3 * c) = X
        rw [Real.exp_add, Real.exp_add]; ring

theorem tendsto_log_shift_pow_div (n : ℕ) :
    Tendsto (fun t : ℝ => Real.log (t + 3) ^ n / t) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-3) n one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop 3 tendsto_id)
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [Function.comp, id]
  congr 1; ring

theorem tendsto_rpow_log_shift_div {θ : ℝ} (hθ : θ < 1) :
    Tendsto (fun t : ℝ => (t + 3) ^ θ * Real.log (t + 3) / t) atTop (𝓝 0) := by
  have hr : 0 < 1 - θ := by linarith
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 - θ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have hshift : Tendsto (fun t : ℝ => t + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3 tendsto_id
  have h2 : Tendsto (fun t : ℝ => Real.log (t + 3) / (t + 3) ^ (1 - θ)) atTop (𝓝 0) :=
    h1.comp hshift
  have h3 : Tendsto (fun t : ℝ => (t + 3) / t) atTop (𝓝 1) := by
    have : Tendsto (fun t : ℝ => 1 + 3 * t⁻¹) atTop (𝓝 (1 + 3 * 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul 3)
    rw [show (1 : ℝ) + 3 * 0 = 1 by ring] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    field_simp
  have h4 := h2.mul h3
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hp : 0 < t + 3 := by linarith
  have hsplit : (t + 3) ^ θ = (t + 3) / (t + 3) ^ (1 - θ) := by
    rw [Real.rpow_sub hp, Real.rpow_one]; field_simp
  rw [hsplit]
  field_simp

/-- For `θ < 1` and `a > 0`, eventually
`Q + D(t+3)^θ + P log(t+3) + log(1+t²) ≤ a t / log(t+3)`. -/
theorem eventually_le_mul_div_log {θ Q D P a : ℝ} (hθ : θ < 1) (ha : 0 < a) :
    ∀ᶠ t : ℝ in atTop, Q + D * (t + 3) ^ θ + P * Real.log (t + 3) + Real.log (1 + t ^ 2) ≤
      a * t / Real.log (t + 3) := by
  have h1 := tendsto_log_shift_pow_div 1
  have h2 := tendsto_log_shift_pow_div 2
  have h3 := tendsto_rpow_log_shift_div hθ
  have h4 : Tendsto (fun t : ℝ => Real.log (1 + t ^ 2) * Real.log (t + 3) / t) atTop (𝓝 0) := by
    have hup : Tendsto (fun t : ℝ => 2 * (Real.log (t + 3) ^ 2 / t)) atTop (𝓝 0) := by
      simpa using h2.const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith)
      have : 0 ≤ Real.log (t + 3) := Real.log_nonneg (by linarith)
      positivity
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hl : Real.log (1 + t ^ 2) ≤ 2 * Real.log (t + 3) := by
        rw [← Real.log_rpow (by linarith)]
        exact Real.log_le_log (by positivity) (by norm_num; nlinarith)
      have hL : 0 ≤ Real.log (t + 3) := Real.log_nonneg (by linarith)
      rw [div_le_iff₀ ht]
      have : 2 * (Real.log (t + 3) ^ 2 / t) * t = 2 * Real.log (t + 3) ^ 2 := by field_simp
      rw [this]; nlinarith
  have hsum : Tendsto (fun t : ℝ => (Q + D * (t + 3) ^ θ + P * Real.log (t + 3) +
      Real.log (1 + t ^ 2)) * Real.log (t + 3) / t) atTop (𝓝 0) := by
    have := ((h1.const_mul Q).add (h3.const_mul D)).add ((h2.const_mul P).add h4)
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [pow_one]
    ring
  filter_upwards [hsum.eventually (gt_mem_nhds ha), eventually_gt_atTop 0] with t ht ht0
  have hL : 0 < Real.log (t + 3) := Real.log_pos (by linarith)
  rw [div_lt_iff₀ ht0] at ht
  rw [le_div_iff₀ hL]
  nlinarith

theorem blindExtremal_ofReal (c x : ℝ) :
    blindExtremal c x =
      ((Real.sin (π * Real.exp x) * Real.exp (-(π * c) * (x * Real.exp x)) : ℝ) : ℂ) := by
  unfold blindExtremal
  push_cast
  ring_nf

theorem conj_blindExtremal_ofReal (c x : ℝ) :
    (starRingEnd ℂ) (blindExtremal c x) = blindExtremal c x := by
  rw [blindExtremal_ofReal, Complex.conj_ofReal]

theorem norm_blindExtremal_ofReal_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ‖blindExtremal c x‖ ≤ blindStripConst c 1 * Real.exp (-(1 * |x|)) := by
  have h := norm_blindExtremal_le_strip hc one_pos (z := (x : ℂ)) (by simp; positivity)
    (by simp)
  simpa using h

theorem integrable_blindExtremal_ofReal {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => blindExtremal c x) := by
  refine ((integrable_exp_neg_mul_abs' one_pos).const_mul (blindStripConst c 1)).mono'
    ((differentiable_blindExtremal c).continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_blindExtremal_ofReal_le hc x)

theorem norm_cexp_I_mul_mul (x t : ℝ) : ‖cexp (I * x * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem continuous_blindLine {c : ℝ} (hc : 0 < c) : Continuous (blindLine c) := by
  unfold blindLine
  refine continuous_of_dominated (bound := fun x : ℝ => ‖blindExtremal c x‖) ?_ ?_
    (integrable_blindExtremal_ofReal hc).norm ?_
  · intro t
    exact (((differentiable_blindExtremal c).continuous.comp Complex.continuous_ofReal).mul
      (by fun_prop)).aestronglyMeasurable
  · intro t
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, norm_cexp_I_mul_mul, mul_one]
  · exact Eventually.of_forall fun x => by fun_prop

theorem norm_blindLine_le_mass (c t : ℝ) :
    ‖blindLine c t‖ ≤ ∫ x : ℝ, ‖blindExtremal c x‖ := by
  unfold blindLine
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x; rw [norm_mul, norm_cexp_I_mul_mul, mul_one]

theorem blindLine_neg (c t : ℝ) : blindLine c (-t) = (starRingEnd ℂ) (blindLine c t) := by
  unfold blindLine
  rw [← integral_conj]
  congr 1; funext x
  rw [map_mul, conj_blindExtremal_ofReal, ← Complex.exp_conj]
  congr 2
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

theorem norm_blindLine_neg (c t : ℝ) : ‖blindLine c (-t)‖ = ‖blindLine c t‖ := by
  rw [blindLine_neg, Complex.norm_conj]

theorem norm_blindLine_abs (c t : ℝ) : ‖blindLine c |t|‖ = ‖blindLine c t‖ := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, norm_blindLine_neg]

/-- The profile `ξ ↦ F_c(2πξ)` in the Fourier normalization of mathlib. -/
def blindProfile (c : ℝ) (ξ : ℝ) : ℂ := blindExtremal c ((2 * π * ξ : ℝ) : ℂ)

/-- **The integer-blind witness** `w_c = 𝓕⁻(F_c(2π·))`, i.e. `w_c(t) = (2π)⁻¹ ∫ F_c(x) e^{ixt} dx`. -/
def blindWitness (c : ℝ) : ℝ → ℂ := 𝓕⁻ (blindProfile c)

theorem continuous_blindProfile (c : ℝ) : Continuous (blindProfile c) :=
  (differentiable_blindExtremal c).continuous.comp (by fun_prop)

theorem integrable_blindProfile {c : ℝ} (hc : 0 < c) : Integrable (blindProfile c) := by
  have h := (integrable_blindExtremal_ofReal hc).comp_mul_left'
    (show (2 * π : ℝ) ≠ 0 by positivity)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp [blindProfile]

theorem blindWitness_eq {c : ℝ} (t : ℝ) :
    blindWitness c t = (((2 * π)⁻¹ : ℝ) : ℂ) * blindLine c t := by
  unfold blindWitness
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  unfold blindLine
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => blindExtremal c x * cexp (I * x * t)) (2 * π)
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)] at h
  rw [← Complex.real_smul, ← h]
  congr 1; funext v
  simp only [smul_eq_mul, blindProfile]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem norm_blindWitness_eq {c : ℝ} (t : ℝ) :
    ‖blindWitness c t‖ = (2 * π)⁻¹ * ‖blindLine c t‖ := by
  rw [blindWitness_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]

theorem continuous_blindWitness {c : ℝ} (hc : 0 < c) : Continuous (blindWitness c) := by
  have : blindWitness c = fun t => (((2 * π)⁻¹ : ℝ) : ℂ) * blindLine c t := funext blindWitness_eq
  rw [this]
  exact continuous_const.mul (continuous_blindLine hc)

theorem logRoomWeight_abs (K t : ℝ) : logRoomWeight K |t| = logRoomWeight K t := by
  unfold logRoomWeight; rw [abs_abs]

theorem logRoomWeight_le_of_abs_le {K T t : ℝ} (hK : 0 ≤ K) (ht : |t| ≤ T) :
    logRoomWeight K t ≤ Real.exp (π / 2 * T) := by
  unfold logRoomWeight
  apply Real.exp_le_exp.mpr
  have hL : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
  have : 0 ≤ K * |t| / Real.log (|t| + 3) := div_nonneg (mul_nonneg hK (abs_nonneg t)) hL.le
  have := Real.pi_pos
  nlinarith

theorem one_le_logRoomWeight {K t : ℝ} (hK : 0 < K) (ht : 2 * K / π ≤ Real.log (|t| + 3)) :
    1 ≤ logRoomWeight K t := by
  unfold logRoomWeight
  apply Real.one_le_exp
  have hpi := Real.pi_pos
  have hL : 0 < Real.log (|t| + 3) := lt_of_lt_of_le (by positivity) ht
  have h : K * |t| / Real.log (|t| + 3) ≤ π / 2 * |t| := by
    rw [div_le_iff₀ hL]
    have h2 : 2 * K ≤ π * Real.log (|t| + 3) := by rw [div_le_iff₀ hpi] at ht; linarith
    nlinarith [abs_nonneg t]
  linarith

/-- The parameters `c = 4/(K − π/2)` and `κ = (K + π/2)/2` used for a given `K > π/2`. -/
theorem blindTheta_lt_one {K : ℝ} (hK : π / 2 < K) :
    blindTheta (4 / (K - π / 2)) ((K + π / 2) / 2) < 1 := by
  have hd : 0 < K - π / 2 := by linarith
  have hc : 0 < 4 / (K - π / 2) := by positivity
  have hκ : 0 < (K + π / 2) / 2 := by have := Real.pi_pos; linarith
  unfold blindTheta blindA
  rw [div_lt_one (mul_pos hc hκ)]
  have e : 4 / (K - π / 2) * ((K + π / 2) / 2) = 4 / (K - π / 2) * (π / 2) + 2 := by
    have e' : ∀ d : ℝ, d ≠ 0 → 4 / d * ((d + π) / 2) = 4 / d * (π / 2) + 2 := by
      intro d hd0; field_simp; ring
    rw [show K + π / 2 = (K - π / 2) + π by ring]
    exact e' _ hd.ne'
  rw [e]
  have : 4 / (K - π / 2) * π / 2 = 4 / (K - π / 2) * (π / 2) := by ring
  linarith

/-- **Uniform bound for the line integral against the room weight.**  For `K > π/2` there is a
`C` with `‖∫ F_c e^{ixt}‖ · e^{(π/2)|t| − K|t|/log(|t|+3)} ≤ C/(1+t²)` and
`‖∫ F_c e^{ixt}‖ ≤ C/(1+t²)` for every real `t`, where `c = 4/(K − π/2)`. -/
theorem exists_blindLine_room_bound {K : ℝ} (hK : π / 2 < K) :
    ∃ C : ℝ, ∀ t : ℝ,
      ‖blindLine (4 / (K - π / 2)) t‖ * logRoomWeight K t ≤ C * (1 + t ^ 2)⁻¹ ∧
      ‖blindLine (4 / (K - π / 2)) t‖ ≤ C * (1 + t ^ 2)⁻¹ := by
  have hpi := Real.pi_pos
  set c := 4 / (K - π / 2) with hcdef
  set κ := (K + π / 2) / 2 with hκdef
  have hd : 0 < K - π / 2 := by linarith
  have hc : 0 < c := by positivity
  have hκ : 0 < κ := by linarith
  have hK0 : 0 < K := by linarith
  have hθ := blindTheta_lt_one hK
  rw [← hcdef, ← hκdef] at hθ
  have hKκ : 0 < K - κ := by rw [hκdef]; linarith
  set Q : ℝ := (blindLeftConst c + 1) * blindMass + 2 * blindA c / (3 * c) with hQ
  have hev := (eventually_le_mul_div_log (Q := Q) (D := blindD c) (P := 2 * blindTheta c κ)
    hθ hKκ).and ((eventually_ge_atTop (Real.exp κ - 3)).and
      ((eventually_ge_atTop (Real.exp (2 * K / π) - 3)).and (eventually_ge_atTop 0)))
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
  set T := max T₀ 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  -- the tail bound for `t ≥ T`
  have htail : ∀ t : ℝ, T ≤ t →
      ‖blindLine c t‖ * logRoomWeight K t ≤ (1 + t ^ 2)⁻¹ ∧ 1 ≤ logRoomWeight K t := by
    intro t ht
    obtain ⟨h3, hκt, hKt, ht0⟩ := hT₀ t ((le_max_left _ _).trans ht)
    have hL3 : 0 < t + 3 := by linarith
    have hκL : κ ≤ Real.log (t + 3) := by
      rw [Real.le_log_iff_exp_le hL3]; linarith
    have hKL : 2 * K / π ≤ Real.log (|t| + 3) := by
      rw [abs_of_nonneg ht0, Real.le_log_iff_exp_le hL3]; linarith
    refine ⟨?_, one_le_logRoomWeight hK0 hKL⟩
    have hb := norm_blindLine_mul_logRoom_le (K := K) hc hκ ht0 hκL
    have hm : 0 ≤ (blindLeftConst c + 1) * blindMass := by
      have := blindLeftConst_pos c; have := blindMass_nonneg; positivity
    have hexp := Real.add_one_le_exp ((blindLeftConst c + 1) * blindMass)
    set X := blindD c * (t + 3) ^ blindTheta c κ + 2 * blindTheta c κ * Real.log (t + 3) +
      2 * blindA c / (3 * c) - (K - κ) * t / Real.log (t + 3) with hX
    have h1 : (blindLeftConst c + 1) * blindMass * Real.exp X ≤
        Real.exp ((blindLeftConst c + 1) * blindMass) * Real.exp X :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have h2 : Real.exp ((blindLeftConst c + 1) * blindMass) * Real.exp X ≤ (1 + t ^ 2)⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_log (by positivity : (0 : ℝ) < 1 + t ^ 2), ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      rw [hX]
      linarith
    exact hb.trans (h1.trans h2)
  -- the compact part
  set W₀ := ∫ x : ℝ, ‖blindExtremal c x‖ with hW₀
  have hW₀0 : 0 ≤ W₀ := integral_nonneg fun _ => norm_nonneg _
  refine ⟨1 + W₀ * Real.exp (π / 2 * T) * (1 + T ^ 2), fun t => ?_⟩
  have hC1 : 1 ≤ 1 + W₀ * Real.exp (π / 2 * T) * (1 + T ^ 2) := by
    have : 0 ≤ W₀ * Real.exp (π / 2 * T) * (1 + T ^ 2) := by positivity
    linarith
  have hinv0 : 0 < (1 + t ^ 2)⁻¹ := by positivity
  rcases le_or_gt T |t| with hbig | hsmall
  · obtain ⟨h1, h2⟩ := htail |t| hbig
    rw [norm_blindLine_abs, logRoomWeight_abs, sq_abs] at h1
    have hroom := logRoomWeight_nonneg K t
    rw [logRoomWeight_abs] at h2
    constructor
    · calc ‖blindLine c t‖ * logRoomWeight K t ≤ (1 + t ^ 2)⁻¹ := h1
        _ ≤ (1 + W₀ * Real.exp (π / 2 * T) * (1 + T ^ 2)) * (1 + t ^ 2)⁻¹ := by nlinarith
    · calc ‖blindLine c t‖ ≤ ‖blindLine c t‖ * logRoomWeight K t :=
            le_mul_of_one_le_right (norm_nonneg _) h2
        _ ≤ (1 + t ^ 2)⁻¹ := h1
        _ ≤ (1 + W₀ * Real.exp (π / 2 * T) * (1 + T ^ 2)) * (1 + t ^ 2)⁻¹ := by nlinarith
  · have hl := norm_blindLine_le_mass c t
    rw [← hW₀] at hl
    have hroom := logRoomWeight_le_of_abs_le hK0.le hsmall.le
    have hroom0 := logRoomWeight_nonneg K t
    have hE1 : 1 ≤ Real.exp (π / 2 * T) := Real.one_le_exp (by positivity)
    have ht2 : t ^ 2 ≤ T ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) hsmall.le 2
    have hfac : 1 ≤ (1 + T ^ 2) * (1 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
    have key : W₀ * Real.exp (π / 2 * T) ≤
        (1 + W₀ * Real.exp (π / 2 * T) * (1 + T ^ 2)) * (1 + t ^ 2)⁻¹ := by
      have h0 : 0 ≤ W₀ * Real.exp (π / 2 * T) := by positivity
      calc W₀ * Real.exp (π / 2 * T) ≤ W₀ * Real.exp (π / 2 * T) * ((1 + T ^ 2) * (1 + t ^ 2)⁻¹) :=
            le_mul_of_one_le_right h0 hfac
        _ ≤ (1 + W₀ * Real.exp (π / 2 * T) * (1 + T ^ 2)) * (1 + t ^ 2)⁻¹ := by nlinarith
    constructor
    · calc ‖blindLine c t‖ * logRoomWeight K t ≤ W₀ * Real.exp (π / 2 * T) :=
            mul_le_mul hl hroom hroom0 hW₀0
        _ ≤ _ := key
    · calc ‖blindLine c t‖ ≤ W₀ * Real.exp (π / 2 * T) := by nlinarith
        _ ≤ _ := key

theorem continuous_logRoomWeight (K : ℝ) : Continuous (logRoomWeight K) := by
  unfold logRoomWeight
  refine Real.continuous_exp.comp ((continuous_const.mul continuous_abs).sub ?_)
  refine (continuous_const.mul continuous_abs).div ?_ fun t =>
    (Real.log_pos (by linarith [abs_nonneg t])).ne'
  exact (continuous_abs.add continuous_const).log fun t => by
    show |t| + 3 ≠ 0; positivity

theorem integrable_blindWitness_room {K : ℝ} (hK : π / 2 < K) :
    Integrable (blindWitness (4 / (K - π / 2))) ∧
      Integrable fun t => ‖blindWitness (4 / (K - π / 2)) t‖ * logRoomWeight K t := by
  have hpi := Real.pi_pos
  have hd : 0 < K - π / 2 := by linarith
  have hc : 0 < 4 / (K - π / 2) := by positivity
  obtain ⟨C, hC⟩ := exists_blindLine_room_bound hK
  have hcont := continuous_blindWitness hc
  have hmaj : Integrable fun t : ℝ => (2 * π)⁻¹ * C * (1 + t ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  constructor
  · refine hmaj.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_blindWitness_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC t).2 (by positivity)
  · refine hmaj.mono' ((hcont.norm.mul (continuous_logRoomWeight K)).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (logRoomWeight_nonneg K t)),
      norm_blindWitness_eq, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC t).1 (by positivity)

/-- **Fourier inversion for the witness.**  `𝓕 w_c = F_c(2π·)`. -/
theorem fourier_blindWitness {K : ℝ} (hK : π / 2 < K) :
    𝓕 (blindWitness (4 / (K - π / 2))) = blindProfile (4 / (K - π / 2)) := by
  have hpi := Real.pi_pos
  have hd : 0 < K - π / 2 := by linarith
  have hc : 0 < 4 / (K - π / 2) := by positivity
  have hw := (integrable_blindWitness_room hK).1
  have hF : 𝓕 (blindProfile (4 / (K - π / 2))) =
      fun v => blindWitness (4 / (K - π / 2)) (-v) := by
    funext v
    unfold blindWitness
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFi : Integrable (𝓕 (blindProfile (4 / (K - π / 2)))) := by
    rw [hF]; exact hw.comp_neg
  exact Continuous.fourier_fourierInv_eq (continuous_blindProfile _) (integrable_blindProfile hc) hFi

/-- **Every Fourier moment of the witness is a value of `F_c`.**
`∫ w_c(t) e^{-itx} dt = F_c(x)`. -/
theorem integral_blindWitness_mul_cexp {K : ℝ} (hK : π / 2 < K) (x : ℝ) :
    ∫ t, blindWitness (4 / (K - π / 2)) t * cexp (-(I * t) * x) =
      blindExtremal (4 / (K - π / 2)) x := by
  have hpi := Real.pi_pos
  have h := congrFun (fourier_blindWitness hK) (x / (2 * π))
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  have hx : ((2 * π * (x / (2 * π)) : ℝ) : ℂ) = (x : ℂ) := by
    congr 1; field_simp
  unfold blindProfile at h
  rw [hx] at h
  rw [← h]
  congr 1; funext t
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

theorem blindExtremal_log_nat (c : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    blindExtremal c (Real.log n) = 0 := by
  rw [blindExtremal_ofReal, Real.exp_log (by exact_mod_cast hn)]
  have : Real.sin (π * n) = 0 := by rw [mul_comm]; exact Real.sin_nat_mul_pi n
  rw [this, zero_mul, Complex.ofReal_zero]

theorem blindExtremal_neg_log_two_ne_zero (c : ℝ) :
    blindExtremal c ((-Real.log 2 : ℝ) : ℂ) ≠ 0 := by
  rw [blindExtremal_ofReal, Real.exp_neg, Real.exp_log (by norm_num)]
  have : Real.sin (π * 2⁻¹) = 1 := by rw [← div_eq_mul_inv]; exact Real.sin_pi_div_two
  rw [this, one_mul, Complex.ofReal_ne_zero]
  exact (Real.exp_pos _).ne'

/-- **Sharpness of the logarithmic Carlson threshold (Theorem B).**  For every `K > π/2` there is
a continuous integrable `w`, with `∫ |w| e^{(π/2)|t| − K|t|/log(|t|+3)} < ∞`, whose Dirichlet
moments `∫ w(t) n^{-it} dt` vanish at every integer `n ≥ 1`, but whose Fourier transform is not
identically zero.

With `fourier_eq_zero_of_integerMoment_eq_zero_logRoom` (which forces vanishing for `K < π/2`),
this shows that `π/2` is the exact constant at the scale `t/log t`.  The witness is the inverse
Fourier transform of `F_c(x) = sin(π e^x) e^{-π c x e^x}`, `c = 4/(K − π/2)`; its decay comes
from shifting the line of integration to `Im x = π/2 − κ/log(|t|+3)`, `κ = (K + π/2)/2`. -/
theorem exists_integerBlind_logRoom {K : ℝ} (hK : π / 2 < K) :
    ∃ w : ℝ → ℂ, Continuous w ∧ Integrable w ∧
      Integrable (fun t => ‖w t‖ * logRoomWeight K t) ∧
      (∀ n : ℕ, 1 ≤ n → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) ∧
      ∃ x : ℝ, ∫ t, w t * cexp (-(I * t) * x) ≠ 0 := by
  have hpi := Real.pi_pos
  have hd : 0 < K - π / 2 := by linarith
  have hc : 0 < 4 / (K - π / 2) := by positivity
  obtain ⟨hw, hroom⟩ := integrable_blindWitness_room hK
  refine ⟨blindWitness (4 / (K - π / 2)), continuous_blindWitness hc, hw, hroom, fun n hn => ?_,
    -Real.log 2, ?_⟩
  · rw [integral_blindWitness_mul_cexp hK]; exact blindExtremal_log_nat _ hn
  · rw [integral_blindWitness_mul_cexp hK]
    exact blindExtremal_neg_log_two_ne_zero _

/-- **The exact second-order Carlson constant for `log ℕ`.**  With room
`e^{(π/2)|t| − K|t|/log(|t|+3)}`, vanishing Dirichlet moments at the integers force a vanishing
Fourier transform when `0 ≤ K < π/2`, and fail to do so for every `K > π/2`. -/
theorem logRoom_integerBlind_threshold :
    (∀ K : ℝ, 0 ≤ K → K < π / 2 → ∀ w : ℝ → ℂ, AEStronglyMeasurable w volume →
      Integrable (fun t => ‖w t‖ * logRoomWeight K t) →
      (∀ n : ℕ, 2 ≤ n → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) →
      ∀ x : ℝ, ∫ t, w t * cexp (-(I * t) * x) = 0) ∧
    (∀ K : ℝ, π / 2 < K → ∃ w : ℝ → ℂ, Integrable (fun t => ‖w t‖ * logRoomWeight K t) ∧
      (∀ n : ℕ, 1 ≤ n → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) ∧
      ∃ x : ℝ, ∫ t, w t * cexp (-(I * t) * x) ≠ 0) := by
  refine ⟨fun K hK0 hK w hwm hroom hmom x =>
    fourier_eq_zero_of_integerMoment_eq_zero_logRoom hK0 hK hwm hroom hmom x, fun K hK => ?_⟩
  obtain ⟨w, -, -, hroom, hmom, hx⟩ := exists_integerBlind_logRoom hK
  exact ⟨w, hroom, hmom, hx⟩

end RHTower.PrimeBlindCarlson
