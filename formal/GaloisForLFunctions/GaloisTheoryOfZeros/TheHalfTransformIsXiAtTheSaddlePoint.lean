import GaloisForLFunctions.GaloisTheoryOfZeros.TheGaussianConcentratesAtTheSaddlePoint

/-!
# The half transform is `ξ` at the saddle point

For a time `τ` with `Re τ > 0`, a point `s` and a corner `κ ≥ 5` with `Re s + κ ≥ 11/2`, put
`a = ½ log((s + κ)/2π)` (the slope of `ξ` at the base point `s + κ`), `p = s + 2τa` (the saddle
point) and `M = ξ(p) e^{−τa²}` (the saddle value). Then

`∫_0^∞ g_τ(u) ξ(s + u) du = M (1 + o(1))`  as `Re a → ∞`,

uniformly for `τ` in `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` (`exists_norm_integral_sub_saddleValue_le`). For
`s = 1/2 + iz`, `Im z ≤ Y`, `κ = Y + 5` this is the half transform `𝒜(τ, z)` at the far places of
a lower half-plane (`exists_halfHeat_sub_saddleValue_le`); `M ≠ 0` there.

Mechanism. The half line is moved through the corner `κ` to the height `Im(2τa)`:

* the ray through the saddle carries `M`: on a window around `Re(2τa)` the slope `ξ'/ξ` is `a`
  up to `o(1)`, and beyond it up to `1 + (λ/2)|u − Re 2τa|`, `λ` the Gaussian rate;
* on the vertical side the exponent of the Gaussian is concave, and at both ends the integrand is
  smaller than `M` by `e^{−c (Re a)²}`;
* the unshifted piece on `[0, κ]` is bounded through the strip by `ξ(s + κ)`, which is smaller
  than `M` by `e^{−t₀ (Re a)²}`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Elementary facts -/

theorem re_two_mul_mul (τ a : ℂ) : (2 * τ * a).re = 2 * (τ.re * a.re - τ.im * a.im) := by
  rw [mul_assoc, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.mul_re]

theorem re_mul_sq (τ a : ℂ) :
    (τ * a ^ 2).re = τ.re * (a.re ^ 2 - a.im ^ 2) - 2 * τ.im * a.re * a.im := by
  simp only [sq, Complex.mul_re, Complex.mul_im]
  ring

theorem le_convexCombo {θ x y m : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hx : m ≤ x) (hy : m ≤ y) :
    m ≤ (1 - θ) * x + θ * y := by
  nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hy h0]

theorem convexCombo_le {θ x y m : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hx : x ≤ m) (hy : y ≤ m) :
    (1 - θ) * x + θ * y ≤ m := by
  nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hy h0]

/-- The coordinates of a point of a segment are convex combinations of those of its ends. -/
theorem re_im_of_mem_segment {p q w : ℂ} (hw : w ∈ segment ℝ p q) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ w.re = (1 - θ) * p.re + θ * q.re ∧
      w.im = (1 - θ) * p.im + θ * q.im := by
  rw [segment_eq_image'] at hw
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hw
  refine ⟨θ, h0, h1, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul, Complex.sub_re]
    ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.im_ofReal_mul, Complex.sub_im]
    ring

/-! ## The saddle configuration -/

/-- The threshold on `Re a` beyond which the slope of `ξ` is under control near the base point. -/
def slopeThreshold (t₀ T₀ : ℝ) : ℝ := 4 + 4 * T₀ + 1 / gaussRate t₀ T₀

/-- The threshold on `Re a` beyond which the saddle lies far to the right of the corner `κ`. -/
def farThreshold (t₀ T₀ κ : ℝ) : ℝ := slopeThreshold t₀ T₀ + (2 * T₀ + κ) / t₀

/-- A time `τ` of the box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, a corner `κ`, a point `s` whose base point
`s + κ` lies in `Re ≥ 11/2`, and the slope `a` of `ξ` at the base point, with `Re a` beyond the
slope threshold. The saddle `2τa` lies to the right of the corner when moreover
`2T₀ + κ ≤ t₀ Re a`. -/
structure SlopeConfig (t₀ T₀ κ : ℝ) (τ s a : ℂ) : Prop where
  ht₀ : 0 < t₀
  hτt : t₀ ≤ τ.re
  hτT : ‖τ‖ ≤ T₀
  hκ : 5 ≤ κ
  hs : 11 / 2 ≤ s.re + κ
  ha : a = xiSlope (s + (κ : ℂ))
  hα : slopeThreshold t₀ T₀ ≤ a.re

namespace SlopeConfig

variable {t₀ T₀ κ : ℝ} {τ s a : ℂ}

theorem τ_re_pos (h : SlopeConfig t₀ T₀ κ τ s a) : 0 < τ.re := h.ht₀.trans_le h.hτt

theorem t₀_le (h : SlopeConfig t₀ T₀ κ τ s a) : t₀ ≤ T₀ :=
  h.hτt.trans ((Complex.re_le_norm τ).trans h.hτT)

theorem T₀_pos (h : SlopeConfig t₀ T₀ κ τ s a) : 0 < T₀ := h.ht₀.trans_le h.t₀_le

theorem rate_pos (h : SlopeConfig t₀ T₀ κ τ s a) : 0 < gaussRate t₀ T₀ := by
  have h1 := h.ht₀
  have h2 := h.T₀_pos
  rw [gaussRate]
  positivity

theorem rate_mul_le (h : SlopeConfig t₀ T₀ κ τ s a) : gaussRate t₀ T₀ * t₀ ≤ 1 := by
  have h1 := h.ht₀
  have h2 := h.T₀_pos
  have h3 := h.t₀_le
  rw [gaussRate, div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith [mul_self_le_mul_self h1.le h3, sq_nonneg T₀]

theorem four_le (h : SlopeConfig t₀ T₀ κ τ s a) : 4 + 4 * T₀ + 1 / gaussRate t₀ T₀ ≤ a.re :=
  h.hα

theorem four_le_re (h : SlopeConfig t₀ T₀ κ τ s a) : 4 ≤ a.re := by
  have h1 := h.four_le
  have h2 := h.T₀_pos
  have h3 : 0 < 1 / gaussRate t₀ T₀ := one_div_pos.2 h.rate_pos
  linarith

theorem one_le_rate_mul (h : SlopeConfig t₀ T₀ κ τ s a) :
    1 ≤ gaussRate t₀ T₀ * (1 + a.re) := by
  have h1 : 1 / gaussRate t₀ T₀ ≤ 1 + a.re := by
    have h2 := h.four_le
    have h3 := h.T₀_pos
    linarith
  rw [div_le_iff₀ h.rate_pos] at h1
  linarith

theorem base_re (h : SlopeConfig t₀ T₀ κ τ s a) : 11 / 2 ≤ (s + (κ : ℂ)).re := by
  rw [Complex.add_re, Complex.ofReal_re]
  exact h.hs

/-- `‖s + κ‖ = 2π e^{2 Re a}`. -/
theorem norm_base (h : SlopeConfig t₀ T₀ κ τ s a) :
    ‖s + (κ : ℂ)‖ = 2 * Real.pi * Real.exp (2 * a.re) := by
  have hpos : 0 < ‖s + (κ : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) (h.base_re.trans (Complex.re_le_norm _))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have e : 2 * a.re = Real.log ‖s + (κ : ℂ)‖ - Real.log (2 * Real.pi) := by
    rw [h.ha, xiSlope_re]
    ring
  rw [e, Real.exp_sub, Real.exp_log hpos, Real.exp_log h2pi]
  field_simp

theorem abs_im_le (h : SlopeConfig t₀ T₀ κ τ s a) : |a.im| ≤ 1 := by
  have h1 := abs_xiSlope_im_lt (s := s + (κ : ℂ)) (by linarith [h.base_re])
  have h2 := Real.pi_lt_d2
  rw [h.ha]
  linarith

theorem norm_le (h : SlopeConfig t₀ T₀ κ τ s a) : ‖a‖ ≤ 1 + a.re := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [abs_of_nonneg (by linarith [h.four_le_re])]
  linarith [h.abs_im_le]

theorem norm_two_mul_le (h : SlopeConfig t₀ T₀ κ τ s a) :
    ‖2 * τ * a‖ ≤ 2 * T₀ * (1 + a.re) := by
  rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
  have h1 := mul_le_mul h.hτT h.norm_le (norm_nonneg _) h.T₀_pos.le
  linarith

theorem abs_im_mul_im_le (h : SlopeConfig t₀ T₀ κ τ s a) : |τ.im * a.im| ≤ T₀ := by
  rw [abs_mul]
  calc |τ.im| * |a.im| ≤ T₀ * 1 :=
        mul_le_mul ((Complex.abs_im_le_norm τ).trans h.hτT) h.abs_im_le (abs_nonneg _)
          h.T₀_pos.le
    _ = T₀ := mul_one _

/-- The saddle lies to the right of the corner: `Re(2τa) ≥ κ + t₀ Re a`. -/
theorem le_re_two_mul (h : SlopeConfig t₀ T₀ κ τ s a) (hκα : 2 * T₀ + κ ≤ t₀ * a.re) :
    κ + t₀ * a.re ≤ (2 * τ * a).re := by
  rw [re_two_mul_mul]
  have h1 : t₀ * a.re ≤ τ.re * a.re :=
    mul_le_mul_of_nonneg_right h.hτt (by linarith [h.four_le_re])
  have h2 := (abs_le.1 h.abs_im_mul_im_le).2
  linarith

/-- `Re(τa²) ≥ t₀ (Re a)² − 2T₀ Re a − T₀`. -/
theorem le_re_mul_sq (h : SlopeConfig t₀ T₀ κ τ s a) :
    t₀ * a.re ^ 2 - 2 * T₀ * a.re - T₀ ≤ (τ * a ^ 2).re := by
  rw [re_mul_sq]
  have hα0 : 0 ≤ a.re := by linarith [h.four_le_re]
  have hφ2 : a.im ^ 2 ≤ 1 := by
    have h1 := h.abs_im_le
    rw [← sq_abs]
    nlinarith [abs_nonneg a.im]
  have hτre : τ.re ≤ T₀ := (Complex.re_le_norm τ).trans h.hτT
  have h1 : t₀ * a.re ^ 2 ≤ τ.re * a.re ^ 2 := mul_le_mul_of_nonneg_right h.hτt (sq_nonneg _)
  have h2 : τ.re * a.im ^ 2 ≤ T₀ * 1 := mul_le_mul hτre hφ2 (sq_nonneg _) h.T₀_pos.le
  have h4 : τ.im * a.im * a.re ≤ T₀ * a.re :=
    mul_le_mul_of_nonneg_right (abs_le.1 h.abs_im_mul_im_le).2 hα0
  nlinarith

/-- The base point is far from the origin on the scale of the saddle. -/
theorem sq_le_half_norm_base (h : SlopeConfig t₀ T₀ κ τ s a) :
    (1 + a.re) ^ 2 ≤ ‖s + (κ : ℂ)‖ / 2 - 2 * T₀ * (1 + a.re) := by
  rw [h.norm_base]
  have hα := h.four_le_re
  have hT : T₀ ≤ 1 + a.re := by
    have h1 := h.four_le
    have h2 := h.T₀_pos
    have h3 : 0 < 1 / gaussRate t₀ T₀ := one_div_pos.2 h.rate_pos
    linarith
  have he : (1 + a.re) ^ 2 ≤ Real.exp (2 * a.re) := by
    have h1 := Real.add_one_le_exp a.re
    have h2 : Real.exp (2 * a.re) = Real.exp a.re * Real.exp a.re := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h2]
    nlinarith [mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ a.re + 1) h1]
  have hpiE3 : 3 * Real.exp (2 * a.re) ≤ Real.pi * Real.exp (2 * a.re) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos _).le
  have hTN : T₀ * (1 + a.re) ≤ (1 + a.re) * (1 + a.re) :=
    mul_le_mul_of_nonneg_right hT (by linarith)
  nlinarith

/-- **The slope to the right of the base point.** For `Re w ≥ Re(s + κ)` and
`|Im w − Im s| ≤ 2T₀(1 + Re a)`,
`‖ξ'/ξ(w) − a‖ ≤ 4/N² + 2^{5 − Re w}/12 + (Re w − Re(s + κ) + 2T₀N)/(2N²)`, `N = 1 + Re a`. -/
theorem norm_logDeriv_xi_sub_le (h : SlopeConfig t₀ T₀ κ τ s a) {w : ℂ}
    (hre : (s + (κ : ℂ)).re ≤ w.re)
    (him : |w.im - (s + (κ : ℂ)).im| ≤ 2 * T₀ * (1 + a.re)) :
    ‖logDeriv xi w - a‖ ≤
      4 / (1 + a.re) ^ 2 + (2 : ℝ) ^ (5 - w.re) / 12 +
        ((w.re - (s + (κ : ℂ)).re) + 2 * T₀ * (1 + a.re)) / (2 * (1 + a.re) ^ 2) := by
  have hb := h.base_re
  have hα := h.four_le_re
  have hm : 0 < (1 + a.re) ^ 2 := pow_pos (by linarith) 2
  have h1 := norm_logDeriv_xi_sub_xiSlope_base_le (b := s + (κ : ℂ)) (w := w) (κ := 0)
    (h := 2 * T₀ * (1 + a.re)) (m := (1 + a.re) ^ 2)
    (by linarith) (by linarith) le_rfl (by linarith) him hm
    (by linarith [h.sq_le_half_norm_base])
  rw [← h.ha] at h1
  have h2 : ‖w - (s + (κ : ℂ))‖ ≤ (w.re - (s + (κ : ℂ)).re) + 2 * T₀ * (1 + a.re) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, abs_of_nonneg (sub_nonneg.2 hre)]
    linarith
  have h3 := div_le_div_of_nonneg_right h2 (mul_pos two_pos hm).le
  linarith

/-- Crude form: the slope is `a` up to `1 + (λ/2) D`, `D` the excess of `Re w − Re(s + κ)` over
`2T₀(1 + Re a)`. -/
theorem norm_logDeriv_xi_sub_le_one_add (h : SlopeConfig t₀ T₀ κ τ s a) {w : ℂ} {D : ℝ}
    (hD : 0 ≤ D) (hre : (s + (κ : ℂ)).re ≤ w.re)
    (hre' : w.re - (s + (κ : ℂ)).re ≤ 2 * T₀ * (1 + a.re) + D)
    (him : |w.im - (s + (κ : ℂ)).im| ≤ 2 * T₀ * (1 + a.re)) :
    ‖logDeriv xi w - a‖ ≤ 1 + gaussRate t₀ T₀ / 2 * D := by
  have h0 := h.norm_logDeriv_xi_sub_le hre him
  have hα := h.four_le_re
  have hT0 := h.T₀_pos
  have hlam := h.rate_pos
  have hN5 : 5 ≤ 1 + a.re := by linarith
  have h4T : 4 * T₀ ≤ 1 + a.re := by
    have h1 := h.four_le
    have h3 : 0 < 1 / gaussRate t₀ T₀ := one_div_pos.2 hlam
    linarith
  have hlamN := h.one_le_rate_mul
  have hN2 : 25 ≤ (1 + a.re) ^ 2 := by nlinarith
  have hlamN2 : 1 ≤ gaussRate t₀ T₀ * (1 + a.re) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hlamN) (by linarith : (0 : ℝ) ≤ 1 + a.re - 1)]
  have e1 : 4 / (1 + a.re) ^ 2 ≤ 4 / 25 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN2
  have e2 : (2 : ℝ) ^ (5 - w.re) / 12 ≤ 1 / 12 := by
    have : (2 : ℝ) ^ (5 - w.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [h.base_re])
    linarith
  have e3 : ((w.re - (s + (κ : ℂ)).re) + 2 * T₀ * (1 + a.re)) / (2 * (1 + a.re) ^ 2) ≤
      1 / 2 + gaussRate t₀ T₀ / 2 * D := by
    rw [div_le_iff₀ (mul_pos two_pos (pow_pos (by linarith) 2))]
    have a1 : 4 * T₀ * (1 + a.re) ≤ (1 + a.re) * (1 + a.re) :=
      mul_le_mul_of_nonneg_right h4T (by linarith)
    have a2 := mul_le_mul_of_nonneg_left hlamN2 hD
    nlinarith
  linarith

theorem norm_logDeriv_xi_sub_le_one (h : SlopeConfig t₀ T₀ κ τ s a) {w : ℂ}
    (hre : (s + (κ : ℂ)).re ≤ w.re) (hre' : w.re - (s + (κ : ℂ)).re ≤ 2 * T₀ * (1 + a.re))
    (him : |w.im - (s + (κ : ℂ)).im| ≤ 2 * T₀ * (1 + a.re)) : ‖logDeriv xi w - a‖ ≤ 1 := by
  have h1 := h.norm_logDeriv_xi_sub_le_one_add le_rfl hre (by linarith) him
  linarith

/-! ## The ray through the saddle -/

/-- **The ray through the saddle carries the saddle value.** `L` is the half width of the window,
`η₁` the bound for the deviation of the slope on it. -/
theorem norm_ray_sub_le (h : SlopeConfig t₀ T₀ κ τ s a) (hκα : 2 * T₀ + κ ≤ t₀ * a.re)
    {L η₁ : ℝ} (hL : 4 / gaussRate t₀ T₀ ≤ L) (hLα : 2 * L ≤ t₀ * a.re) (hη₁ : 0 < η₁)
    (hη : 4 / (1 + a.re) ^ 2 + 1 / (3 * (t₀ * a.re)) +
      (4 * T₀ * (1 + a.re) + L) / (2 * (1 + a.re) ^ 2) ≤ η₁) :
    ‖(∫ u in Ioi κ, complexGauss τ (u + (2 * τ * a).im * I) *
          xi (s + (u + (2 * τ * a).im * I))) - xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (gaussHeight t₀ *
        ((Real.exp (η₁ * L) - 1) * (∫ v : ℝ, Real.exp (-gaussRate t₀ T₀ * v ^ 2)) +
          2 * (Real.exp (-gaussRate t₀ T₀ * L ^ 2 / 8) *
            ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 8) * v ^ 2)))) := by
  set w₀ : ℝ := (2 * τ * a).re with hw₀
  set c : ℝ := (2 * τ * a).im with hc
  have hsad : 2 * τ * a = w₀ + c * I := (Complex.re_add_im _).symm
  have hα4 := h.four_le_re
  have ht₀ := h.ht₀
  have hT0 := h.T₀_pos
  have hκ := h.hκ
  have hlam := h.rate_pos
  have hL0 : 0 < L := lt_of_lt_of_le (div_pos (by norm_num) hlam) hL
  have hta : 0 < t₀ * a.re := mul_pos ht₀ (by linarith)
  have hw₀κ : κ + t₀ * a.re ≤ w₀ := h.le_re_two_mul hκα
  have hu₂ : κ + L ≤ w₀ := by linarith
  have hnorm := h.norm_two_mul_le
  have hw₀le : w₀ ≤ 2 * T₀ * (1 + a.re) := (Complex.re_le_norm _).trans hnorm
  have hcle : |c| ≤ 2 * T₀ * (1 + a.re) := (Complex.abs_im_le_norm _).trans hnorm
  have e5 : (s + (κ : ℂ)).re = s.re + κ := by rw [Complex.add_re, Complex.ofReal_re]
  have e6 : (s + (κ : ℂ)).im = s.im := by rw [Complex.add_im, Complex.ofReal_im, add_zero]
  have hbre := h.base_re
  -- the horizontal segment from the saddle point
  have hgeom : ∀ u : ℝ, ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + ((u : ℂ) + c * I)),
      (s + (κ : ℂ)).re + (min u w₀ - κ) ≤ w'.re ∧
        w'.re ≤ (s + (κ : ℂ)).re + (max u w₀ - κ) ∧ w'.im - (s + (κ : ℂ)).im = c := by
    intro u w' hw'
    obtain ⟨θ, hθ0, hθ1, hre, him⟩ := re_im_of_mem_segment hw'
    have e1 : (s + 2 * τ * a).re = s.re + w₀ := by rw [Complex.add_re, ← hw₀]
    have e2 : (s + 2 * τ * a).im = s.im + c := by rw [Complex.add_im, ← hc]
    have e3 : (s + ((u : ℂ) + c * I)).re = s.re + u := by simp
    have e4 : (s + ((u : ℂ) + c * I)).im = s.im + c := by simp
    rw [e1, e3] at hre
    rw [e2, e4] at him
    rw [e5, e6]
    have h1 := le_convexCombo hθ0 hθ1 (min_le_right u w₀) (min_le_left u w₀)
    have h2 := convexCombo_le hθ0 hθ1 (le_max_right u w₀) (le_max_left u w₀)
    refine ⟨?_, ?_, ?_⟩
    · rw [hre]
      linarith
    · rw [hre]
      linarith
    · rw [him]
      ring
  have hnear : ∀ u : ℝ, κ ≤ u → |u - w₀| ≤ L →
      ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + ((u : ℂ) + c * I)),
        1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ η₁ := by
    intro u hu huL w' hw'
    obtain ⟨g1, g2, g3⟩ := hgeom u w' hw'
    have hab := abs_le.1 huL
    have hmin : w₀ - L ≤ min u w₀ := le_min (by linarith) (by linarith)
    have hmax : max u w₀ ≤ w₀ + L := max_le (by linarith) (by linarith)
    have hx : 0 < t₀ * a.re / 2 := by linarith
    have hwre : (s + (κ : ℂ)).re + t₀ * a.re / 2 ≤ w'.re := by linarith
    refine ⟨by linarith, ?_⟩
    have hS := h.norm_logDeriv_xi_sub_le (w := w') (by linarith) (by rw [g3]; exact hcle)
    refine hS.trans (le_trans ?_ hη)
    have hr : (2 : ℝ) ^ (5 - w'.re) ≤ (2 : ℝ) ^ (-(t₀ * a.re / 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hr2 := mul_two_rpow_neg_le hx
    have e2 : (2 : ℝ) ^ (5 - w'.re) / 12 ≤ 1 / (3 * (t₀ * a.re)) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hr hx.le]
    have e3 : ((w'.re - (s + (κ : ℂ)).re) + 2 * T₀ * (1 + a.re)) / (2 * (1 + a.re) ^ 2) ≤
        (4 * T₀ * (1 + a.re) + L) / (2 * (1 + a.re) ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (mul_pos two_pos (pow_pos (by linarith) 2)).le
    linarith
  have hfar : ∀ u : ℝ, κ ≤ u → ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + ((u : ℂ) + c * I)),
      1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ 1 + gaussRate t₀ T₀ / 2 * |u - w₀| := by
    intro u hu w' hw'
    obtain ⟨g1, g2, g3⟩ := hgeom u w' hw'
    have hmin : κ ≤ min u w₀ := le_min hu (by linarith)
    have hmax : max u w₀ ≤ w₀ + |u - w₀| :=
      max_le (by linarith [le_abs_self (u - w₀)]) (by linarith [abs_nonneg (u - w₀)])
    refine ⟨by linarith, ?_⟩
    exact h.norm_logDeriv_xi_sub_le_one_add (abs_nonneg _) (by linarith) (by linarith)
      (by rw [g3]; exact hcle)
  exact norm_integral_ray_sub_saddle_le h.ht₀ h.hτt h.hτT s a hsad hL hu₂ hη₁ hnear hfar

/-! ## The vertical side -/

/-- **The vertical side is smaller than the saddle value by `e^{−λt₀² (Re a)²}`.** -/
theorem norm_side_le (h : SlopeConfig t₀ T₀ κ τ s a) (hκα : 2 * T₀ + κ ≤ t₀ * a.re) :
    ‖∫ v in (0 : ℝ)..(2 * τ * a).im, complexGauss τ (κ + v * I) * xi (s + (κ + v * I))‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (gaussHeight t₀ * (2 * T₀ * (1 + a.re)) *
        Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀)) := by
  set w₀ : ℝ := (2 * τ * a).re with hw₀
  set c : ℝ := (2 * τ * a).im with hc
  have hsad : 2 * τ * a = w₀ + c * I := (Complex.re_add_im _).symm
  have hτ := h.τ_re_pos
  have hτ0 := ne_zero_of_re_pos hτ
  have hα4 := h.four_le_re
  have ht₀ := h.ht₀
  have hT0 := h.T₀_pos
  have hκ := h.hκ
  have hlam := h.rate_pos
  have hta : 0 < t₀ * a.re := mul_pos ht₀ (by linarith)
  have hw₀κ : κ + t₀ * a.re ≤ w₀ := h.le_re_two_mul hκα
  have hnorm := h.norm_two_mul_le
  have hw₀le : w₀ ≤ 2 * T₀ * (1 + a.re) := (Complex.re_le_norm _).trans hnorm
  have hcle : |c| ≤ 2 * T₀ * (1 + a.re) := (Complex.abs_im_le_norm _).trans hnorm
  have e5 : (s + (κ : ℂ)).re = s.re + κ := by rw [Complex.add_re, Complex.ofReal_re]
  have e6 : (s + (κ : ℂ)).im = s.im := by rw [Complex.add_im, Complex.ofReal_im, add_zero]
  have hbre := h.base_re
  have hpt : ∀ v ∈ Set.uIoc (0 : ℝ) c,
      ‖complexGauss τ (κ + v * I) * xi (s + (κ + v * I))‖ ≤
        ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (gaussHeight t₀ *
          Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀)) := by
    intro v hv
    obtain ⟨θ, hθ0, hθ1, rfl⟩ := exists_mul_of_mem_uIoc hv
    -- the segment from the saddle point stays to the right of the base point
    have hseg : ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)),
        1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ 1 := by
      intro w' hw'
      obtain ⟨θ', hθ'0, hθ'1, hre, him⟩ := re_im_of_mem_segment hw'
      have e1 : (s + 2 * τ * a).re = s.re + w₀ := by rw [Complex.add_re, ← hw₀]
      have e2 : (s + 2 * τ * a).im = s.im + c := by rw [Complex.add_im, ← hc]
      have e3 : (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)).re = s.re + κ := by simp
      have e4 : (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)).im = s.im + θ * c := by simp
      rw [e1, e3] at hre
      rw [e2, e4] at him
      have hre1 : (s + (κ : ℂ)).re ≤ w'.re := by
        rw [e5, hre]
        have := le_convexCombo hθ'0 hθ'1 (by linarith : s.re + κ ≤ s.re + w₀)
          (le_refl (s.re + κ))
        linarith
      have hre2 : w'.re - (s + (κ : ℂ)).re ≤ 2 * T₀ * (1 + a.re) := by
        rw [e5, hre]
        have := convexCombo_le hθ'0 hθ'1
          (by linarith : s.re + w₀ ≤ s.re + κ + 2 * T₀ * (1 + a.re))
          (by linarith : s.re + κ ≤ s.re + κ + 2 * T₀ * (1 + a.re))
        linarith
      have him1 : |w'.im - (s + (κ : ℂ)).im| ≤ 2 * T₀ * (1 + a.re) := by
        have e : w'.im - (s + (κ : ℂ)).im = (1 - θ' * (1 - θ)) * c := by
          rw [e6, him]
          ring
        have h0 : 0 ≤ 1 - θ' * (1 - θ) := by nlinarith [mul_nonneg hθ'0 hθ0]
        have h1 : 1 - θ' * (1 - θ) ≤ 1 := by
          nlinarith [mul_nonneg hθ'0 (sub_nonneg.2 hθ1)]
        rw [e, abs_mul, abs_of_nonneg h0]
        exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans hcle
      exact ⟨by linarith, h.norm_logDeriv_xi_sub_le_one hre1 hre2 him1⟩
    have hmain := norm_complexGauss_mul_xi_le hτ0 s a ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)
      one_pos hseg
    have hd : (κ : ℂ) + ((θ * c : ℝ) : ℂ) * I - 2 * τ * a =
        ((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I := by
      rw [hsad]
      push_cast
      ring
    rw [hd] at hmain
    -- the distance to the saddle
    have hdn : ‖((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I‖ ≤ 4 * T₀ * (1 + a.re) := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have r1 : (((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I).re = κ - w₀ := by simp
      have r2 : (((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I).im = θ * c - c := by simp
      rw [r1, r2, abs_of_nonpos (by linarith), show θ * c - c = -((1 - θ) * c) by ring, abs_neg,
        abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ)]
      have : (1 - θ) * |c| ≤ |c| := mul_le_of_le_one_left (abs_nonneg _) (by linarith)
      linarith
    -- the Gaussian factor: concavity between the two ends
    have hg : ‖complexGauss τ (((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I)‖ ≤
        gaussHeight t₀ * Real.exp
          (-(gaussRate t₀ T₀ * t₀ ^ 2 * a.re ^ 2 - (2 * T₀ + κ) * a.re - T₀)) := by
      rw [norm_complexGauss hτ]
      have hconc := re_sq_div_concave hτ (κ - w₀) c θ hθ0 hθ1
      have hR1 : gaussRate t₀ T₀ * t₀ ^ 2 * a.re ^ 2 - (2 * T₀ + κ) * a.re - T₀ ≤
          (((κ - w₀ : ℝ) : ℂ) ^ 2 / (4 * τ)).re := by
        rw [re_ofReal_sq_div hτ]
        have q1 := gaussRate_le h.ht₀ h.hτt h.hτT
        have q2 : (t₀ * a.re) ^ 2 ≤ (κ - w₀) ^ 2 := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ w₀ - κ - t₀ * a.re)
            (by linarith : (0 : ℝ) ≤ w₀ - κ + t₀ * a.re)]
        have q3 : gaussRate t₀ T₀ * (t₀ * a.re) ^ 2 ≤
            τ.re / (4 * ‖τ‖ ^ 2) * (κ - w₀) ^ 2 :=
          mul_le_mul q1 q2 (sq_nonneg _) (le_trans hlam.le q1)
        nlinarith [mul_nonneg hT0.le (by linarith : (0 : ℝ) ≤ a.re),
          mul_nonneg (by linarith : (0 : ℝ) ≤ κ) (by linarith : (0 : ℝ) ≤ a.re)]
      have hR0 : gaussRate t₀ T₀ * t₀ ^ 2 * a.re ^ 2 - (2 * T₀ + κ) * a.re - T₀ ≤
          ((((κ - w₀ : ℝ) : ℂ) + ((0 - c : ℝ) : ℂ) * I) ^ 2 / (4 * τ)).re := by
        have e : (((κ - w₀ : ℝ) : ℂ) + ((0 - c : ℝ) : ℂ) * I) ^ 2 / (4 * τ) =
            (κ : ℂ) ^ 2 / (4 * τ) - κ * a + τ * a ^ 2 := by
          have e0 : ((κ - w₀ : ℝ) : ℂ) + ((0 - c : ℝ) : ℂ) * I = κ - 2 * τ * a := by
            rw [hsad]
            push_cast
            ring
          rw [e0]
          field_simp
          ring
        rw [e, Complex.add_re, Complex.sub_re, re_ofReal_sq_div hτ, Complex.re_ofReal_mul]
        have q1 := h.le_re_mul_sq
        have q2 : 0 ≤ τ.re / (4 * ‖τ‖ ^ 2) * κ ^ 2 :=
          mul_nonneg (div_nonneg hτ.le (by positivity)) (sq_nonneg _)
        have q4 : gaussRate t₀ T₀ * t₀ * (t₀ * a.re ^ 2) ≤ 1 * (t₀ * a.re ^ 2) :=
          mul_le_mul_of_nonneg_right h.rate_mul_le (mul_nonneg ht₀.le (sq_nonneg _))
        nlinarith
      have hlow := le_convexCombo hθ0 hθ1 hR0 hR1
      calc Real.exp (-((((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I) ^ 2 / (4 * τ)).re) /
            Real.sqrt (4 * Real.pi * ‖τ‖)
          = 1 / Real.sqrt (4 * Real.pi * ‖τ‖) *
              Real.exp (-((((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I) ^ 2 /
                (4 * τ)).re) := by ring
        _ ≤ _ := mul_le_mul (one_div_sqrt_le_gaussHeight h.ht₀ h.hτt)
            (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (gaussHeight_pos h.ht₀).le
    have hE : Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀) =
        Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2 * a.re ^ 2 - (2 * T₀ + κ) * a.re - T₀)) *
          Real.exp (4 * T₀ * (1 + a.re)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖complexGauss τ ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I) *
          xi (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I))‖
        ≤ ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ *
            ‖complexGauss τ (((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I)‖ *
            Real.exp (1 * ‖((κ - w₀ : ℝ) : ℂ) + ((θ * c - c : ℝ) : ℂ) * I‖) := hmain
      _ ≤ ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ *
            (gaussHeight t₀ * Real.exp
              (-(gaussRate t₀ T₀ * t₀ ^ 2 * a.re ^ 2 - (2 * T₀ + κ) * a.re - T₀))) *
            Real.exp (4 * T₀ * (1 + a.re)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
            (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
            (mul_nonneg (norm_nonneg _)
              (mul_nonneg (gaussHeight_pos h.ht₀).le (Real.exp_pos _).le))
      _ = _ := by
          rw [hE]
          ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine hint.trans ?_
  rw [sub_zero]
  calc ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (gaussHeight t₀ *
          Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀)) * |c|
      ≤ ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (gaussHeight t₀ *
          Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀)) *
          (2 * T₀ * (1 + a.re)) :=
        mul_le_mul_of_nonneg_left hcle
          (mul_nonneg (norm_nonneg _) (mul_nonneg (gaussHeight_pos h.ht₀).le (Real.exp_pos _).le))
    _ = _ := by ring

/-! ## The unshifted piece -/

/-- On `[0, κ]` the values of `ξ(s + ·)` are bounded by `ξ(s + κ)` times `e^{O(Re a)}`: growth to
the left in `Re ≥ 5`, the strip to the left of it. -/
theorem norm_xi_le_base {C : ℝ} (hC : 0 < C)
    (hstrip : ∀ Y σ X : ℝ, 4 ≤ Y → -Y ≤ σ → σ ≤ 5 →
      ‖xi ((σ : ℂ) + X * I)‖ ≤
        C * (1 + |X|) * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) *
          ‖xi ((5 : ℝ) + X * I)‖)
    (h : SlopeConfig t₀ T₀ κ τ s a) {u : ℝ} (hu0 : 0 ≤ u) (huκ : u ≤ κ) :
    ‖xi (s + u)‖ ≤
      (1 + 8 * C) * Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5) + 4 * κ) *
        ‖xi (s + κ)‖ := by
  have hκ := h.hκ
  have hα4 := h.four_le_re
  have e5 : (s + (κ : ℂ)).re = s.re + κ := by rw [Complex.add_re, Complex.ofReal_re]
  have e6 : (s + (κ : ℂ)).im = s.im := by rw [Complex.add_im, Complex.ofReal_im, add_zero]
  have hbre := h.base_re
  have hlog : 0 ≤ Real.log (13 + κ) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ (2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5) :=
    add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  have hexp1 : 1 ≤ Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) :=
    Real.one_le_exp hB0
  have hb0 : 0 ≤ ‖xi (s + (κ : ℂ))‖ := norm_nonneg _
  have hC8 : 0 ≤ 1 + 8 * C := by linarith
  rcases le_or_gt 5 (s.re + u) with hσ | hσ
  · -- growth to the left from the base point
    have hg := norm_xi_sub_le_mul_exp (s := s + (κ : ℂ)) (v := κ - u) (by linarith)
      (by rw [e5]; linarith)
    have e : s + (κ : ℂ) - ((κ - u : ℝ) : ℂ) = s + u := by
      push_cast
      ring
    rw [e] at hg
    refine hg.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hb0
    calc Real.exp (4 * (κ - u)) ≤ Real.exp (4 * κ) := Real.exp_le_exp.2 (by linarith)
      _ ≤ Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) * Real.exp (4 * κ) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hexp1
      _ ≤ (1 + 8 * C) * (Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) *
            Real.exp (4 * κ)) :=
          le_mul_of_one_le_left (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
            (by linarith)
      _ = _ := by rw [← Real.exp_add]
  · -- the strip, then growth to the left from the base point
    have hs : s + (u : ℂ) = ((s.re + u : ℝ) : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp
    have h1 := hstrip κ (s.re + u) s.im (by linarith) (by linarith [h.hs]) hσ.le
    rw [← hs] at h1
    have hg := norm_xi_sub_le_mul_exp (s := s + (κ : ℂ)) (v := (s + (κ : ℂ)).re - 5)
      (by linarith) (by linarith)
    have e : s + (κ : ℂ) - (((s + (κ : ℂ)).re - 5 : ℝ) : ℂ) = ((5 : ℝ) : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
        ring
      · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re]
        ring
    rw [e] at hg
    have hg' : ‖xi (((5 : ℝ) : ℂ) + (s.im : ℂ) * I)‖ ≤
        ‖xi (s + (κ : ℂ))‖ * Real.exp (4 * κ) :=
      hg.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by rw [e5]; linarith)) hb0)
    -- the height against `Re a`
    have hE1 : 1 ≤ Real.exp (2 * a.re) := Real.one_le_exp (by linarith)
    have hXn : |s.im| ≤ 2 * Real.pi * Real.exp (2 * a.re) := by
      have h2 := Complex.abs_im_le_norm (s + (κ : ℂ))
      rw [e6, h.norm_base] at h2
      exact h2
    have hpi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
    have hpiE := mul_le_mul_of_nonneg_right hpi (Real.exp_pos (2 * a.re)).le
    have hX1 : 1 + |s.im| ≤ 8 * Real.exp (2 * a.re) := by linarith
    have hX2 : |s.im| + κ + 6 ≤ (13 + κ) * Real.exp (2 * a.re) := by
      have := mul_le_mul_of_nonneg_left hE1 (by linarith : (0 : ℝ) ≤ κ + 6)
      linarith
    have habs := abs_nonneg s.im
    have hlogle : Real.log (|s.im| + κ + 6) ≤ 2 * a.re + Real.log (13 + κ) := by
      have h2 := Real.log_le_log (by linarith) hX2
      rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp] at h2
      linarith
    have hstr : C * (1 + |s.im|) * Real.exp (κ * (Real.log (|s.im| + κ + 6) / 2 + 5)) ≤
        8 * C * Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) := by
      have k1 : Real.exp (κ * (Real.log (|s.im| + κ + 6) / 2 + 5)) ≤
          Real.exp (κ * a.re + κ * (Real.log (13 + κ) / 2 + 5)) := by
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hlogle (by linarith : (0 : ℝ) ≤ κ)]
      have k2 : Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) =
          Real.exp (2 * a.re) * Real.exp (κ * a.re + κ * (Real.log (13 + κ) / 2 + 5)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [k2]
      calc C * (1 + |s.im|) * Real.exp (κ * (Real.log (|s.im| + κ + 6) / 2 + 5))
          ≤ C * (8 * Real.exp (2 * a.re)) *
              Real.exp (κ * a.re + κ * (Real.log (13 + κ) / 2 + 5)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hX1 hC.le) k1 (Real.exp_pos _).le
              (mul_nonneg hC.le (mul_nonneg (by norm_num) (Real.exp_pos _).le))
        _ = _ := by ring
    calc ‖xi (s + (u : ℂ))‖
        ≤ C * (1 + |s.im|) * Real.exp (κ * (Real.log (|s.im| + κ + 6) / 2 + 5)) *
            ‖xi (((5 : ℝ) : ℂ) + (s.im : ℂ) * I)‖ := h1
      _ ≤ 8 * C * Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) *
            (‖xi (s + (κ : ℂ))‖ * Real.exp (4 * κ)) :=
          mul_le_mul hstr hg' (norm_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) hC.le) (Real.exp_pos _).le)
      _ ≤ (1 + 8 * C) * Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) *
            (‖xi (s + (κ : ℂ))‖ * Real.exp (4 * κ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
            (mul_nonneg hb0 (Real.exp_pos _).le)
      _ = _ := by
          rw [Real.exp_add ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5)) (4 * κ)]
          ring

/-- **The base point against the saddle value.** `ξ(s + κ)` is smaller than the saddle value by
`e^{−Re(τa²)}`: one comparison of two values of `ξ` along the segment from the saddle point. -/
theorem norm_xi_base_le_of_re (h : SlopeConfig t₀ T₀ κ τ s a) (hκα : 2 * T₀ + κ ≤ t₀ * a.re) :
    ‖xi (s + κ)‖ ≤ ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ *
      Real.exp (-(τ * a ^ 2).re + (κ + 2 * T₀) * a.re + (κ + 2 * T₀)) := by
  set w₀ : ℝ := (2 * τ * a).re with hw₀
  set c : ℝ := (2 * τ * a).im with hc
  have hα4 := h.four_le_re
  have ht₀ := h.ht₀
  have hT0 := h.T₀_pos
  have hκ := h.hκ
  have hta : 0 < t₀ * a.re := mul_pos ht₀ (by linarith)
  have hw₀κ : κ + t₀ * a.re ≤ w₀ := h.le_re_two_mul hκα
  have hnorm := h.norm_two_mul_le
  have hw₀le : w₀ ≤ 2 * T₀ * (1 + a.re) := (Complex.re_le_norm _).trans hnorm
  have hcle : |c| ≤ 2 * T₀ * (1 + a.re) := (Complex.abs_im_le_norm _).trans hnorm
  have e5 : (s + (κ : ℂ)).re = s.re + κ := by rw [Complex.add_re, Complex.ofReal_re]
  have e6 : (s + (κ : ℂ)).im = s.im := by rw [Complex.add_im, Complex.ofReal_im, add_zero]
  have hbre := h.base_re
  have hseg : ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + (κ : ℂ)),
      1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ 1 := by
    intro w' hw'
    obtain ⟨θ, hθ0, hθ1, hre, him⟩ := re_im_of_mem_segment hw'
    have e1 : (s + 2 * τ * a).re = s.re + w₀ := by rw [Complex.add_re, ← hw₀]
    have e2 : (s + 2 * τ * a).im = s.im + c := by rw [Complex.add_im, ← hc]
    rw [e1, e5] at hre
    rw [e2, e6] at him
    have hre1 : (s + (κ : ℂ)).re ≤ w'.re := by
      rw [e5, hre]
      have := le_convexCombo hθ0 hθ1 (by linarith : s.re + κ ≤ s.re + w₀) (le_refl (s.re + κ))
      linarith
    have hre2 : w'.re - (s + (κ : ℂ)).re ≤ 2 * T₀ * (1 + a.re) := by
      rw [e5, hre]
      have := convexCombo_le hθ0 hθ1
        (by linarith : s.re + w₀ ≤ s.re + κ + 2 * T₀ * (1 + a.re))
        (by linarith : s.re + κ ≤ s.re + κ + 2 * T₀ * (1 + a.re))
      linarith
    have him1 : |w'.im - (s + (κ : ℂ)).im| ≤ 2 * T₀ * (1 + a.re) := by
      have e : w'.im - (s + (κ : ℂ)).im = (1 - θ) * c := by
        rw [e6, him]
        ring
      rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith)).trans hcle
    exact ⟨by linarith, h.norm_logDeriv_xi_sub_le_one hre1 hre2 him1⟩
  have hmain := norm_xi_le_mul_exp (p := s + 2 * τ * a) (q := s + (κ : ℂ)) (a := a) one_pos hseg
  have hd : s + (κ : ℂ) - (s + 2 * τ * a) = κ - 2 * τ * a := by ring
  rw [hd] at hmain
  have hre : (((κ : ℂ) - 2 * τ * a) * a).re = κ * a.re - 2 * (τ * a ^ 2).re := by
    have e : ((κ : ℂ) - 2 * τ * a) * a = (κ : ℂ) * a - ((2 : ℝ) : ℂ) * (τ * a ^ 2) := by
      push_cast
      ring
    rw [e, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hn : ‖(κ : ℂ) - 2 * τ * a‖ ≤ κ + 2 * T₀ * (1 + a.re) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, mul_assoc, ← Real.exp_add]
  refine hmain.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
  rw [hre]
  linarith

/-- The base point is smaller than the saddle value by `e^{−t₀ (Re a)²}`. -/
theorem norm_xi_base_le (h : SlopeConfig t₀ T₀ κ τ s a) (hκα : 2 * T₀ + κ ≤ t₀ * a.re) :
    ‖xi (s + κ)‖ ≤ ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ *
      Real.exp (-t₀ * a.re ^ 2 + (κ + 4 * T₀) * a.re + (κ + 3 * T₀)) := by
  refine (h.norm_xi_base_le_of_re hκα).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
  linarith [h.le_re_mul_sq]

/-- **The unshifted piece is smaller than the saddle value by `e^{−t₀ (Re a)²}`.** -/
theorem norm_unshifted_le {C : ℝ} (hC : 0 < C)
    (hstrip : ∀ Y σ X : ℝ, 4 ≤ Y → -Y ≤ σ → σ ≤ 5 →
      ‖xi ((σ : ℂ) + X * I)‖ ≤
        C * (1 + |X|) * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) *
          ‖xi ((5 : ℝ) + X * I)‖)
    (h : SlopeConfig t₀ T₀ κ τ s a) (hκα : 2 * T₀ + κ ≤ t₀ * a.re) :
    ‖∫ u in (0 : ℝ)..κ, complexGauss τ u * xi (s + u)‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (gaussHeight t₀ * κ * (1 + 8 * C) *
        Real.exp (-t₀ * a.re ^ 2 + (2 * κ + 4 * T₀ + 2) * a.re +
          (κ * (Real.log (13 + κ) / 2 + 5) + 5 * κ + 3 * T₀))) := by
  have hκ := h.hκ
  have hC8 : 0 ≤ 1 + 8 * C := by linarith
  have hpt : ∀ u ∈ Set.uIoc (0 : ℝ) κ, ‖complexGauss τ u * xi (s + u)‖ ≤
      gaussHeight t₀ * ((1 + 8 * C) *
        Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5) + 4 * κ) *
        (‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ *
          Real.exp (-t₀ * a.re ^ 2 + (κ + 4 * T₀) * a.re + (κ + 3 * T₀)))) := by
    intro u hu
    rw [uIoc_of_le (by linarith)] at hu
    rw [norm_mul]
    have hg : ‖complexGauss τ u‖ ≤ gaussHeight t₀ := by
      refine (norm_complexGauss_ofReal_le h.ht₀ h.hτt h.hτT u).trans ?_
      have h1 : Real.exp (-gaussRate t₀ T₀ * u ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg h.rate_pos.le (sq_nonneg u)])
      exact mul_le_of_le_one_right (gaussHeight_pos h.ht₀).le h1
    have hx := (norm_xi_le_base hC hstrip h hu.1.le hu.2).trans
      (mul_le_mul_of_nonneg_left (h.norm_xi_base_le hκα) (mul_nonneg hC8 (Real.exp_pos _).le))
    exact mul_le_mul hg hx (norm_nonneg _) (gaussHeight_pos h.ht₀).le
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine hint.trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg (by linarith)]
  have hE : Real.exp (-t₀ * a.re ^ 2 + (2 * κ + 4 * T₀ + 2) * a.re +
      (κ * (Real.log (13 + κ) / 2 + 5) + 5 * κ + 3 * T₀)) =
      Real.exp ((2 + κ) * a.re + κ * (Real.log (13 + κ) / 2 + 5) + 4 * κ) *
        Real.exp (-t₀ * a.re ^ 2 + (κ + 4 * T₀) * a.re + (κ + 3 * T₀)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hE]
  ring

end SlopeConfig

/-! ## The three pieces at far points -/

/-- The ray through the saddle is the saddle value up to `ε`, for `Re a` large. -/
theorem exists_norm_ray_sub_le {t₀ T₀ κ ε : ℝ} (ht₀ : 0 < t₀) (hT : t₀ ≤ T₀) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ τ s a : ℂ, SlopeConfig t₀ T₀ κ τ s a → 2 * T₀ + κ ≤ t₀ * a.re → A ≤ a.re →
      ‖(∫ u in Ioi κ, complexGauss τ (u + (2 * τ * a).im * I) *
          xi (s + (u + (2 * τ * a).im * I))) - xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ ≤
        ε * ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ := by
  have hT0 : 0 < T₀ := ht₀.trans_le hT
  have hlam0 : 0 < gaussRate t₀ T₀ := by
    rw [gaussRate]
    positivity
  have hkap0 : 0 < gaussHeight t₀ := gaussHeight_pos ht₀
  have hI₁0 : 0 ≤ ∫ v : ℝ, Real.exp (-gaussRate t₀ T₀ * v ^ 2) :=
    integral_nonneg fun v => (Real.exp_pos _).le
  have hI₈0 : 0 ≤ ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 8) * v ^ 2) :=
    integral_nonneg fun v => (Real.exp_pos _).le
  obtain ⟨I₁, hI₁⟩ : ∃ I₁ : ℝ, I₁ = ∫ v : ℝ, Real.exp (-gaussRate t₀ T₀ * v ^ 2) := ⟨_, rfl⟩
  obtain ⟨I₈, hI₈⟩ : ∃ I₈ : ℝ, I₈ = ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 8) * v ^ 2) :=
    ⟨_, rfl⟩
  rw [← hI₁] at hI₁0
  rw [← hI₈] at hI₈0
  -- the window: the Gaussian tail beyond `L` is below `ε/4`
  obtain ⟨ε₈, hε₈⟩ : ∃ ε₈ : ℝ, ε₈ = ε / (8 * gaussHeight t₀ * (I₈ + 1)) := ⟨_, rfl⟩
  have hd8 : 0 < 8 * gaussHeight t₀ * (I₈ + 1) :=
    mul_pos (mul_pos (by norm_num) hkap0) (by linarith)
  have hε₈0 : 0 < ε₈ := by
    rw [hε₈]
    exact div_pos hε hd8
  have hε₈e : ε₈ * (8 * gaussHeight t₀ * (I₈ + 1)) = ε := by
    rw [hε₈]
    exact div_mul_cancel₀ _ hd8.ne'
  obtain ⟨AL, -, hAL⟩ := exists_forall_exp_neg_quadratic_le (a := gaussRate t₀ T₀ / 8)
    (ε := ε₈) (by linarith) hε₈0 0 0
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = max (4 / gaussRate t₀ T₀) AL := ⟨_, rfl⟩
  have hL4 : 4 / gaussRate t₀ T₀ ≤ L := by
    rw [hLdef]
    exact le_max_left _ _
  have hL0 : 0 < L := lt_of_lt_of_le (div_pos (by norm_num) hlam0) hL4
  have he8 : Real.exp (-gaussRate t₀ T₀ * L ^ 2 / 8) ≤ ε₈ := by
    have h1 := hAL L (by rw [hLdef]; exact le_max_right _ _)
    have e : -(gaussRate t₀ T₀ / 8) * L ^ 2 + 0 * L + 0 = -gaussRate t₀ T₀ * L ^ 2 / 8 := by ring
    rwa [e] at h1
  -- the slope on the window: `e^{η₁L} − 1` is below `ε/4`
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (4 * gaussHeight t₀ * (I₁ + 1)) := ⟨_, rfl⟩
  have hd4 : 0 < 4 * gaussHeight t₀ * (I₁ + 1) :=
    mul_pos (mul_pos (by norm_num) hkap0) (by linarith)
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact div_pos hε hd4
  have hδe : δ * (4 * gaussHeight t₀ * (I₁ + 1)) = ε := by
    rw [hδ]
    exact div_mul_cancel₀ _ hd4.ne'
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : ℝ, η₁ = Real.log (1 + δ) / L := ⟨_, rfl⟩
  have hη₁0 : 0 < η₁ := by
    rw [hη₁]
    exact div_pos (Real.log_pos (by linarith)) hL0
  have hexp : Real.exp (η₁ * L) - 1 = δ := by
    rw [hη₁, div_mul_cancel₀ _ hL0.ne', Real.exp_log (by linarith)]
    ring
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 + 1 / (3 * t₀) + 2 * T₀ + L / 2 := ⟨_, rfl⟩
  refine ⟨max (2 * L / t₀) (K / η₁), fun τ s a h hκα hA => ?_⟩
  have hα4 := h.four_le_re
  have hα0 : 0 < a.re := by linarith
  have hLα : 2 * L ≤ t₀ * a.re := by
    have h1 := (le_max_left _ _).trans hA
    rw [div_le_iff₀ ht₀] at h1
    linarith
  have hKα : K / a.re ≤ η₁ := by
    have h1 := (le_max_right _ _).trans hA
    rw [div_le_iff₀ hη₁0] at h1
    rw [div_le_iff₀ hα0]
    linarith
  have hη : 4 / (1 + a.re) ^ 2 + 1 / (3 * (t₀ * a.re)) +
      (4 * T₀ * (1 + a.re) + L) / (2 * (1 + a.re) ^ 2) ≤ η₁ := by
    refine le_trans ?_ hKα
    have hN2 : a.re ≤ (1 + a.re) ^ 2 := by nlinarith
    have e1 : 4 / (1 + a.re) ^ 2 ≤ 4 / a.re := div_le_div_of_nonneg_left (by norm_num) hα0 hN2
    have e2 : 1 / (3 * (t₀ * a.re)) = 1 / (3 * t₀) / a.re := by rw [div_div, mul_assoc]
    have e3 : (4 * T₀ * (1 + a.re) + L) / (2 * (1 + a.re) ^ 2) ≤ (2 * T₀ + L / 2) / a.re := by
      rw [div_le_div_iff₀ (mul_pos two_pos (pow_pos (by linarith) 2)) hα0]
      nlinarith [mul_nonneg (mul_nonneg hT0.le (by linarith : (0 : ℝ) ≤ 1 + a.re))
        (by linarith : (0 : ℝ) ≤ 1 + a.re - a.re), mul_nonneg hL0.le (sub_nonneg.2 hN2)]
    have e4 : K / a.re = 4 / a.re + 1 / (3 * t₀) / a.re + (2 * T₀ + L / 2) / a.re := by
      rw [hK]
      ring
    rw [e4, e2]
    linarith
  have hmain := h.norm_ray_sub_le hκα hL4 hLα hη₁0 hη
  rw [hexp, ← hI₁, ← hI₈] at hmain
  refine hmain.trans ?_
  rw [mul_comm ε]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have b1 : 0 ≤ gaussHeight t₀ * δ := mul_nonneg hkap0.le hδ0.le
  have b2 := mul_le_mul_of_nonneg_left he8 (mul_nonneg hkap0.le hI₈0)
  have b3 : 0 ≤ gaussHeight t₀ * ε₈ := mul_nonneg hkap0.le hε₈0.le
  nlinarith

/-- The vertical side is at most `ε` times the saddle value, for `Re a` large. -/
theorem exists_norm_side_le {t₀ T₀ κ ε : ℝ} (ht₀ : 0 < t₀) (hT : t₀ ≤ T₀) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ τ s a : ℂ, SlopeConfig t₀ T₀ κ τ s a → 2 * T₀ + κ ≤ t₀ * a.re → A ≤ a.re →
      ‖∫ v in (0 : ℝ)..(2 * τ * a).im, complexGauss τ (κ + v * I) * xi (s + (κ + v * I))‖ ≤
        ε * ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ := by
  have hT0 : 0 < T₀ := ht₀.trans_le hT
  have hlam0 : 0 < gaussRate t₀ T₀ := by
    rw [gaussRate]
    positivity
  have hkap0 : 0 < gaussHeight t₀ := gaussHeight_pos ht₀
  have hc0 : 0 < gaussHeight t₀ * (2 * T₀) := mul_pos hkap0 (by linarith)
  obtain ⟨A, -, hA⟩ := exists_forall_exp_neg_quadratic_le (a := gaussRate t₀ T₀ * t₀ ^ 2)
    (ε := ε / (gaussHeight t₀ * (2 * T₀))) (mul_pos hlam0 (pow_pos ht₀ 2)) (div_pos hε hc0)
    (6 * T₀ + κ + 1) (5 * T₀)
  refine ⟨A, fun τ s a h hκα hAα => ?_⟩
  refine (h.norm_side_le hκα).trans ?_
  rw [mul_comm ε]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : 1 + a.re ≤ Real.exp a.re := by linarith [Real.add_one_le_exp a.re]
  have h2 := hA a.re hAα
  have hE : Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ + 1) * a.re +
      5 * T₀) = Real.exp a.re *
        Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc gaussHeight t₀ * (2 * T₀ * (1 + a.re)) *
        Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀)
      ≤ gaussHeight t₀ * (2 * T₀ * Real.exp a.re) *
        Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ) * a.re + 5 * T₀) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by linarith)) hkap0.le)
          (Real.exp_pos _).le
    _ = gaussHeight t₀ * (2 * T₀) *
        Real.exp (-(gaussRate t₀ T₀ * t₀ ^ 2) * a.re ^ 2 + (6 * T₀ + κ + 1) * a.re +
          5 * T₀) := by
        rw [hE]
        ring
    _ ≤ gaussHeight t₀ * (2 * T₀) * (ε / (gaussHeight t₀ * (2 * T₀))) :=
        mul_le_mul_of_nonneg_left h2 hc0.le
    _ = ε := by rw [mul_comm, div_mul_cancel₀ _ hc0.ne']

/-- The unshifted piece is at most `ε` times the saddle value, for `Re a` large. -/
theorem exists_norm_unshifted_le {t₀ T₀ κ ε : ℝ} (ht₀ : 0 < t₀) (hκ : 5 ≤ κ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ τ s a : ℂ, SlopeConfig t₀ T₀ κ τ s a → 2 * T₀ + κ ≤ t₀ * a.re → A ≤ a.re →
      ‖∫ u in (0 : ℝ)..κ, complexGauss τ u * xi (s + u)‖ ≤
        ε * ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ := by
  obtain ⟨C, hC, hstrip⟩ := exists_norm_xi_le_strip
  have hkap0 : 0 < gaussHeight t₀ := gaussHeight_pos ht₀
  have hc0 : 0 < gaussHeight t₀ * κ * (1 + 8 * C) :=
    mul_pos (mul_pos hkap0 (by linarith)) (by linarith)
  obtain ⟨A, -, hA⟩ := exists_forall_exp_neg_quadratic_le (a := t₀)
    (ε := ε / (gaussHeight t₀ * κ * (1 + 8 * C))) ht₀ (div_pos hε hc0)
    (2 * κ + 4 * T₀ + 2) (κ * (Real.log (13 + κ) / 2 + 5) + 5 * κ + 3 * T₀)
  refine ⟨A, fun τ s a h hκα hAα => ?_⟩
  refine (h.norm_unshifted_le hC hstrip hκα).trans ?_
  rw [mul_comm ε]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc gaussHeight t₀ * κ * (1 + 8 * C) *
        Real.exp (-t₀ * a.re ^ 2 + (2 * κ + 4 * T₀ + 2) * a.re +
          (κ * (Real.log (13 + κ) / 2 + 5) + 5 * κ + 3 * T₀))
      ≤ gaussHeight t₀ * κ * (1 + 8 * C) * (ε / (gaussHeight t₀ * κ * (1 + 8 * C))) :=
        mul_le_mul_of_nonneg_left (hA a.re hAα) hc0.le
    _ = ε := by rw [mul_comm, div_mul_cancel₀ _ hc0.ne']

/-! ## The saddle value -/

/-- The slope of `ξ` at the base point `s + κ`. -/
def saddleSlope (κ : ℝ) (s : ℂ) : ℂ := xiSlope (s + (κ : ℂ))

/-- The saddle value `ξ(s + 2τa) e^{−τa²}`, `a` the slope at the base point `s + κ`. -/
def saddleValue (κ : ℝ) (τ s : ℂ) : ℂ :=
  xi (s + 2 * τ * saddleSlope κ s) * cexp (-(τ * saddleSlope κ s ^ 2))

/-- A base point of large modulus has a large slope. -/
theorem le_saddleSlope_re {κ A : ℝ} {s : ℂ}
    (hs : 2 * Real.pi * Real.exp (2 * A) ≤ ‖s + (κ : ℂ)‖) : A ≤ (saddleSlope κ s).re := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpos : 0 < 2 * Real.pi * Real.exp (2 * A) := by positivity
  have h := Real.log_le_log hpos hs
  rw [Real.log_mul h2pi.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  rw [saddleSlope, xiSlope_re]
  linarith

/-- **The half line at a far point.** For `τ` in the box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` and `s` with
`Re s + κ ≥ 11/2` and `Re a ≥ A`, the integral `∫_0^∞ g_τ(u) ξ(s + u) du` is the saddle value up
to the relative error `ε`, and the saddle value does not vanish. -/
theorem exists_norm_integral_sub_saddleValue_le {t₀ κ ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀)
    (hκ : 5 ≤ κ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ τ s : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → 11 / 2 ≤ s.re + κ → A ≤ (saddleSlope κ s).re →
      saddleValue κ τ s ≠ 0 ∧
        ‖(∫ u in Ioi (0 : ℝ), complexGauss τ u * xi (s + u)) - saddleValue κ τ s‖ ≤
          ε * ‖saddleValue κ τ s‖ := by
  by_cases hT : t₀ ≤ T₀
  swap
  · exact ⟨0, fun τ s h1 h2 _ _ => absurd (h1.trans ((Complex.re_le_norm τ).trans h2)) hT⟩
  obtain ⟨A₃, hA₃⟩ := exists_norm_ray_sub_le (κ := κ) ht₀ hT (by positivity : 0 < ε / 3)
  obtain ⟨A₂, hA₂⟩ := exists_norm_side_le (κ := κ) ht₀ hT (by positivity : 0 < ε / 3)
  obtain ⟨A₁, hA₁⟩ := exists_norm_unshifted_le (T₀ := T₀) ht₀ hκ (by positivity : 0 < ε / 3)
  refine ⟨max (farThreshold t₀ T₀ κ) (max A₃ (max A₂ A₁)), fun τ s hτt hτT hs hA => ?_⟩
  have hfar := (le_max_left _ _).trans hA
  rw [farThreshold] at hfar
  have hT0 : 0 < T₀ := ht₀.trans_le hT
  have hdiv : 0 ≤ (2 * T₀ + κ) / t₀ := div_nonneg (by linarith) ht₀.le
  have hκα : 2 * T₀ + κ ≤ t₀ * (saddleSlope κ s).re := by
    have hlam : 0 < 1 / gaussRate t₀ T₀ := by
      rw [gaussRate]
      positivity
    have h1 : (2 * T₀ + κ) / t₀ ≤ (saddleSlope κ s).re := by
      rw [slopeThreshold] at hfar
      linarith
    rw [div_le_iff₀ ht₀] at h1
    linarith
  have h : SlopeConfig t₀ T₀ κ τ s (saddleSlope κ s) :=
    ⟨ht₀, hτt, hτT, hκ, hs, rfl, by linarith⟩
  have hA' := (le_max_right _ _).trans hA
  have h3 := hA₃ τ s _ h hκα ((le_max_left _ _).trans hA')
  have hA'' := (le_max_right _ _).trans hA'
  have h2 := hA₂ τ s _ h hκα ((le_max_left _ _).trans hA'')
  have h1 := hA₁ τ s _ h hκα ((le_max_right _ _).trans hA'')
  have hτ := h.τ_re_pos
  have hM : saddleValue κ τ s =
      xi (s + 2 * τ * saddleSlope κ s) * cexp (-(τ * saddleSlope κ s ^ 2)) := rfl
  refine ⟨?_, ?_⟩
  · -- the saddle point lies in `Re > 1`
    rw [hM]
    refine mul_ne_zero (xi_ne_zero_of_one_lt_re ?_) (Complex.exp_ne_zero _)
    rw [Complex.add_re]
    have e1 := h.le_re_two_mul hκα
    have e2 := h.four_le_re
    have e3 : 0 ≤ t₀ * (saddleSlope κ s).re := mul_nonneg ht₀.le (by linarith)
    linarith
  · rw [hM, integral_Ioi_zero_complexGauss_mul_xi_eq_corner hτ s κ
      (2 * τ * saddleSlope κ s).im]
    have e : ∀ J₁ J₂ J₃ M : ℂ, J₁ + I * J₂ + J₃ - M = J₁ + I * J₂ + (J₃ - M) :=
      fun _ _ _ _ => by ring
    rw [e]
    refine norm_add₃_le.trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    linarith

/-- **The half transform is `ξ` at the saddle point.** For `τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` and `z` with `Im z ≤ Y`, `‖z‖ ≥ R`, the half transform `𝒜(τ, z)` is the
saddle value `ξ(1/2 + iz + 2τa) e^{−τa²}`, `a = ½ log((1/2 + iz + Y + 5)/2π)`, up to the relative
error `ε`; the saddle value does not vanish. -/
theorem exists_halfHeat_sub_saddleValue_le {t₀ Y ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) (hY : 0 ≤ Y)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ z : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → z.im ≤ Y → R ≤ ‖z‖ →
      saddleValue (Y + 5) τ (1 / 2 + I * z) ≠ 0 ∧
        ‖halfHeat τ z - saddleValue (Y + 5) τ (1 / 2 + I * z)‖ ≤
          ε * ‖saddleValue (Y + 5) τ (1 / 2 + I * z)‖ := by
  obtain ⟨A, hA⟩ := exists_norm_integral_sub_saddleValue_le (κ := Y + 5) T₀ ht₀ (by linarith) hε
  refine ⟨2 * Real.pi * Real.exp (2 * A) + (Y + 11 / 2), fun τ z hτt hτT hz hR => ?_⟩
  have hre : (1 / 2 + I * z : ℂ).re = 1 / 2 - z.im := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have hs : 11 / 2 ≤ (1 / 2 + I * z : ℂ).re + (Y + 5) := by
    rw [hre]
    linarith
  have hb : 2 * Real.pi * Real.exp (2 * A) ≤ ‖(1 / 2 + I * z : ℂ) + ((Y + 5 : ℝ) : ℂ)‖ := by
    have e : (1 / 2 + I * z : ℂ) + ((Y + 5 : ℝ) : ℂ) = I * z - (-((Y + 11 / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    have h1 := norm_sub_norm_le (I * z) (-((Y + 11 / 2 : ℝ) : ℂ))
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)] at h1
    rw [e]
    linarith
  exact hA τ (1 / 2 + I * z) hτt hτT hs (le_saddleSlope_re hb)

end

end GaloisForLFunctions.GaloisTheoryOfZeros
