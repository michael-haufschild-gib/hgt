import GaloisForLFunctions.RHTower.XiWeilTwoChannelResolvent

/-!
# The finite-aperture two-channel resolvent family

The two canonical resolvent channels are the Fourier transforms, in the convention
`f̂ (z) = ∫ f x exp (i z x) dx`, of the two-sided exponential sources

```
u_w^A (x) = exp (-(w |x|)) / 2,     u_w^B (x) = sgn x · exp (-(w |x|)) / (2 i).
```

Truncating the sources to `[-a, a]` replaces each Hardy orientation `1 / (w ∓ i z)` by its
incomplete form `(1 - exp (-((w ∓ i z) a))) / (w ∓ i z)`.  On the centred Xi divisor the exponential
defect is bounded by `exp (-(Re w - 1/2) a)` uniformly in the zero, so the truncated two-channel
Weil Gram converges to the exact one at every finite node system, and the negative index of the
exact form is already visible at a finite aperture.
-/

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ComplexOrder

namespace RHTower

/-! ### The truncated Hardy orientations -/

/-- The forward truncated Hardy orientation, the right half of the aperture integral. -/
def weilApertureRight (w : ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..a, Complex.exp (-((w - Complex.I * z) * (x : ℝ)))

/-- The backward truncated Hardy orientation, the left half of the aperture integral. -/
def weilApertureLeft (w : ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x in (-a)..(0 : ℝ), Complex.exp ((w + Complex.I * z) * (x : ℝ))

theorem weilApertureRight_eq {w z : ℂ} (h : w - Complex.I * z ≠ 0) (a : ℝ) :
    weilApertureRight w a z
      = (1 - Complex.exp (-((w - Complex.I * z) * (a : ℝ)))) / (w - Complex.I * z) := by
  have hc : -(w - Complex.I * z) ≠ 0 := neg_ne_zero.mpr h
  have hcongr : ∀ x : ℝ, Complex.exp (-((w - Complex.I * z) * (x : ℝ)))
      = Complex.exp (-(w - Complex.I * z) * (x : ℝ)) := by
    intro x
    congr 1
    ring
  rw [weilApertureRight, intervalIntegral.integral_congr (fun x _ => hcongr x),
    integral_exp_mul_complex hc]
  push_cast
  field_simp
  simp only [mul_zero, neg_zero, Complex.exp_zero]
  ring

theorem weilApertureLeft_eq {w z : ℂ} (h : w + Complex.I * z ≠ 0) (a : ℝ) :
    weilApertureLeft w a z
      = (1 - Complex.exp (-((w + Complex.I * z) * (a : ℝ)))) / (w + Complex.I * z) := by
  rw [weilApertureLeft, integral_exp_mul_complex h]
  push_cast
  field_simp
  simp only [mul_zero, Complex.exp_zero]

/-- The aperture-`a` even channel `A_{w,a}`. -/
def weilApertureA (w : ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  (weilApertureRight w a z + weilApertureLeft w a z) / 2

/-- The aperture-`a` odd channel `B_{w,a}`. -/
def weilApertureB (w : ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  (weilApertureRight w a z - weilApertureLeft w a z) / (2 * Complex.I)

/-- **Equation (24).** -/
theorem weilApertureA_eq {w z : ℂ} (h1 : w - Complex.I * z ≠ 0) (h2 : w + Complex.I * z ≠ 0)
    (a : ℝ) :
    weilApertureA w a z
      = ((1 - Complex.exp (-((w - Complex.I * z) * (a : ℝ)))) / (w - Complex.I * z)
        + (1 - Complex.exp (-((w + Complex.I * z) * (a : ℝ)))) / (w + Complex.I * z)) / 2 := by
  rw [weilApertureA, weilApertureRight_eq h1, weilApertureLeft_eq h2]

/-- **Equation (25).** -/
theorem weilApertureB_eq {w z : ℂ} (h1 : w - Complex.I * z ≠ 0) (h2 : w + Complex.I * z ≠ 0)
    (a : ℝ) :
    weilApertureB w a z
      = ((1 - Complex.exp (-((w - Complex.I * z) * (a : ℝ)))) / (w - Complex.I * z)
        - (1 - Complex.exp (-((w + Complex.I * z) * (a : ℝ)))) / (w + Complex.I * z))
          / (2 * Complex.I) := by
  rw [weilApertureB, weilApertureRight_eq h1, weilApertureLeft_eq h2]

/-! ### The aperture channels are the truncated Fourier transforms -/

/-- **Equations (21)-(22).**  The even aperture channel is the Fourier transform, in the card's
convention, of the truncated two-sided exponential source. -/
theorem weilApertureA_eq_fourier (w z : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    weilApertureA w a z
      = ∫ x in (-a)..a,
          Complex.exp (-(w * (|x| : ℝ))) / 2 * Complex.exp (Complex.I * z * (x : ℝ)) := by
  have hcont : Continuous fun x : ℝ =>
      Complex.exp (-(w * (|x| : ℝ))) / 2 * Complex.exp (Complex.I * z * (x : ℝ)) := by
    fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (a := -a) (b := 0) (c := a) (f := fun x : ℝ =>
      Complex.exp (-(w * (|x| : ℝ))) / 2 * Complex.exp (Complex.I * z * (x : ℝ)))
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [← hsplit, weilApertureA]
  have hleft : (∫ x in (-a)..(0 : ℝ),
      Complex.exp (-(w * (|x| : ℝ))) / 2 * Complex.exp (Complex.I * z * (x : ℝ)))
      = weilApertureLeft w a z / 2 := by
    rw [weilApertureLeft, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hle : -a ≤ (0 : ℝ) := by linarith
    rw [Set.uIcc_of_le hle] at hx
    have habs : (|x| : ℝ) = -x := abs_of_nonpos hx.2
    rw [habs, div_mul_eq_mul_div, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hright : (∫ x in (0 : ℝ)..a,
      Complex.exp (-(w * (|x| : ℝ))) / 2 * Complex.exp (Complex.I * z * (x : ℝ)))
      = weilApertureRight w a z / 2 := by
    rw [weilApertureRight, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le ha] at hx
    have habs : (|x| : ℝ) = x := abs_of_nonneg hx.1
    rw [habs, div_mul_eq_mul_div, ← Complex.exp_add]
    congr 2
    ring
  rw [hleft, hright]
  ring

/-! ### Equation (23): the aperture channels converge to the exact channels -/

theorem tendsto_exp_neg_mul_atTop {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun a : ℝ => Complex.exp (-(c * (a : ℝ)))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ a : ℝ, ‖Complex.exp (-(c * (a : ℝ)))‖ = Real.exp (-(c.re * a)) := by
    intro a
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  simp only [hnorm]
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hc tendsto_id))

theorem norm_exp_neg_mul_le_one {c : ℂ} (hc : 0 ≤ c.re) {a : ℝ} (ha : 0 ≤ a) :
    ‖Complex.exp (-(c * (a : ℝ)))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (-(c * (a : ℝ))).re = -(c.re * a) := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_le_one_iff]
  nlinarith

theorem sq_add_sq_ne_zero_of_re_pos {w z : ℂ} (h1 : 0 < (w - Complex.I * z).re)
    (h2 : 0 < (w + Complex.I * z).re) : w ^ 2 + z ^ 2 ≠ 0 := by
  have hn1 : w - Complex.I * z ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  have hn2 : w + Complex.I * z ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
  have hfac : w ^ 2 + z ^ 2 = (w - Complex.I * z) * (w + Complex.I * z) := by
    linear_combination (z ^ 2) * Complex.I_mul_I
  rw [hfac]
  exact mul_ne_zero hn1 hn2

theorem tendsto_weilApertureA {w z : ℂ} (h1 : 0 < (w - Complex.I * z).re)
    (h2 : 0 < (w + Complex.I * z).re) :
    Tendsto (fun a : ℝ => weilApertureA w a z) atTop (𝓝 (weilChannelA w z)) := by
  have hn1 : w - Complex.I * z ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hn2 : w + Complex.I * z ≠ 0 := by
    intro h; rw [h] at h2; simp at h2
  have hsq := sq_add_sq_ne_zero_of_re_pos h1 h2
  have heq : ((1 - (0 : ℂ)) / (w - Complex.I * z) + (1 - 0) / (w + Complex.I * z)) / 2
      = weilChannelA w z := by
    rw [weilChannelA_eq_resolvent hsq, weilResolventPlus, weilResolventMinus]
    ring
  rw [← heq]
  simp only [fun a : ℝ => weilApertureA_eq hn1 hn2 a]
  exact ((((tendsto_const_nhds.sub (tendsto_exp_neg_mul_atTop h1)).div_const _).add
    ((tendsto_const_nhds.sub (tendsto_exp_neg_mul_atTop h2)).div_const _)).div_const _)

theorem tendsto_weilApertureB {w z : ℂ} (h1 : 0 < (w - Complex.I * z).re)
    (h2 : 0 < (w + Complex.I * z).re) :
    Tendsto (fun a : ℝ => weilApertureB w a z) atTop (𝓝 (weilChannelB w z)) := by
  have hn1 : w - Complex.I * z ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hn2 : w + Complex.I * z ≠ 0 := by
    intro h; rw [h] at h2; simp at h2
  have hsq := sq_add_sq_ne_zero_of_re_pos h1 h2
  have heq : ((1 - (0 : ℂ)) / (w - Complex.I * z) - (1 - 0) / (w + Complex.I * z))
      / (2 * Complex.I) = weilChannelB w z := by
    rw [weilChannelB_eq_resolvent hsq, weilResolventPlus, weilResolventMinus]
    ring
  rw [← heq]
  simp only [fun a : ℝ => weilApertureB_eq hn1 hn2 a]
  exact ((((tendsto_const_nhds.sub (tendsto_exp_neg_mul_atTop h1)).div_const _).sub
    ((tendsto_const_nhds.sub (tendsto_exp_neg_mul_atTop h2)).div_const _)).div_const _)

/-! ### Equation (28): the uniform aperture bound -/

theorem norm_weilApertureA_le {w z : ℂ} (h1 : 0 ≤ (w - Complex.I * z).re)
    (h2 : 0 ≤ (w + Complex.I * z).re) {a : ℝ} (ha : 0 ≤ a)
    (hn1 : w - Complex.I * z ≠ 0) (hn2 : w + Complex.I * z ≠ 0) :
    ‖weilApertureA w a z‖ ≤ 1 / ‖w - Complex.I * z‖ + 1 / ‖w + Complex.I * z‖ := by
  have hb1 : ‖(1 - Complex.exp (-((w - Complex.I * z) * (a : ℝ)))) / (w - Complex.I * z)‖
      ≤ 2 / ‖w - Complex.I * z‖ := by
    rw [norm_div]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (norm_sub_le _ _) ?_
    have := norm_exp_neg_mul_le_one h1 ha
    simp only [norm_one]
    linarith
  have hb2 : ‖(1 - Complex.exp (-((w + Complex.I * z) * (a : ℝ)))) / (w + Complex.I * z)‖
      ≤ 2 / ‖w + Complex.I * z‖ := by
    rw [norm_div]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (norm_sub_le _ _) ?_
    have := norm_exp_neg_mul_le_one h2 ha
    simp only [norm_one]
    linarith
  rw [weilApertureA_eq hn1 hn2, norm_div, Complex.norm_ofNat]
  have hsum := le_trans (norm_add_le _ _) (add_le_add hb1 hb2)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have h1n : (0:ℝ) < ‖w - Complex.I * z‖ := norm_pos_iff.mpr hn1
  have h2n : (0:ℝ) < ‖w + Complex.I * z‖ := norm_pos_iff.mpr hn2
  have hd1 : 2 / ‖w - Complex.I * z‖ = 2 * (1 / ‖w - Complex.I * z‖) := by ring
  have hd2 : 2 / ‖w + Complex.I * z‖ = 2 * (1 / ‖w + Complex.I * z‖) := by ring
  rw [hd1, hd2] at hsum
  linarith

theorem norm_weilApertureB_le {w z : ℂ} (h1 : 0 ≤ (w - Complex.I * z).re)
    (h2 : 0 ≤ (w + Complex.I * z).re) {a : ℝ} (ha : 0 ≤ a)
    (hn1 : w - Complex.I * z ≠ 0) (hn2 : w + Complex.I * z ≠ 0) :
    ‖weilApertureB w a z‖ ≤ 1 / ‖w - Complex.I * z‖ + 1 / ‖w + Complex.I * z‖ := by
  have hb1 : ‖(1 - Complex.exp (-((w - Complex.I * z) * (a : ℝ)))) / (w - Complex.I * z)‖
      ≤ 2 / ‖w - Complex.I * z‖ := by
    rw [norm_div]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (norm_sub_le _ _) ?_
    have := norm_exp_neg_mul_le_one h1 ha
    simp only [norm_one]
    linarith
  have hb2 : ‖(1 - Complex.exp (-((w + Complex.I * z) * (a : ℝ)))) / (w + Complex.I * z)‖
      ≤ 2 / ‖w + Complex.I * z‖ := by
    rw [norm_div]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (norm_sub_le _ _) ?_
    have := norm_exp_neg_mul_le_one h2 ha
    simp only [norm_one]
    linarith
  have hnorm2I : ‖(2 : ℂ) * Complex.I‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  rw [weilApertureB_eq hn1 hn2, norm_div, hnorm2I]
  have hsum := le_trans (norm_sub_le _ _) (add_le_add hb1 hb2)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have hd1 : 2 / ‖w - Complex.I * z‖ = 2 * (1 / ‖w - Complex.I * z‖) := by ring
  have hd2 : 2 / ‖w + Complex.I * z‖ = 2 * (1 / ‖w + Complex.I * z‖) := by ring
  rw [hd1, hd2] at hsum
  linarith

/-! ### The sharp involution on the aperture channels -/

theorem weilApertureLeft_eq_exp (w : ℂ) (a : ℝ) (z : ℂ) :
    weilApertureLeft w a z
      = ∫ x in (0 : ℝ)..a, Complex.exp (-((w + Complex.I * z) * (x : ℝ))) := by
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => Complex.exp ((w + Complex.I * z) * (x : ℝ))) (a := (0 : ℝ)) (b := a)
  rw [neg_zero] at hcomp
  rw [weilApertureLeft, ← hcomp]
  refine intervalIntegral.integral_congr fun x _ => ?_
  congr 1
  push_cast
  ring

theorem conj_weilApertureRight (w : ℂ) (a : ℝ) (z : ℂ) :
    conj (weilApertureRight w a (conj z)) = weilApertureLeft (conj w) a z := by
  rw [weilApertureRight, weilApertureLeft_eq_exp, ← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, map_sub, Complex.conj_I, Complex.conj_conj,
    Complex.conj_ofReal]
  ring

theorem conj_weilApertureLeft (w : ℂ) (a : ℝ) (z : ℂ) :
    conj (weilApertureLeft w a (conj z)) = weilApertureRight (conj w) a z := by
  rw [weilApertureLeft_eq_exp, weilApertureRight, ← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, map_add, Complex.conj_I, Complex.conj_conj,
    Complex.conj_ofReal]
  ring

theorem xiWeilSharp_weilApertureA (v : ℂ) (a : ℝ) :
    xiWeilSharp (weilApertureA v a) = weilApertureA (conj v) a := by
  funext z
  rw [xiWeilSharp, weilApertureA, weilApertureA, map_div₀, map_add, conj_weilApertureRight,
    conj_weilApertureLeft, Complex.conj_ofNat]
  ring

theorem xiWeilSharp_weilApertureB (v : ℂ) (a : ℝ) :
    xiWeilSharp (weilApertureB v a) = weilApertureB (conj v) a := by
  funext z
  have hconj2I : conj ((2 : ℂ) * Complex.I) = -(2 * Complex.I) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofNat]
    ring
  rw [xiWeilSharp, weilApertureB, weilApertureB, map_div₀, map_sub, conj_weilApertureRight,
    conj_weilApertureLeft, hconj2I]
  have hne : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  field_simp
  ring

/-! ### Uniform bounds on the divisor -/

theorem re_sub_I_spectral_ge {w : ℂ} (q : XiZeroCopy) :
    w.re - 1 / 2 ≤ (w - Complex.I * xiSpectralPoint q).re := by
  have hb := abs_le.mp (abs_im_xiSpectralPoint_le q)
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, sub_neg_eq_add]
  linarith [hb.1]

theorem re_add_I_spectral_ge {w : ℂ} (q : XiZeroCopy) :
    w.re - 1 / 2 ≤ (w + Complex.I * xiSpectralPoint q).re := by
  have hb := abs_le.mp (abs_im_xiSpectralPoint_le q)
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub]
  linarith [hb.2]

theorem norm_weilApertureA_spectral_le {w : ℂ} (hw : 1 / 2 < w.re) (q : XiZeroCopy)
    {a : ℝ} (ha : 0 ≤ a) :
    ‖weilApertureA w a (xiSpectralPoint q)‖ ≤ 2 / (w.re - 1 / 2) := by
  have hδ : 0 < w.re - 1 / 2 := by linarith
  have h1 := re_sub_I_spectral_ge (w := w) q
  have h2 := re_add_I_spectral_ge (w := w) q
  have hn1 : w - Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h1
    linarith
  have hn2 : w + Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h2
    linarith
  have hb1 : w.re - 1 / 2 ≤ ‖w - Complex.I * xiSpectralPoint q‖ :=
    le_trans h1 (Complex.re_le_norm _)
  have hb2 : w.re - 1 / 2 ≤ ‖w + Complex.I * xiSpectralPoint q‖ :=
    le_trans h2 (Complex.re_le_norm _)
  refine le_trans (norm_weilApertureA_le (by linarith) (by linarith) ha hn1 hn2) ?_
  have hd1 : 1 / ‖w - Complex.I * xiSpectralPoint q‖ ≤ 1 / (w.re - 1 / 2) :=
    one_div_le_one_div_of_le hδ hb1
  have hd2 : 1 / ‖w + Complex.I * xiSpectralPoint q‖ ≤ 1 / (w.re - 1 / 2) :=
    one_div_le_one_div_of_le hδ hb2
  have : 2 / (w.re - 1 / 2) = 1 / (w.re - 1 / 2) + 1 / (w.re - 1 / 2) := by ring
  rw [this]
  linarith

theorem norm_weilApertureB_spectral_le {w : ℂ} (hw : 1 / 2 < w.re) (q : XiZeroCopy)
    {a : ℝ} (ha : 0 ≤ a) :
    ‖weilApertureB w a (xiSpectralPoint q)‖ ≤ 2 / (w.re - 1 / 2) := by
  have hδ : 0 < w.re - 1 / 2 := by linarith
  have h1 := re_sub_I_spectral_ge (w := w) q
  have h2 := re_add_I_spectral_ge (w := w) q
  have hn1 : w - Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h1
    linarith
  have hn2 : w + Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h2
    linarith
  have hb1 : w.re - 1 / 2 ≤ ‖w - Complex.I * xiSpectralPoint q‖ :=
    le_trans h1 (Complex.re_le_norm _)
  have hb2 : w.re - 1 / 2 ≤ ‖w + Complex.I * xiSpectralPoint q‖ :=
    le_trans h2 (Complex.re_le_norm _)
  refine le_trans (norm_weilApertureB_le (by linarith) (by linarith) ha hn1 hn2) ?_
  have hd1 : 1 / ‖w - Complex.I * xiSpectralPoint q‖ ≤ 1 / (w.re - 1 / 2) :=
    one_div_le_one_div_of_le hδ hb1
  have hd2 : 1 / ‖w + Complex.I * xiSpectralPoint q‖ ≤ 1 / (w.re - 1 / 2) :=
    one_div_le_one_div_of_le hδ hb2
  have : 2 / (w.re - 1 / 2) = 1 / (w.re - 1 / 2) + 1 / (w.re - 1 / 2) := by ring
  rw [this]
  linarith

theorem norm_weilApertureA_spectral_le' {w : ℂ} (hw : 1 / 2 < w.re) {q : XiZeroCopy}
    (hq : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) {a : ℝ} (ha : 0 ≤ a) :
    ‖weilApertureA w a (xiSpectralPoint q)‖ ≤ 4 / ‖xiSpectralPoint q‖ := by
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have h1 := re_sub_I_spectral_ge (w := w) q
  have h2 := re_add_I_spectral_ge (w := w) q
  have hn1 : w - Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h1
    linarith
  have hn2 : w + Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h2
    linarith
  have hb1 := norm_sub_I_mul_spectral_ge hq
  have hb2 := norm_add_I_mul_spectral_ge hq
  refine le_trans (norm_weilApertureA_le (by linarith) (by linarith) ha hn1 hn2) ?_
  have hd1 : 1 / ‖w - Complex.I * xiSpectralPoint q‖ ≤ 1 / (‖xiSpectralPoint q‖ / 2) :=
    one_div_le_one_div_of_le (by positivity) hb1
  have hd2 : 1 / ‖w + Complex.I * xiSpectralPoint q‖ ≤ 1 / (‖xiSpectralPoint q‖ / 2) :=
    one_div_le_one_div_of_le (by positivity) hb2
  have hval : 1 / (‖xiSpectralPoint q‖ / 2) = 2 / ‖xiSpectralPoint q‖ := by
    field_simp
  rw [hval] at hd1 hd2
  have : 4 / ‖xiSpectralPoint q‖ = 2 / ‖xiSpectralPoint q‖ + 2 / ‖xiSpectralPoint q‖ := by ring
  rw [this]
  linarith

theorem norm_weilApertureB_spectral_le' {w : ℂ} (hw : 1 / 2 < w.re) {q : XiZeroCopy}
    (hq : 2 * ‖w‖ ≤ ‖xiSpectralPoint q‖) {a : ℝ} (ha : 0 ≤ a) :
    ‖weilApertureB w a (xiSpectralPoint q)‖ ≤ 4 / ‖xiSpectralPoint q‖ := by
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have h1 := re_sub_I_spectral_ge (w := w) q
  have h2 := re_add_I_spectral_ge (w := w) q
  have hn1 : w - Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h1
    linarith
  have hn2 : w + Complex.I * xiSpectralPoint q ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at h2
    linarith
  have hb1 := norm_sub_I_mul_spectral_ge hq
  have hb2 := norm_add_I_mul_spectral_ge hq
  refine le_trans (norm_weilApertureB_le (by linarith) (by linarith) ha hn1 hn2) ?_
  have hd1 : 1 / ‖w - Complex.I * xiSpectralPoint q‖ ≤ 1 / (‖xiSpectralPoint q‖ / 2) :=
    one_div_le_one_div_of_le (by positivity) hb1
  have hd2 : 1 / ‖w + Complex.I * xiSpectralPoint q‖ ≤ 1 / (‖xiSpectralPoint q‖ / 2) :=
    one_div_le_one_div_of_le (by positivity) hb2
  have hval : 1 / (‖xiSpectralPoint q‖ / 2) = 2 / ‖xiSpectralPoint q‖ := by
    field_simp
  rw [hval] at hd1 hd2
  have : 4 / ‖xiSpectralPoint q‖ = 2 / ‖xiSpectralPoint q‖ + 2 / ‖xiSpectralPoint q‖ := by ring
  rw [this]
  linarith

end RHTower
