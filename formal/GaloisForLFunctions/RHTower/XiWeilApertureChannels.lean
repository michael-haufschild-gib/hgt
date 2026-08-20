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

/-! ### Equation (27): exponential Weil-form convergence -/

/-- The uniform dominating constant of the aperture channel products. -/
def apertureDominant (w u : ℂ) : ℝ :=
  16 + 4 * (2 * max ‖w‖ ‖u‖) ^ 2 / ((w.re - 1 / 2) * (u.re - 1 / 2))

theorem apertureDominant_bound {w u : ℂ} (hw : 1 / 2 < w.re) (hu : 1 / 2 < u.re)
    {q : XiZeroCopy} {p r : ℝ} (hr : 0 ≤ r)
    (hglob : p ≤ 2 / (w.re - 1 / 2)) (hglob' : r ≤ 2 / (u.re - 1 / 2))
    (hfar : 2 * max ‖w‖ ‖u‖ ≤ ‖xiSpectralPoint q‖ →
      p ≤ 4 / ‖xiSpectralPoint q‖ ∧ r ≤ 4 / ‖xiSpectralPoint q‖) :
    p * r ≤ apertureDominant w u / ‖xiSpectralPoint q‖ ^ 2 := by
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hdw : 0 < w.re - 1 / 2 := by linarith
  have hdu : 0 < u.re - 1 / 2 := by linarith
  set M : ℝ := 2 * max ‖w‖ ‖u‖ with hM
  have hMnn : 0 ≤ M := by positivity
  by_cases hcase : M ≤ ‖xiSpectralPoint q‖
  · obtain ⟨hp4, hr4⟩ := hfar hcase
    have hprod : p * r ≤ (4 / ‖xiSpectralPoint q‖) * (4 / ‖xiSpectralPoint q‖) :=
      mul_le_mul hp4 hr4 hr (by positivity)
    have hval : (4 / ‖xiSpectralPoint q‖) * (4 / ‖xiSpectralPoint q‖)
        = 16 / ‖xiSpectralPoint q‖ ^ 2 := by
      field_simp
      ring
    rw [hval] at hprod
    refine hprod.trans ?_
    rw [apertureDominant, div_le_div_iff₀ (by positivity) (by positivity)]
    have hextra : 0 ≤ 4 * M ^ 2 / ((w.re - 1 / 2) * (u.re - 1 / 2)) := by positivity
    nlinarith [hextra, sq_nonneg ‖xiSpectralPoint q‖, hpos]
  · rw [not_le] at hcase
    have hprod : p * r ≤ (2 / (w.re - 1 / 2)) * (2 / (u.re - 1 / 2)) :=
      mul_le_mul hglob hglob' hr (by positivity)
    refine hprod.trans ?_
    rw [apertureDominant]
    have hkey : (2 / (w.re - 1 / 2)) * (2 / (u.re - 1 / 2))
        ≤ (4 * M ^ 2 / ((w.re - 1 / 2) * (u.re - 1 / 2))) / ‖xiSpectralPoint q‖ ^ 2 := by
      rw [div_mul_div_comm, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : ‖xiSpectralPoint q‖ ^ 2 ≤ M ^ 2 := by nlinarith [hcase, hpos, hMnn]
      nlinarith [hsq, mul_pos hdw hdu]
    refine hkey.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (0 : ℝ) ≤ 16 := by norm_num
    nlinarith [h16, sq_nonneg ‖xiSpectralPoint q‖, hpos,
      div_nonneg (by positivity : (0:ℝ) ≤ 4 * M ^ 2) (le_of_lt (mul_pos hdw hdu))]

theorem summable_apertureDominant (w u : ℂ) :
    Summable (fun q : XiZeroCopy => apertureDominant w u / ‖xiSpectralPoint q‖ ^ 2) := by
  refine (xiSpectralPoint_inv_sq_summable.mul_left (apertureDominant w u)).congr fun q => ?_
  rw [mul_one_div]

theorem re_sub_I_spectral_pos {w : ℂ} (hw : 1 / 2 < w.re) (q : XiZeroCopy) :
    0 < (w - Complex.I * xiSpectralPoint q).re :=
  lt_of_lt_of_le (by linarith) (re_sub_I_spectral_ge q)

theorem re_add_I_spectral_pos {w : ℂ} (hw : 1 / 2 < w.re) (q : XiZeroCopy) :
    0 < (w + Complex.I * xiSpectralPoint q).re :=
  lt_of_lt_of_le (by linarith) (re_add_I_spectral_ge q)

theorem tendsto_xiWeilPolarization_apertureA {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    Tendsto (fun a : ℝ => xiWeilPolarization (weilApertureA w a) (weilApertureA v a)) atTop
      (𝓝 (xiWeilPolarization (weilChannelA w) (weilChannelA v))) := by
  have hcv : 1 / 2 < (conj v).re := by
    rwa [Complex.conj_re]
  simp only [xiWeilPolarization, xiWeilSharp_weilApertureA, xiWeilSharp_channelA]
  refine tendsto_tsum_of_dominated_convergence (summable_apertureDominant w (conj v))
    (fun q => ?_) ?_
  · exact (tendsto_weilApertureA (re_sub_I_spectral_pos hw q) (re_add_I_spectral_pos hw q)).mul
      (tendsto_weilApertureA (re_sub_I_spectral_pos hcv q) (re_add_I_spectral_pos hcv q))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha q
    rw [norm_mul]
    refine apertureDominant_bound hw hcv (norm_nonneg _)
      (norm_weilApertureA_spectral_le hw q ha) (norm_weilApertureA_spectral_le hcv q ha)
      (fun hfar => ⟨norm_weilApertureA_spectral_le' hw
        (le_trans (by linarith [le_max_left ‖w‖ ‖(conj v)‖]) hfar) ha,
        norm_weilApertureA_spectral_le' hcv
        (le_trans (by linarith [le_max_right ‖w‖ ‖(conj v)‖]) hfar) ha⟩)

theorem tendsto_xiWeilPolarization_apertureB {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    Tendsto (fun a : ℝ => xiWeilPolarization (weilApertureB w a) (weilApertureB v a)) atTop
      (𝓝 (xiWeilPolarization (weilChannelB w) (weilChannelB v))) := by
  have hcv : 1 / 2 < (conj v).re := by
    rwa [Complex.conj_re]
  simp only [xiWeilPolarization, xiWeilSharp_weilApertureB, xiWeilSharp_channelB]
  refine tendsto_tsum_of_dominated_convergence (summable_apertureDominant w (conj v))
    (fun q => ?_) ?_
  · exact (tendsto_weilApertureB (re_sub_I_spectral_pos hw q) (re_add_I_spectral_pos hw q)).mul
      (tendsto_weilApertureB (re_sub_I_spectral_pos hcv q) (re_add_I_spectral_pos hcv q))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha q
    rw [norm_mul]
    refine apertureDominant_bound hw hcv (norm_nonneg _)
      (norm_weilApertureB_spectral_le hw q ha) (norm_weilApertureB_spectral_le hcv q ha)
      (fun hfar => ⟨norm_weilApertureB_spectral_le' hw
        (le_trans (by linarith [le_max_left ‖w‖ ‖(conj v)‖]) hfar) ha,
        norm_weilApertureB_spectral_le' hcv
        (le_trans (by linarith [le_max_right ‖w‖ ‖(conj v)‖]) hfar) ha⟩)

/-- The aperture-`a` two-channel Weil Gram kernel. -/
def apertureTwoChannelKernel (a : ℝ) (x y : {W : ℂ // 1 / 2 < W.re}) : ℂ :=
  xiWeilPolarization (weilApertureA (x : ℂ) a) (weilApertureA (y : ℂ) a)
    + xiWeilPolarization (weilApertureB (x : ℂ) a) (weilApertureB (y : ℂ) a)

/-- **Equation (27).**  The finite-aperture two-channel Weil Gram converges to the exact one. -/
theorem tendsto_apertureTwoChannelKernel (x y : {W : ℂ // 1 / 2 < W.re}) :
    Tendsto (fun a : ℝ => apertureTwoChannelKernel a x y) atTop (𝓝 (twoChannelKernel x y)) := by
  rw [twoChannelKernel]
  exact (tendsto_xiWeilPolarization_apertureA x.2 y.2).add
    (tendsto_xiWeilPolarization_apertureB x.2 y.2)

/-! ### Equations (30)-(32): index-faithful finite-aperture transport -/

theorem xiWeilSquareSummable_weilApertureA {w : ℂ} (hw : 1 / 2 < w.re) {a : ℝ} (ha : 0 ≤ a) :
    XiWeilSquareSummable (weilApertureA w a) := by
  refine Summable.of_norm_bounded (summable_apertureDominant w w) (fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact apertureDominant_bound hw hw (norm_nonneg _)
    (norm_weilApertureA_spectral_le hw q ha) (norm_weilApertureA_spectral_le hw q ha)
    (fun hfar => ⟨norm_weilApertureA_spectral_le' hw
        (le_trans (by simp) hfar) ha,
      norm_weilApertureA_spectral_le' hw (le_trans (by simp) hfar) ha⟩)

theorem xiWeilSquareSummable_weilApertureB {w : ℂ} (hw : 1 / 2 < w.re) {a : ℝ} (ha : 0 ≤ a) :
    XiWeilSquareSummable (weilApertureB w a) := by
  refine Summable.of_norm_bounded (summable_apertureDominant w w) (fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact apertureDominant_bound hw hw (norm_nonneg _)
    (norm_weilApertureB_spectral_le hw q ha) (norm_weilApertureB_spectral_le hw q ha)
    (fun hfar => ⟨norm_weilApertureB_spectral_le' hw
        (le_trans (by simp) hfar) ha,
      norm_weilApertureB_spectral_le' hw (le_trans (by simp) hfar) ha⟩)

/-- The even aperture packet `A_{c,a}`. -/
def aperturePacketA {n : ℕ} (a : ℝ) (c : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) : ℂ → ℂ :=
  fun z => ∑ j, c j * weilApertureA ((w j : ℂ)) a z

/-- The odd aperture packet `B_{c,a}`. -/
def aperturePacketB {n : ℕ} (a : ℝ) (c : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) : ℂ → ℂ :=
  fun z => ∑ j, c j * weilApertureB ((w j : ℂ)) a z

theorem xiWeilPolarization_aperturePacketA {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (c d : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    xiWeilPolarization (aperturePacketA a c w) (aperturePacketA a d w)
      = ∑ j, ∑ k, c j * conj (d k)
          * xiWeilPolarization (weilApertureA ((w j : ℂ)) a) (weilApertureA ((w k : ℂ)) a) := by
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      XiWeilSquareSummable (weilApertureA ((w j : ℂ)) a) :=
    fun j _ => xiWeilSquareSummable_weilApertureA (w j).2 ha
  unfold aperturePacketA
  rw [xiWeilPolarization_finsetSum_left hsum c (XiWeilSquareSummable.finsetSum hsum d)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [xiWeilPolarization_finsetSum_right hsum d (hsum j (Finset.mem_univ j)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem xiWeilPolarization_aperturePacketB {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (c d : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    xiWeilPolarization (aperturePacketB a c w) (aperturePacketB a d w)
      = ∑ j, ∑ k, c j * conj (d k)
          * xiWeilPolarization (weilApertureB ((w j : ℂ)) a) (weilApertureB ((w k : ℂ)) a) := by
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      XiWeilSquareSummable (weilApertureB ((w j : ℂ)) a) :=
    fun j _ => xiWeilSquareSummable_weilApertureB (w j).2 ha
  unfold aperturePacketB
  rw [xiWeilPolarization_finsetSum_left hsum c (XiWeilSquareSummable.finsetSum hsum d)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [xiWeilPolarization_finsetSum_right hsum d (hsum j (Finset.mem_univ j)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem aperture_packet_eq_kernelEnergy {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (c : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    xiWeilPolarization (aperturePacketA a c w) (aperturePacketA a c w)
        + xiWeilPolarization (aperturePacketB a c w) (aperturePacketB a c w)
      = kernelEnergy (apertureTwoChannelKernel a) (fun j => conj (c j)) w := by
  rw [xiWeilPolarization_aperturePacketA ha, xiWeilPolarization_aperturePacketB ha, kernelEnergy,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [apertureTwoChannelKernel, Complex.conj_conj]
  ring

theorem tendsto_kernelEnergy_aperture {n : ℕ} (c : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    Tendsto (fun a : ℝ => kernelEnergy (apertureTwoChannelKernel a) c w) atTop
      (𝓝 (kernelEnergy twoChannelKernel c w)) := by
  simp only [kernelEnergy]
  refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => ?_
  exact (tendsto_apertureTwoChannelKernel (w j) (w k)).const_mul _

/-- **Equation (30).**  A negative exact two-channel energy is already negative at every
sufficiently large finite aperture. -/
theorem eventually_aperture_energy_neg {n : ℕ} {c : Fin n → ℂ}
    {w : Fin n → {W : ℂ // 1 / 2 < W.re}}
    (h : (kernelEnergy twoChannelKernel c w).re < 0) :
    ∀ᶠ a : ℝ in atTop, (kernelEnergy (apertureTwoChannelKernel a) c w).re < 0 :=
  ((Complex.continuous_re.tendsto _).comp (tendsto_kernelEnergy_aperture c w)).eventually_lt_const h

/-- **Equation (32).**  Nonnegativity of every finite-aperture two-channel Weil form is exactly the
Riemann hypothesis. -/
theorem riemannHypothesis_iff_forall_aperture_energy_nonneg :
    RiemannHypothesis ↔
      ∀ a : ℝ, 0 ≤ a → ∀ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}),
        0 ≤ (kernelEnergy (apertureTwoChannelKernel a) c w).re := by
  constructor
  · intro hRH a ha n c w
    have hval := aperture_packet_eq_kernelEnergy ha (fun j => conj (c j)) w
    simp only [Complex.conj_conj] at hval
    rw [← hval, Complex.add_re]
    have hsumA : XiWeilSquareSummable (aperturePacketA a (fun j => conj (c j)) w) :=
      XiWeilSquareSummable.finsetSum
        (fun j _ => xiWeilSquareSummable_weilApertureA (w j).2 ha) _
    have hsumB : XiWeilSquareSummable (aperturePacketB a (fun j => conj (c j)) w) :=
      XiWeilSquareSummable.finsetSum
        (fun j _ => xiWeilSquareSummable_weilApertureB (w j).2 ha) _
    have hA := xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis hRH _ hsumA
    have hB := xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis hRH _ hsumB
    linarith
  · intro h
    refine riemannHypothesis_iff_isPSDKernel_twoChannel.mpr
      ((isPSDKernel_iff_forall_energy_nonneg twoChannelKernel_conj_symm).mpr fun n c w => ?_)
    refine ge_of_tendsto
      ((Complex.continuous_re.tendsto _).comp (tendsto_kernelEnergy_aperture c w)) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    exact h a ha n c w

end RHTower
