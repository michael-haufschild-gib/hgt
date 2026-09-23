import GaloisForLFunctions.HTGeometry.StripContourShift
import GaloisForLFunctions.HTGeometry.MassDerivativeTransfer
import GaloisForLFunctions.HTGeometry.CauchyKernelFourier

/-!
# Exponential frequency decay of the mass kernel

The kernel `(Z + w²)^{-(n+1)}` is holomorphic on the strip `|Im w| < √Z`, and on that strip the
real part of `Z + w²` is `Z - (Im w)² + (Re w)² > 0`.  Shifting the contour down by `h < √Z` and
paying the factor `e^{-hL}` carried by `e^{-iLw}` gives

`‖∫ (Z + x²)^{-(n+1)} e^{-iLx} dx‖ ≤ e^{-hL}·(Z - h²)^{-n}·π/√(Z - h²)`

for every `L ≥ 0`.  The rate `h` is free below `√Z`, and the bound is uniform in `Z` on any half
line `Z > h² `.  This is the frequency aperture of a rational half-density of mass `√Z`.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The mass kernel at a frequency, as a function of a complex variable. -/
def massKernelPhase (Z L : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  (((Z : ℂ) + w ^ (2 : ℕ)) ^ (n + 1))⁻¹ * Complex.exp (-(L : ℂ) * w * Complex.I)

theorem re_ofReal_add_sq (Z : ℝ) (w : ℂ) :
    ((Z : ℂ) + w ^ (2 : ℕ)).re = Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ) := by
  simp only [Complex.add_re, Complex.ofReal_re, sq, Complex.mul_re]
  ring

theorem le_norm_ofReal_add_sq {Z : ℝ} {w : ℂ} :
    Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ) ≤ ‖(Z : ℂ) + w ^ (2 : ℕ)‖ := by
  have h1 : ((Z : ℂ) + w ^ (2 : ℕ)).re ≤ ‖(Z : ℂ) + w ^ (2 : ℕ)‖ := Complex.re_le_norm _
  rw [re_ofReal_add_sq] at h1
  exact h1

theorem ofReal_add_sq_ne_zero {Z : ℝ} {w : ℂ} (h : w.im ^ (2 : ℕ) < Z) :
    (Z : ℂ) + w ^ (2 : ℕ) ≠ 0 := by
  intro h0
  have hre := congrArg Complex.re h0
  rw [re_ofReal_add_sq] at hre
  simp only [Complex.zero_re] at hre
  nlinarith [sq_nonneg w.re]

theorem differentiableAt_massKernelPhase {Z L : ℝ} (n : ℕ) {w : ℂ} (h : w.im ^ (2 : ℕ) < Z) :
    DifferentiableAt ℂ (massKernelPhase Z L n) w := by
  have hne : ((Z : ℂ) + w ^ (2 : ℕ)) ^ (n + 1) ≠ 0 := pow_ne_zero _ (ofReal_add_sq_ne_zero h)
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (((Z : ℂ) + v ^ (2 : ℕ)) ^ (n + 1))⁻¹) w := by
    refine DifferentiableAt.inv ?_ hne
    exact (((differentiable_id.pow 2).const_add (Z : ℂ)).pow (n + 1)).differentiableAt
  have h2 : DifferentiableAt ℂ (fun v : ℂ => Complex.exp (-(L : ℂ) * v * Complex.I)) w := by
    exact (((differentiable_const (-(L : ℂ))).mul differentiable_id).mul
      (differentiable_const Complex.I)).cexp.differentiableAt
  exact h1.mul h2

theorem norm_massKernelPhase_le {Z L : ℝ} (n : ℕ) {w : ℂ} (h : w.im ^ (2 : ℕ) < Z) :
    ‖massKernelPhase Z L n w‖
      ≤ Real.exp (L * w.im) * ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ := by
  have hpos : (0 : ℝ) < Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ) := by nlinarith [sq_nonneg w.re]
  have hnorm : Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ) ≤ ‖(Z : ℂ) + w ^ (2 : ℕ)‖ := le_norm_ofReal_add_sq
  have hexp : ‖Complex.exp (-(L : ℂ) * w * Complex.I)‖ = Real.exp (L * w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, neg_zero, zero_mul,
      mul_zero, mul_one, sub_zero, zero_sub, add_zero]
    ring
  rw [massKernelPhase, norm_mul, hexp, norm_inv, norm_pow]
  have hstep : (‖(Z : ℂ) + w ^ (2 : ℕ)‖ ^ (n + 1))⁻¹ ≤ ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ := by
    have hle : (Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1) ≤ ‖(Z : ℂ) + w ^ (2 : ℕ)‖ ^ (n + 1) :=
      pow_le_pow_left₀ hpos.le hnorm _
    have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))
      hle
    simpa [one_div] using this
  calc (‖(Z : ℂ) + w ^ (2 : ℕ)‖ ^ (n + 1))⁻¹ * Real.exp (L * w.im)
      ≤ ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ * Real.exp (L * w.im) :=
        mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)
    _ = Real.exp (L * w.im) * ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ := by ring


theorem re_line (x t : ℝ) : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by
  simp

theorem im_line (x t : ℝ) : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by
  simp

theorem continuous_massKernelPhase_line {Z L t : ℝ} (h : t ^ (2 : ℕ) < Z) (n : ℕ) :
    Continuous fun x : ℝ => massKernelPhase Z L n ((x : ℂ) + (t : ℂ) * Complex.I) := by
  simp only [massKernelPhase]
  refine Continuous.mul ?_ (by fun_prop)
  refine Continuous.inv₀ (by fun_prop) fun x => ?_
  refine pow_ne_zero _ (ofReal_add_sq_ne_zero ?_)
  rw [im_line x t]
  exact h

theorem norm_massKernelPhase_line_le {Z L t : ℝ} (h : t ^ (2 : ℕ) < Z) (n : ℕ) (x : ℝ) :
    ‖massKernelPhase Z L n ((x : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp (L * t) * (((Z - t ^ (2 : ℕ)) ^ n)⁻¹ * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹) := by
  have hZt : (0 : ℝ) < Z - t ^ (2 : ℕ) := by linarith
  have hpos : (0 : ℝ) < Z - t ^ (2 : ℕ) + x ^ (2 : ℕ) := by positivity
  have hbase := norm_massKernelPhase_le (Z := Z) (L := L) n
    (w := (x : ℂ) + (t : ℂ) * Complex.I) (by rw [im_line x t]; exact h)
  rw [re_line x t, im_line x t] at hbase
  have hrw : Z + x ^ (2 : ℕ) - t ^ (2 : ℕ) = Z - t ^ (2 : ℕ) + x ^ (2 : ℕ) := by ring
  rw [hrw] at hbase
  have hcmp : (Z - t ^ (2 : ℕ)) ^ n * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ)) ≤ (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (n + 1) := by
    have h1 : (Z - t ^ (2 : ℕ)) ^ n ≤ (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ n :=
      pow_le_pow_left₀ hZt.le (by nlinarith [sq_nonneg x]) n
    calc (Z - t ^ (2 : ℕ)) ^ n * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ))
        ≤ (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ n * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (n + 1) := by ring
  have hinv : ((Z - t ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (n + 1))⁻¹ ≤ ((Z - t ^ (2 : ℕ)) ^ n)⁻¹ * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ := by
    have := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (Z - t ^ (2 : ℕ)) ^ n * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ))) hcmp
    rw [← mul_inv]
    simpa [one_div] using this
  exact hbase.trans (mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg _))

theorem integrable_massKernelPhase_line {Z L t : ℝ} (h : t ^ (2 : ℕ) < Z) (n : ℕ) :
    Integrable fun x : ℝ => massKernelPhase Z L n ((x : ℂ) + (t : ℂ) * Complex.I) := by
  have hZt : (0 : ℝ) < Z - t ^ (2 : ℕ) := by linarith
  have hA : (0 : ℝ) < Real.sqrt (Z - t ^ (2 : ℕ)) := Real.sqrt_pos.mpr hZt
  have hAsq : Real.sqrt (Z - t ^ (2 : ℕ)) ^ (2 : ℕ) = Z - t ^ (2 : ℕ) := Real.sq_sqrt hZt.le
  have hmaj : Integrable fun x : ℝ =>
      Real.exp (L * t) * ((Z - t ^ (2 : ℕ)) ^ n)⁻¹ * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ := by
    have hb := (integrable_inv_sq_add_sq hA).const_mul
      (Real.exp (L * t) * ((Z - t ^ (2 : ℕ)) ^ n)⁻¹)
    refine hb.congr ?_
    filter_upwards with x
    rw [hAsq]
  refine hmaj.mono' (continuous_massKernelPhase_line h n).aestronglyMeasurable ?_
  filter_upwards with x
  have hle := norm_massKernelPhase_line_le (Z := Z) (L := L) (t := t) h n x
  calc ‖massKernelPhase Z L n ((x : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp (L * t) * (((Z - t ^ (2 : ℕ)) ^ n)⁻¹ * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹) := hle
    _ = Real.exp (L * t) * ((Z - t ^ (2 : ℕ)) ^ n)⁻¹ * (Z - t ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ := by ring


theorem norm_massKernelPhase_strip_le {Z L h : ℝ} (hhZ : h ^ (2 : ℕ) < Z) (hL : 0 ≤ L) (n : ℕ)
    {w : ℂ} (hlo : -h ≤ w.im) (hhi : w.im ≤ 0) :
    ‖massKernelPhase Z L n w‖ ≤ ((Z - h ^ (2 : ℕ) + w.re ^ (2 : ℕ)) ^ (n + 1))⁻¹ := by
  have hsq : w.im ^ (2 : ℕ) ≤ h ^ (2 : ℕ) := by nlinarith
  have him : w.im ^ (2 : ℕ) < Z := lt_of_le_of_lt hsq hhZ
  have hbase := norm_massKernelPhase_le (Z := Z) (L := L) n him
  have hexp : Real.exp (L * w.im) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    exact mul_nonpos_of_nonneg_of_nonpos hL hhi
  have hpos : (0 : ℝ) < Z - h ^ (2 : ℕ) + w.re ^ (2 : ℕ) := by nlinarith [sq_nonneg w.re]
  have hcmp : (Z - h ^ (2 : ℕ) + w.re ^ (2 : ℕ)) ^ (n + 1) ≤ (Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1) :=
    pow_le_pow_left₀ hpos.le (by linarith) _
  have hinv : ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ ≤ ((Z - h ^ (2 : ℕ) + w.re ^ (2 : ℕ)) ^ (n + 1))⁻¹ := by
    have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (Z - h ^ (2 : ℕ) + w.re ^ (2 : ℕ)) ^ (n + 1))
      hcmp
    simpa [one_div] using this
  have hnn : (0 : ℝ) ≤ ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ := by
    have : (0 : ℝ) < Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ) := by nlinarith [sq_nonneg w.re]
    positivity
  calc ‖massKernelPhase Z L n w‖
      ≤ Real.exp (L * w.im) * ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ := hbase
    _ ≤ 1 * ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ :=
        mul_le_mul_of_nonneg_right hexp hnn
    _ = ((Z + w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ)) ^ (n + 1))⁻¹ := one_mul _
    _ ≤ ((Z - h ^ (2 : ℕ) + w.re ^ (2 : ℕ)) ^ (n + 1))⁻¹ := hinv

theorem tendsto_vertical_massKernelPhase {Z L h : ℝ} (hh : 0 < h) (hhZ : h ^ (2 : ℕ) < Z) (hL : 0 ≤ L)
    (n : ℕ) :
    Filter.Tendsto (fun R : ℝ =>
        ‖∫ y in (0 : ℝ)..(-h), massKernelPhase Z L n ((R : ℂ) + (y : ℂ) * Complex.I)‖
        + ‖∫ y in (0 : ℝ)..(-h), massKernelPhase Z L n (-(R : ℂ) + (y : ℂ) * Complex.I)‖)
      Filter.atTop (nhds 0) := by
  have hmem : ∀ y : ℝ, y ∈ Set.uIoc (0 : ℝ) (-h) → -h ≤ y ∧ y ≤ 0 := by
    intro y hy
    rw [Set.uIoc_of_ge (by linarith)] at hy
    exact ⟨le_of_lt hy.1, hy.2⟩
  have hlim : Filter.Tendsto (fun R : ℝ => 2 * h * ((Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) ^ (n + 1))⁻¹)
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun R : ℝ => Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) Filter.atTop Filter.atTop := by
      have hp : Filter.Tendsto (fun R : ℝ => R ^ (2 : ℕ)) Filter.atTop Filter.atTop :=
        Filter.tendsto_pow_atTop (by norm_num)
      exact Filter.tendsto_atTop_add_const_left _ _ hp
    have hpow : Filter.Tendsto (fun R : ℝ => (Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) ^ (n + 1))
        Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono' _ ?_ hbase
      filter_upwards [hbase.eventually_ge_atTop 1] with R hR
      have hstep : (Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) ^ (1 : ℕ) ≤ (Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) ^ (n + 1) :=
        pow_le_pow_right₀ hR (Nat.le_add_left 1 n)
      simpa using hstep
    have := (tendsto_inv_atTop_zero.comp hpow).const_mul (2 * h)
    simpa using this
  refine squeeze_zero (fun R => by positivity) (fun R => ?_) hlim
  have hb1 : ‖∫ y in (0 : ℝ)..(-h), massKernelPhase Z L n ((R : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ ((Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) ^ (n + 1))⁻¹ * |(-h) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    obtain ⟨h1, h2⟩ := hmem y hy
    have := norm_massKernelPhase_strip_le (Z := Z) (L := L) (h := h) hhZ hL n
      (w := (R : ℂ) + (y : ℂ) * Complex.I) (by rw [im_line R y]; exact h1)
      (by rw [im_line R y]; exact h2)
    rwa [re_line R y] at this
  have hb2 : ‖∫ y in (0 : ℝ)..(-h), massKernelPhase Z L n (-(R : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ ((Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) ^ (n + 1))⁻¹ * |(-h) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    obtain ⟨h1, h2⟩ := hmem y hy
    have hrw : -(R : ℂ) + (y : ℂ) * Complex.I = ((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hrw]
    have := norm_massKernelPhase_strip_le (Z := Z) (L := L) (h := h) hhZ hL n
      (w := ((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I) (by rw [im_line (-R) y]; exact h1)
      (by rw [im_line (-R) y]; exact h2)
    rw [re_line (-R) y] at this
    calc ‖massKernelPhase Z L n (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ ((Z - h ^ (2 : ℕ) + (-R) ^ (2 : ℕ)) ^ (n + 1))⁻¹ := this
      _ = ((Z - h ^ (2 : ℕ) + R ^ (2 : ℕ)) ^ (n + 1))⁻¹ := by rw [neg_pow]; norm_num
  have habs : |(-h) - 0| = h := by
    rw [sub_zero, abs_neg, abs_of_pos hh]
  rw [habs] at hb1 hb2
  linarith [hb1, hb2]


theorem integral_massKernelPhase_shift {Z L h : ℝ} (hh : 0 < h) (hhZ : h ^ (2 : ℕ) < Z) (hL : 0 ≤ L)
    (n : ℕ) :
    (∫ x : ℝ, massKernelPhase Z L n ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))
      = ∫ x : ℝ, massKernelPhase Z L n ((x : ℂ) + ((-h : ℝ) : ℂ) * Complex.I) := by
  have hZ : (0 : ℝ) < Z := lt_of_le_of_lt (sq_nonneg h) hhZ
  have hnegsq : (-h) ^ (2 : ℕ) < Z := by
    rw [neg_pow]
    simpa using hhZ
  refine integral_line_shift (a := (0 : ℝ)) (b := -h) ?_
    (integrable_massKernelPhase_line (t := 0) (by simpa using hZ) n)
    (integrable_massKernelPhase_line (t := -h) hnegsq n)
    (tendsto_vertical_massKernelPhase hh hhZ hL n)
  intro z hz
  refine differentiableAt_massKernelPhase n ?_
  rw [Set.mem_uIcc] at hz
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · nlinarith
  · nlinarith

/-- **Exponential frequency decay of the mass kernel.**  Shifting the contour down by `h < √Z`
converts the oscillation into a decay of rate `h`. -/
theorem norm_integral_massKernelPhase_le {Z L h : ℝ} (hh : 0 < h) (hhZ : h ^ (2 : ℕ) < Z) (hL : 0 ≤ L)
    (n : ℕ) :
    ‖∫ x : ℝ, massKernelPhase Z L n (x : ℂ)‖
      ≤ Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹ * (Real.pi / Real.sqrt (Z - h ^ (2 : ℕ))) := by
  have hZh : (0 : ℝ) < Z - h ^ (2 : ℕ) := by linarith
  have hA : (0 : ℝ) < Real.sqrt (Z - h ^ (2 : ℕ)) := Real.sqrt_pos.mpr hZh
  have hAsq : Real.sqrt (Z - h ^ (2 : ℕ)) ^ (2 : ℕ) = Z - h ^ (2 : ℕ) := Real.sq_sqrt hZh.le
  have hnegsq : (-h) ^ (2 : ℕ) < Z := by
    rw [neg_pow]
    simpa using hhZ
  have hzero : (∫ x : ℝ, massKernelPhase Z L n (x : ℂ))
      = ∫ x : ℝ, massKernelPhase Z L n ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    norm_num
  rw [hzero, integral_massKernelPhase_shift hh hhZ hL n]
  have hint := integrable_massKernelPhase_line (Z := Z) (L := L) (t := -h) hnegsq n
  have hmaj : Integrable fun x : ℝ =>
      Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹ * (Z - h ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ := by
    have hb := (integrable_inv_sq_add_sq hA).const_mul
      (Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹)
    refine hb.congr ?_
    filter_upwards with x
    rw [hAsq]
  have hstep : ‖∫ x : ℝ, massKernelPhase Z L n ((x : ℂ) + ((-h : ℝ) : ℂ) * Complex.I)‖
      ≤ ∫ x : ℝ, Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹ * (Z - h ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono hint.norm hmaj fun x => ?_
    have hle := norm_massKernelPhase_line_le (Z := Z) (L := L) (t := -h) hnegsq n x
    have hsq : (Z - (-h) ^ (2 : ℕ)) = Z - h ^ (2 : ℕ) := by
      rw [neg_pow]
      norm_num
    rw [hsq] at hle
    have hexp : L * (-h) = -(L * h) := by ring
    rw [hexp] at hle
    calc ‖massKernelPhase Z L n ((x : ℂ) + ((-h : ℝ) : ℂ) * Complex.I)‖
        ≤ Real.exp (-(L * h)) * (((Z - h ^ (2 : ℕ)) ^ n)⁻¹ * (Z - h ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹) := hle
      _ = Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹ * (Z - h ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ := by ring
  refine le_trans hstep (le_of_eq ?_)
  have hval : (∫ x : ℝ, Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹ * (Z - h ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹)
      = Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹
        * ∫ x : ℝ, (Real.sqrt (Z - h ^ (2 : ℕ)) ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hAsq]
  rw [hval, integral_inv_sq_add_sq hA]


/-! ## The Fourier phase as a mass weight -/

/-- The Fourier phase at frequency `L`. -/
def cauchyFourierWeight (L : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I)

theorem continuous_cauchyFourierWeight (L : ℝ) : Continuous (cauchyFourierWeight L) := by
  unfold cauchyFourierWeight
  fun_prop

theorem norm_cauchyFourierWeight (L x : ℝ) : ‖cauchyFourierWeight L x‖ = 1 := by
  rw [cauchyFourierWeight, Complex.norm_exp]
  simp

theorem cauchyFourierWeight_bound (L x : ℝ) :
    ‖cauchyFourierWeight L x‖ ≤ 1 + Real.log (2 + |x|) := by
  rw [norm_cauchyFourierWeight]
  have hlog : 0 ≤ Real.log (2 + |x|) := Real.log_nonneg (by
    have := abs_nonneg x
    linarith)
  linarith

theorem massPairing_cauchyFourierWeight_eq (Z L : ℝ) (n : ℕ) :
    massPairing (cauchyFourierWeight L) n Z = ∫ x : ℝ, massKernelPhase Z L n (x : ℂ) := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [cauchyFourierWeight, massKernelPhase]
  have hbase : ((Z : ℂ) + (x : ℂ) ^ (2 : ℕ)) = (((Z + x ^ (2 : ℕ) : ℝ)) : ℂ) := by
    push_cast
    ring
  have hexp : Complex.exp (-(L : ℂ) * (x : ℂ) * Complex.I)
      = Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hbase, hexp, ← Complex.ofReal_pow]
  ring

/-- **The exponential frequency aperture of the mass kernel.** -/
theorem norm_massPairing_cauchyFourierWeight_le {Z L h : ℝ} (hh : 0 < h) (hhZ : h ^ (2 : ℕ) < Z)
    (hL : 0 ≤ L) (n : ℕ) :
    ‖massPairing (cauchyFourierWeight L) n Z‖
      ≤ Real.exp (-(L * h)) * ((Z - h ^ (2 : ℕ)) ^ n)⁻¹ * (Real.pi / Real.sqrt (Z - h ^ (2 : ℕ))) := by
  rw [massPairing_cauchyFourierWeight_eq]
  exact norm_integral_massKernelPhase_le hh hhZ hL n

/-- The mass pairing of the Fourier phase at order zero: the Poisson kernel's Fourier transform. -/
theorem massPairing_cauchyFourierWeight_zero {Z : ℝ} (hZ : 0 < Z) (L : ℝ) :
    massPairing (cauchyFourierWeight L) 0 Z
      = ((Real.pi / Real.sqrt Z * Real.exp (-(Real.sqrt Z * |L|)) : ℝ) : ℂ) := by
  have hA : (0 : ℝ) < Real.sqrt Z := Real.sqrt_pos.mpr hZ
  have hAsq : Real.sqrt Z ^ (2 : ℕ) = Z := Real.sq_sqrt hZ.le
  have hbase := integral_inv_sq_add_sq_mul_cexp_neg hA L
  rw [hAsq] at hbase
  rw [← hbase]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [cauchyFourierWeight]
  rw [pow_one]
  ring

end GaloisForLFunctions.HTGeometry

end
