import GaloisForLFunctions.GaloisTheoryOfZeros.TheLineThroughTheSaddleIsAGaussianAtTheSaddleValue

/-!
# The heat family at a saddle time is a constant plus a cosine

Let the saddle `a = σ + iη` lie in the wide region `σ ≥ 50`, `η ≥ 0`, `π/4 − η ≥ 1/(4σ)`
(`WideRegion`). The time `τ(a) = πe^{2a}/a` is a forward time; it is real for the real saddles
`η = 0`, and close to the imaginary direction on the saddle region `π/4 − η ≤ 1/σ`
(`SaddleRegion`), where `Re τ ≍ e^{2σ}/σ²` against `|τ| ≍ e^{2σ}/σ`. At this time the heat family
has two stationary contributions,

`H_{τ(a)}(ζ/a) = B₀(a) + 2S₀(a) cos ζ + O(σ⁵e^{−σ})(|B₀(a)| + |S₀(a)|)`, `|ζ| ≤ R ≤ σ`:

* the bulk term `B₀(a) = iΦ(0)(π/τ)^{1/2}` from the stationary point `x = 0` of `e^{τx²}`;
* the saddle term `S₀(a)e^{±iζ}`, `S₀(a) = 4π²e^{9a/2 + f(a)}(π/(2P − τ))^{1/2}`, from the saddles
  `±a` of `τx² − πe^{2x}`.

The two terms are of comparable size on the saddle region; towards the real saddles the saddle
term dominates. The zeros of the model `B₀ + 2S₀ cos ζ` collide at `ζ ∈ πℤ` when `2S₀ = ±B₀`.

* `WideRegion.*`: the sizes of `P`, `τ` and of the kernel constants on the region.
* `exists_norm_complexHeat_sub_wide_model_le`: the model with the error `Cσ⁵e^{−σ}`.
* `exists_forall_norm_complexHeat_sub_wide_model_le`: for every window `R` and `ε > 0` the model
  holds with the relative error `ε` for `σ` large.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real Interval

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-- The bulk term `B₀(a) = iΦ(0)(π/τ(a))^{1/2}`. -/
def bulkTerm (a : ℂ) : ℂ := I * kernelC 0 * ((π : ℂ) / saddleTime a) ^ (1 / 2 : ℂ)

/-- The wide region of the saddles: `Re a ≥ 50`, `Im a ≥ 0` and `π/4 − Im a ≥ 1/(4 Re a)`. It
contains the real saddles. -/
def WideRegion (a : ℂ) : Prop :=
  50 ≤ a.re ∧ 0 ≤ a.im ∧ 1 / (4 * a.re) ≤ π / 4 - a.im

/-- The region of the saddles near the edge of the strip of the kernel: `Re a ≥ 50` and
`1/(4 Re a) ≤ π/4 − Im a ≤ 1/Re a`. -/
def SaddleRegion (a : ℂ) : Prop :=
  50 ≤ a.re ∧ 1 / (4 * a.re) ≤ π / 4 - a.im ∧ π / 4 - a.im ≤ 1 / a.re

theorem SaddleRegion.wide {a : ℂ} (h : SaddleRegion a) : WideRegion a := by
  refine ⟨h.1, ?_, h.2.1⟩
  have h1 : 1 / a.re ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) h.1
  linarith [h.2.2, Real.pi_gt_three]

theorem kernelC_zero_ne_zero : kernelC 0 ≠ 0 := by
  have h := kernelC_ofReal 0
  rw [Complex.ofReal_zero, riemannPhiKernel_eq_ofReal] at h
  rw [h]
  exact_mod_cast (riemannKernelReal_pos 0).ne'

theorem norm_cpow_half (w : ℂ) : ‖((π : ℂ) / w) ^ (1 / 2 : ℂ)‖ = Real.sqrt (π / ‖w‖) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Real.sqrt_eq_rpow]

/-- `(2/3)σ⁴ ≤ e^{2σ}`. -/
theorem two_thirds_pow_le_exp {σ : ℝ} (hσ : 0 ≤ σ) : 2 / 3 * σ ^ 4 ≤ Real.exp (2 * σ) := by
  have h := Real.pow_div_factorial_le_exp (2 * σ) (by linarith) 4
  have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h
  linarith [show (2 * σ) ^ 4 / 24 = 2 / 3 * σ ^ 4 by ring]

theorem saddlePhaseValue_re (a : ℂ) : (saddlePhaseValue a).re =
    π * Real.exp (2 * a.re) *
      (Real.cos (2 * a.im) * (a.re - 1) - Real.sin (2 * a.im) * a.im) := by
  rw [saddlePhaseValue, Complex.mul_re, saddleP_re, saddleP_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  ring

/-- A crude bound of the segment `[0, iη]`: `|bulkHalf| ≤ e K(η)` for `Re τ ≥ 0`, `|z| ≤ 1`. -/
theorem norm_bulkHalf_le {τ z : ℂ} {η : ℝ} (hτ : 0 ≤ τ.re) (hη0 : 0 ≤ η) (hη : η < π / 4)
    (hz : ‖z‖ ≤ 1) : ‖bulkHalf τ η z‖ ≤ stripConst η * Real.exp 1 := by
  have hK := stripConst_nonneg hη0 hη
  have hη1 : η ≤ 1 := by linarith [Real.pi_lt_d2]
  have hbound : ∀ v ∈ Ι (0 : ℝ) η,
      ‖kernelC (v * I) * cexp (-(τ * (v : ℂ) ^ 2) - z * v)‖ ≤ stripConst η * Real.exp 1 := by
    intro v hv
    rw [uIoc_of_le hη0] at hv
    have hk := norm_kernelC_le_stripConst (x := (v : ℂ) * I) hη
      (by simpa [abs_of_pos hv.1] using hv.2) (by simp)
    have hk' : ‖kernelC ((v : ℂ) * I)‖ ≤ stripConst η := by
      have h0 : ((v : ℂ) * I).re = 0 := by simp
      rw [h0, zero_div, Real.exp_zero, mul_one] at hk
      exact hk
    have hexp : ‖cexp (-(τ * (v : ℂ) ^ 2) - z * v)‖ ≤ Real.exp 1 := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have h1 : (-(τ * (v : ℂ) ^ 2) - z * v).re = -(τ.re * v ^ 2) - z.re * v := by
        have e : -(τ * (v : ℂ) ^ 2) - z * v = -(τ * ((v ^ 2 : ℝ) : ℂ)) - z * ((v : ℝ) : ℂ) := by
          push_cast
          ring
        rw [e, Complex.sub_re, Complex.neg_re, Complex.re_mul_ofReal, Complex.re_mul_ofReal]
      have h2 : -z.re ≤ 1 := (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
      rw [h1]
      linarith [mul_nonneg hτ (sq_nonneg v), hv.2, mul_le_mul_of_nonneg_right h2 hv.1.le]
    rw [norm_mul]
    exact mul_le_mul hk' hexp (norm_nonneg _) hK
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [bulkHalf, norm_mul, Complex.norm_I, one_mul]
  refine h.trans ?_
  rw [sub_zero, abs_of_nonneg hη0]
  exact mul_le_of_le_one_right (by positivity) hη1

/-! ## The regions of the saddles -/

namespace SaddleRegion

theorem cos_eq (a : ℂ) : Real.cos (2 * a.im) = Real.sin (2 * (π / 4 - a.im)) := by
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  ring

theorem time_re_eq (a : ℂ) : (saddleTime a).re =
    ((saddleP a).re * a.re + (saddleP a).im * a.im) / Complex.normSq a := by
  rw [saddleTime, Complex.div_re, ← add_div]

theorem exp_neg_sq_mul_exp (σ : ℝ) : Real.exp (-σ) ^ 2 * Real.exp (2 * σ) = 1 := by
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  have : -σ + -σ + 2 * σ = 0 := by ring
  rw [this, Real.exp_zero]

theorem exp_neg_two_mul_exp (σ : ℝ) : Real.exp (-(2 * σ)) * Real.exp (2 * σ) = 1 := by
  rw [← Real.exp_add]
  simp

end SaddleRegion

open SaddleRegion (time_re_eq exp_neg_sq_mul_exp exp_neg_two_mul_exp)

namespace WideRegion

variable {a : ℂ}

theorem re_pos (h : WideRegion a) : 0 < a.re := by linarith [h.1]

theorem im_lt (h : WideRegion a) : a.im < π / 4 := by
  have hσ := h.re_pos
  have h1 : 0 < 1 / (4 * a.re) := by positivity
  linarith [h.2.2]

theorem im_le_one (h : WideRegion a) : a.im ≤ 1 := by
  have := h.im_lt
  have := Real.pi_lt_d2
  linarith

theorem le_cos (h : WideRegion a) : 1 / (4 * a.re) ≤ Real.cos (2 * a.im) := by
  have hπ := Real.pi_pos
  have hδ0 : 0 ≤ π / 4 - a.im := by linarith [h.im_lt]
  have h1 := Real.mul_le_sin (x := 2 * (π / 4 - a.im)) (by linarith) (by linarith [h.2.1])
  have h2 : π / 4 - a.im ≤ 2 / π * (2 * (π / 4 - a.im)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr Real.pi_le_four)]
  rw [SaddleRegion.cos_eq]
  linarith [h.2.2]

theorem cos_pos (h : WideRegion a) : 0 < Real.cos (2 * a.im) := by
  have hσ := h.re_pos
  exact lt_of_lt_of_le (by positivity) h.le_cos

theorem sin_nonneg (h : WideRegion a) : 0 ≤ Real.sin (2 * a.im) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [h.2.1]) (by linarith [h.im_lt, Real.pi_pos])

theorem P_im_nonneg (h : WideRegion a) : 0 ≤ (saddleP a).im := by
  rw [saddleP_im]
  exact mul_nonneg (mul_pos Real.pi_pos (Real.exp_pos _)).le h.sin_nonneg

/-- `πe^{2σ} ≤ 4σ Re P`. -/
theorem pi_exp_le (h : WideRegion a) :
    π * Real.exp (2 * a.re) ≤ 4 * a.re * (saddleP a).re := by
  have hσ := h.re_pos
  have hE := Real.exp_pos (2 * a.re)
  have hπ := Real.pi_pos
  have h1 := h.le_cos
  rw [div_le_iff₀ (by positivity)] at h1
  rw [saddleP_re]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_pos hπ hE).le]

theorem P_re_ge (h : WideRegion a) : 18 ≤ (saddleP a).re := by
  have hσ := h.re_pos
  have h1 := h.pi_exp_le
  have h2 := two_thirds_pow_le_exp hσ.le
  have hπ := Real.pi_gt_three
  have h3 : (50 : ℝ) ^ 3 ≤ a.re ^ 3 := pow_le_pow_left₀ (by norm_num) h.1 3
  have h5 : 3 * Real.exp (2 * a.re) ≤ π * Real.exp (2 * a.re) :=
    mul_le_mul_of_nonneg_right hπ.le (Real.exp_pos _).le
  have h7 : a.re * (50 : ℝ) ^ 3 ≤ a.re * a.re ^ 3 := mul_le_mul_of_nonneg_left h3 hσ.le
  by_contra hcon
  push Not at hcon
  have h4 : 4 * a.re * (saddleP a).re < 4 * a.re * 18 :=
    mul_lt_mul_of_pos_left hcon (by positivity)
  nlinarith

theorem P_re_pos (h : WideRegion a) : 0 < (saddleP a).re := by linarith [h.P_re_ge]

theorem normSq_bounds (h : WideRegion a) :
    a.re ^ 2 ≤ Complex.normSq a ∧ Complex.normSq a ≤ 2 * a.re ^ 2 := by
  rw [Complex.normSq_apply]
  have h1 := h.2.1
  have h2 := h.im_le_one
  have h3 := h.1
  constructor <;> nlinarith

/-- `Re τ ≥ πe^{2σ}/(8σ²)`: the time is forward. -/
theorem le_time_re (h : WideRegion a) :
    π * Real.exp (2 * a.re) / (8 * a.re ^ 2) ≤ (saddleTime a).re := by
  have hσ := h.re_pos
  have hπ := Real.pi_pos
  have hE := Real.exp_pos (2 * a.re)
  obtain ⟨hN1, hN2⟩ := h.normSq_bounds
  have hN : 0 < Complex.normSq a := lt_of_lt_of_le (by positivity) hN1
  have h1 : π * Real.exp (2 * a.re) / 4 ≤ (saddleP a).re * a.re := by linarith [h.pi_exp_le]
  have h2 : 0 ≤ (saddleP a).im * a.im := mul_nonneg h.P_im_nonneg h.2.1
  have h3 : π * Real.exp (2 * a.re) * Complex.normSq a ≤
      π * Real.exp (2 * a.re) * (2 * a.re ^ 2) :=
    mul_le_mul_of_nonneg_left hN2 (mul_pos hπ hE).le
  have h4 : π * Real.exp (2 * a.re) / 4 * (8 * a.re ^ 2) ≤
      ((saddleP a).re * a.re + (saddleP a).im * a.im) * (8 * a.re ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [time_re_eq, div_le_div_iff₀ (by positivity) hN]
  linarith

theorem time_re_pos (h : WideRegion a) : 0 < (saddleTime a).re := by
  have hσ := h.re_pos
  have hπ := Real.pi_pos
  exact lt_of_lt_of_le (by positivity) h.le_time_re

/-- `8 Re τ ≤ Re P`. -/
theorem time_re_le (h : WideRegion a) : 8 * (saddleTime a).re ≤ (saddleP a).re := by
  have hσ := h.re_pos
  have hπ := Real.pi_pos
  have hE := Real.exp_pos (2 * a.re)
  obtain ⟨hN1, hN2⟩ := h.normSq_bounds
  have hN : 0 < Complex.normSq a := lt_of_lt_of_le (by positivity) hN1
  have hp := h.P_re_pos
  have hQle : (saddleP a).im ≤ π * Real.exp (2 * a.re) := by
    rw [saddleP_im]
    nlinarith [mul_le_mul_of_nonneg_left (Real.sin_le_one (2 * a.im)) (mul_pos hπ hE).le]
  have hQ0 := h.P_im_nonneg
  have h1 := h.pi_exp_le
  have hη := h.im_le_one
  have h2 : (saddleP a).im * a.im ≤ 4 * a.re * (saddleP a).re := by
    calc (saddleP a).im * a.im ≤ (saddleP a).im * 1 := mul_le_mul_of_nonneg_left hη hQ0
      _ ≤ 4 * a.re * (saddleP a).re := by linarith
  have h3 : (saddleP a).re * a.re ^ 2 ≤ (saddleP a).re * Complex.normSq a :=
    mul_le_mul_of_nonneg_left hN1 hp.le
  have h4 : 40 * a.re * (saddleP a).re ≤ a.re * a.re * (saddleP a).re := by
    have : 40 * a.re ≤ a.re * a.re := by nlinarith [h.1]
    exact mul_le_mul_of_nonneg_right this hp.le
  rw [time_re_eq, ← mul_div_assoc, div_le_iff₀ hN]
  nlinarith

theorem ne_zero (h : WideRegion a) : a ≠ 0 := by
  intro h0
  have := h.1
  rw [h0, Complex.zero_re] at this
  linarith

theorem norm_time_le (h : WideRegion a) : ‖saddleTime a‖ ≤ π * Real.exp (2 * a.re) := by
  have hπ := Real.pi_pos
  have h1 : 1 ≤ ‖a‖ := by linarith [(le_abs_self a.re).trans (Complex.abs_re_le_norm a), h.1]
  rw [saddleTime, norm_div, norm_saddleP]
  exact div_le_self (by positivity) h1

/-- Below the height `1/2` the saddle value has nonnegative real part. -/
theorem phase_re_nonneg (h : WideRegion a) (hη : a.im ≤ 1 / 2) :
    0 ≤ (saddlePhaseValue a).re := by
  have hπ := Real.pi_pos
  have hE := Real.exp_pos (2 * a.re)
  have hη0 := h.2.1
  have hc : 1 / 2 ≤ Real.cos (2 * a.im) := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * a.im)
    nlinarith [mul_nonneg hη0 (sub_nonneg.mpr hη)]
  have hs : Real.sin (2 * a.im) * a.im ≤ 1 / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_le_one (2 * a.im))) hη0]
  rw [saddlePhaseValue_re]
  refine mul_nonneg (mul_pos hπ hE).le ?_
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by linarith [h.1] : (0 : ℝ) ≤ a.re - 1), h.1]

/-! ### The constants of the kernel on the region -/

theorem termConst_le (h : WideRegion a) :
    termConst riemannCuspPoly (π * Real.cos (2 * a.im) / 2) ≤
      144 * polyAbsBound riemannCuspPoly * a.re ^ 2 := by
  have hσ := h.re_pos
  have hπ := Real.pi_gt_three
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hc := h.cos_pos
  have hle := h.le_cos
  rw [div_le_iff₀ (by positivity)] at hle
  set a' : ℝ := π * Real.cos (2 * a.im) / 2 with ha'
  have ha0 : 0 < a' := by positivity
  have h1 : 1 ≤ 3 * a.re * a' := by
    rw [ha']
    nlinarith [mul_le_mul_of_nonneg_right hπ.le (mul_nonneg hσ.le hc.le)]
  have ha2 : a' ≤ 2 := by
    have := mul_le_mul Real.pi_le_four (Real.cos_le_one (2 * a.im)) hc.le
      (by norm_num : (0 : ℝ) ≤ 4)
    rw [ha']
    linarith
  have hdef : termConst riemannCuspPoly a' =
      polyAbsBound riemannCuspPoly * (2 / a' ^ 2 * Real.exp a') := by
    rw [termConst, natDegree_riemannCuspPoly]
    norm_num [Nat.factorial]
  have h2 : 2 / a' ^ 2 ≤ 18 * a.re ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_self_le_mul_self zero_le_one h1]
  have h3 : Real.exp a' ≤ 8 := by
    have h4 := Real.exp_one_lt_d9
    have h5 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h6 := Real.exp_le_exp.mpr ha2
    nlinarith [Real.exp_pos 1]
  have h4 : 2 / a' ^ 2 * Real.exp a' ≤ 18 * a.re ^ 2 * 8 :=
    mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
  rw [hdef]
  nlinarith [mul_le_mul_of_nonneg_left h4 hB]

/-- `K(η) ≤ 864 B σ³` on the region. -/
theorem stripConst_le (h : WideRegion a) :
    stripConst a.im ≤ 864 * polyAbsBound riemannCuspPoly * a.re ^ 3 := by
  have hσ := h.re_pos
  have hπ := Real.pi_gt_three
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hc := h.cos_pos
  have hle := h.le_cos
  have hT := h.termConst_le
  rw [div_le_iff₀ (by positivity)] at hle
  rw [stripConst]
  set a' : ℝ := π * Real.cos (2 * a.im) / 2 with ha'
  have ha0 : 0 < a' := by positivity
  have h1 : 1 ≤ 3 * a.re * a' := by
    rw [ha']
    nlinarith [mul_le_mul_of_nonneg_right hπ.le (mul_nonneg hσ.le hc.le)]
  have h6 : 1 / (6 * a.re) ≤ 1 - Real.exp (-a') := by
    rcases le_or_gt a' 1 with ha1 | ha1
    · -- `1 − e^{−a'} ≥ a'/2`
      have h5 : a' / 2 ≤ 1 - Real.exp (-a') := by
        have hm : Real.exp (-a') * Real.exp a' = 1 := by rw [← Real.exp_add]; simp
        have hX := Real.exp_pos (-a')
        have h7 : Real.exp (-a') * (1 + a') ≤ 1 := by
          nlinarith [mul_nonneg hX.le (sub_nonneg.mpr (Real.add_one_le_exp a'))]
        by_contra hcon
        push Not at hcon
        have h8 : 1 - a' / 2 < Real.exp (-a') := by linarith
        nlinarith [mul_lt_mul_of_pos_right h8 (by linarith : 0 < 1 + a'),
          mul_nonneg ha0.le (sub_nonneg.mpr ha1)]
      have h9 : 1 / (6 * a.re) ≤ a' / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · have h7 : Real.exp (-a') ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h8 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      have h9 : 1 / (6 * a.re) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith [h.1]
      linarith
  have h60 : 0 < 1 / (6 * a.re) := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc termConst riemannCuspPoly a' ≤ 144 * polyAbsBound riemannCuspPoly * a.re ^ 2 := hT
    _ = 864 * polyAbsBound riemannCuspPoly * a.re ^ 3 * (1 / (6 * a.re)) := by
        field_simp
        ring
    _ ≤ 864 * polyAbsBound riemannCuspPoly * a.re ^ 3 * (1 - Real.exp (-a')) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)

theorem leadConst_le (h : WideRegion a) :
    leadConst a.im ≤ 146 * polyAbsBound riemannCuspPoly * a.re ^ 2 := by
  have hT := h.termConst_le
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have h1 : (1 : ℝ) ≤ a.re ^ 2 := by nlinarith [h.1]
  rw [leadConst]
  nlinarith [mul_nonneg hB (sub_nonneg.mpr h1)]

/-! ### The sizes of the two terms -/

/-- `|B₀(a)| ≥ |Φ(0)| e^{−σ}`. -/
theorem le_norm_bulkTerm (h : WideRegion a) :
    ‖kernelC 0‖ * Real.exp (-a.re) ≤ ‖bulkTerm a‖ := by
  have hπ := Real.pi_pos
  have hτ0 : 0 < ‖saddleTime a‖ := norm_pos_iff.mpr fun h0 => by
    have := h.time_re_pos
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hsqrt : Real.exp (-a.re) ≤ Real.sqrt (π / ‖saddleTime a‖) := by
    rw [← Real.sqrt_sq (Real.exp_pos (-a.re)).le]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ hτ0]
    calc Real.exp (-a.re) ^ 2 * ‖saddleTime a‖
        ≤ Real.exp (-a.re) ^ 2 * (π * Real.exp (2 * a.re)) :=
          mul_le_mul_of_nonneg_left h.norm_time_le (sq_nonneg _)
      _ = π := by linear_combination π * exp_neg_sq_mul_exp a.re
  rw [bulkTerm, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_cpow_half]
  exact mul_le_mul_of_nonneg_left hsqrt (norm_nonneg _)

/-- `|B₀(a)| ≤ |Φ(0)|`. -/
theorem norm_bulkTerm_le (h : WideRegion a) : ‖bulkTerm a‖ ≤ ‖kernelC 0‖ := by
  have hσ := h.re_pos
  have hπ := Real.pi_pos
  have hE := two_thirds_pow_le_exp hσ.le
  have h2 : 8 * a.re ^ 2 ≤ Real.exp (2 * a.re) := by
    nlinarith [mul_nonneg (sq_nonneg a.re) (by nlinarith [h.1] : (0 : ℝ) ≤ a.re ^ 2 - 12)]
  have h1 : π ≤ (saddleTime a).re := by
    refine le_trans ?_ h.le_time_re
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : π ≤ ‖saddleTime a‖ :=
    h1.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hsqrt : Real.sqrt (π / ‖saddleTime a‖) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one (lt_of_lt_of_le hπ h3)).mpr h3)
  rw [bulkTerm, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_cpow_half]
  exact mul_le_of_le_one_right (norm_nonneg _) hsqrt

/-- `|S₀(a)| ≥ e^{7σ/2 + Re f(a)}`. -/
theorem le_norm_saddleTerm (h : WideRegion a) :
    Real.exp (7 * a.re / 2 + (saddlePhaseValue a).re) ≤ ‖saddleTerm a‖ := by
  have hπ := Real.pi_gt_three
  have hE := Real.exp_pos (2 * a.re)
  have hlamre : 0 < (2 * saddleP a - saddleTime a).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero]
    linarith [h.time_re_le, h.P_re_ge]
  have hlam0 : 0 < ‖2 * saddleP a - saddleTime a‖ := norm_pos_iff.mpr fun h0 => by
    rw [h0, Complex.zero_re] at hlamre
    exact lt_irrefl _ hlamre
  have hlamle : ‖2 * saddleP a - saddleTime a‖ ≤ 3 * (π * Real.exp (2 * a.re)) := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    calc ‖2 * saddleP a - saddleTime a‖ ≤ ‖2 * saddleP a‖ + ‖saddleTime a‖ := norm_sub_le _ _
      _ ≤ 2 * (π * Real.exp (2 * a.re)) + π * Real.exp (2 * a.re) := by
          rw [norm_mul, norm_saddleP, h2]
          linarith [h.norm_time_le]
      _ = 3 * (π * Real.exp (2 * a.re)) := by ring
  have hsqrt : Real.exp (-a.re) / 2 ≤ Real.sqrt (π / ‖2 * saddleP a - saddleTime a‖) := by
    have h0 : (0 : ℝ) ≤ Real.exp (-a.re) / 2 := by positivity
    rw [← Real.sqrt_sq h0]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ hlam0]
    calc (Real.exp (-a.re) / 2) ^ 2 * ‖2 * saddleP a - saddleTime a‖
        ≤ (Real.exp (-a.re) / 2) ^ 2 * (3 * (π * Real.exp (2 * a.re))) :=
          mul_le_mul_of_nonneg_left hlamle (sq_nonneg _)
      _ = 3 / 4 * π * (Real.exp (-a.re) ^ 2 * Real.exp (2 * a.re)) := by ring
      _ ≤ π := by rw [exp_neg_sq_mul_exp]; linarith
  have h1 : ‖(4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [show (4 : ℂ) * (π : ℂ) ^ 2 = ((4 * π ^ 2 : ℝ) : ℂ) by simp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : (9 * a / 2 + saddlePhaseValue a).re = 9 * a.re / 2 + (saddlePhaseValue a).re := by
    have h3 : (9 * a / 2).re = 9 * a.re / 2 := by simp
    rw [Complex.add_re, h3]
  have h4 : Real.exp (7 * a.re / 2 + (saddlePhaseValue a).re) =
      Real.exp (9 * a.re / 2 + (saddlePhaseValue a).re) * Real.exp (-a.re) := by
    rw [← Real.exp_add]
    ring_nf
  have hX := Real.exp_pos (9 * a.re / 2 + (saddlePhaseValue a).re)
  rw [saddleTerm, norm_mul, norm_mul, h1, Complex.norm_exp, h2, norm_cpow_half, h4]
  calc Real.exp (9 * a.re / 2 + (saddlePhaseValue a).re) * Real.exp (-a.re)
      ≤ 4 * π ^ 2 * Real.exp (9 * a.re / 2 + (saddlePhaseValue a).re) * (Real.exp (-a.re) / 2) := by
        have h5 : (0 : ℝ) ≤ 2 * π ^ 2 - 1 := by nlinarith
        nlinarith [mul_nonneg h5 (mul_pos hX (Real.exp_pos (-a.re))).le]
    _ ≤ 4 * π ^ 2 * Real.exp (9 * a.re / 2 + (saddlePhaseValue a).re) *
          Real.sqrt (π / ‖2 * saddleP a - saddleTime a‖) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-! ### The three errors on the region -/

/-- The error of the bulk term: `(1 + K(η))/Re τ ≤ 3(1 + 864B) σ⁵ e^{−2σ}`. -/
theorem bulk_error_le (h : WideRegion a) :
    (1 + stripConst a.im) / (saddleTime a).re ≤
      3 * (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) := by
  have hσ := h.re_pos
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hπ := Real.pi_gt_three
  have hK := h.stripConst_le
  have hτ := h.le_time_re
  have hτ0 := h.time_re_pos
  have h1 : (1 : ℝ) ≤ a.re ^ 3 := one_le_pow₀ (by linarith [h.1])
  have h2 : 1 + stripConst a.im ≤ (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 3 := by
    nlinarith
  have hX : 0 ≤ (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 3 := by positivity
  have h3 : (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 3 ≤
      3 * (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
        (π * Real.exp (2 * a.re) / (8 * a.re ^ 2)) := by
    have e : 3 * (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
        (π * Real.exp (2 * a.re) / (8 * a.re ^ 2)) =
        3 * π / 8 * ((1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 3) *
          (Real.exp (-(2 * a.re)) * Real.exp (2 * a.re)) := by
      field_simp
    rw [e, exp_neg_two_mul_exp, mul_one]
    have h4 : (1 : ℝ) ≤ 3 * π / 8 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h4 hX]
  rw [div_le_iff₀ hτ0]
  calc 1 + stripConst a.im ≤ (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 3 := h2
    _ ≤ 3 * (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
          (π * Real.exp (2 * a.re) / (8 * a.re ^ 2)) := h3
    _ ≤ 3 * (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
          (saddleTime a).re := mul_le_mul_of_nonneg_left hτ (by positivity)

/-- The error to the left of the saddle. -/
theorem leftErr_le (h : WideRegion a) (R : ℝ) :
    leftErr R a ≤ 864 * polyAbsBound riemannCuspPoly * Real.exp R * a.re ^ 4 *
      Real.exp (a.re / 2) * (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
        Real.exp ((saddlePhaseValue a).re)) := by
  have hσ := h.re_pos
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hK := h.stripConst_le
  have h5 : Real.exp ((saddlePhaseValue a).re - (saddleP a).re + (saddleTime a).re) ≤
      Real.exp ((saddlePhaseValue a).re) :=
    Real.exp_le_exp.mpr (by linarith [h.time_re_le, h.P_re_ge])
  rw [leftErr]
  calc a.re * (stripConst a.im * Real.exp (a.re / 2) * Real.exp R *
        (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
          Real.exp ((saddlePhaseValue a).re - (saddleP a).re + (saddleTime a).re)))
      ≤ a.re * (864 * polyAbsBound riemannCuspPoly * a.re ^ 3 * Real.exp (a.re / 2) *
          Real.exp R * (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
            Real.exp ((saddlePhaseValue a).re))) := by
        refine mul_le_mul_of_nonneg_left ?_ hσ.le
        refine mul_le_mul ?_ (add_le_add le_rfl h5) (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = 864 * polyAbsBound riemannCuspPoly * Real.exp R * a.re ^ 4 * Real.exp (a.re / 2) *
          (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
            Real.exp ((saddlePhaseValue a).re)) := by ring

/-- Above the height `1/2` the end at the origin of the line is small. -/
theorem exp_neg_im_sq_le (h : WideRegion a) (hη : 1 / 2 ≤ a.im) :
    Real.exp (-(a.im ^ 2 * (saddleTime a).re)) ≤ Real.exp (-(3 * a.re)) := by
  have hσ := h.re_pos
  have hπ := Real.pi_gt_three
  refine Real.exp_le_exp.mpr ?_
  have hτ := h.le_time_re
  have hE := two_thirds_pow_le_exp hσ.le
  have h2 : a.re ^ 2 / 4 ≤ (saddleTime a).re := by
    refine le_trans ?_ hτ
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hπ.le (Real.exp_pos (2 * a.re)).le]
  have h3 : (1 : ℝ) / 4 ≤ a.im ^ 2 := by nlinarith
  have h4 : 1 / 4 * (a.re ^ 2 / 4) ≤ a.im ^ 2 * (saddleTime a).re :=
    mul_le_mul h3 h2 (by positivity) (sq_nonneg _)
  nlinarith [mul_nonneg hσ.le (by linarith [h.1] : (0 : ℝ) ≤ a.re - 48)]

/-- The error at the saddle. -/
theorem saddleErr_le (h : WideRegion a) :
    saddleErr a ≤ (5120 * π ^ 2 + 584 * polyAbsBound riemannCuspPoly) * Real.exp 4 *
      a.re ^ 2 * Real.exp (5 * a.re / 2) := by
  have hσ := h.re_pos
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hπ := Real.pi_gt_three
  have hp := h.P_re_ge
  have hp0 := h.P_re_pos
  have hE := Real.exp_pos (2 * a.re)
  have h1 := h.pi_exp_le
  have h2 : ‖saddleP a‖ / (saddleP a).re ≤ 4 * a.re := by
    rw [norm_saddleP, div_le_iff₀ hp0]
    linarith
  have h3 : 1 / (saddleP a).re ≤ 4 * a.re * Real.exp (-(2 * a.re)) := by
    rw [div_le_iff₀ hp0]
    have h4 : Real.exp (2 * a.re) ≤ 4 * a.re * (saddleP a).re := by
      nlinarith [mul_le_mul_of_nonneg_right hπ.le hE.le]
    nlinarith [mul_le_mul_of_nonneg_left h4 (Real.exp_pos (-(2 * a.re))).le,
      exp_neg_two_mul_exp a.re]
  have h4 : (1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re ≤
      20 * a.re ^ 2 * Real.exp (-(2 * a.re)) := by
    have e : (1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re =
        (1 + ‖saddleP a‖ / (saddleP a).re) * (1 / (saddleP a).re) := div_eq_mul_one_div _ _
    have h5 : 1 + ‖saddleP a‖ / (saddleP a).re ≤ 5 * a.re := by linarith [h.1]
    rw [e]
    calc (1 + ‖saddleP a‖ / (saddleP a).re) * (1 / (saddleP a).re)
        ≤ 5 * a.re * (4 * a.re * Real.exp (-(2 * a.re))) :=
          mul_le_mul h5 h3 (by positivity) (by positivity)
      _ = 20 * a.re ^ 2 * Real.exp (-(2 * a.re)) := by ring
  have h6 : 1 / Real.sqrt (saddleP a).re ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr hp0)]
    exact Real.one_le_sqrt.mpr (by linarith)
  have hL := h.leadConst_le
  have hL0 := leadConst_nonneg h.2.1 h.im_lt
  have e1 : Real.exp (9 * a.re / 2) * Real.exp (-(2 * a.re)) = Real.exp (5 * a.re / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hA : 4 * π ^ 2 * Real.exp (9 * a.re / 2) *
      (64 * Real.exp 4 * (1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re) ≤
      5120 * π ^ 2 * Real.exp 4 * a.re ^ 2 * Real.exp (5 * a.re / 2) := by
    have e : 64 * Real.exp 4 * (1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re =
        64 * Real.exp 4 * ((1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re) := by ring
    rw [e]
    calc 4 * π ^ 2 * Real.exp (9 * a.re / 2) *
          (64 * Real.exp 4 * ((1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re))
        ≤ 4 * π ^ 2 * Real.exp (9 * a.re / 2) *
            (64 * Real.exp 4 * (20 * a.re ^ 2 * Real.exp (-(2 * a.re)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity))
            (by positivity)
      _ = 5120 * π ^ 2 * Real.exp 4 * a.re ^ 2 *
            (Real.exp (9 * a.re / 2) * Real.exp (-(2 * a.re))) := by ring
      _ = 5120 * π ^ 2 * Real.exp 4 * a.re ^ 2 * Real.exp (5 * a.re / 2) := by rw [e1]
  have hBd : leadConst a.im * Real.exp (5 * a.re / 2) *
      (Real.exp 4 * (4 * (1 / Real.sqrt (saddleP a).re))) ≤
      584 * polyAbsBound riemannCuspPoly * Real.exp 4 * a.re ^ 2 * Real.exp (5 * a.re / 2) := by
    calc leadConst a.im * Real.exp (5 * a.re / 2) *
          (Real.exp 4 * (4 * (1 / Real.sqrt (saddleP a).re)))
        ≤ 146 * polyAbsBound riemannCuspPoly * a.re ^ 2 * Real.exp (5 * a.re / 2) *
            (Real.exp 4 * (4 * 1)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le) ?_
            (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 (by norm_num))
            (Real.exp_pos _).le
      _ = 584 * polyAbsBound riemannCuspPoly * Real.exp 4 * a.re ^ 2 *
            Real.exp (5 * a.re / 2) := by ring
  rw [saddleErr]
  linarith

theorem saddleErr_nonneg (h : WideRegion a) : 0 ≤ saddleErr a := by
  have hp0 := h.P_re_pos
  have hL0 := leadConst_nonneg h.2.1 h.im_lt
  rw [saddleErr]
  positivity

end WideRegion

/-! ### The scale of the errors -/

/-- The scale of the errors of the two-term model: `σ⁵e^{−σ}(e^{−σ} + e^{7σ/2 + Re f(a)})`, the
weight `σ⁵e^{−σ}` times the lower bounds of the two terms. -/
def modelScale (a : ℂ) : ℝ :=
  a.re ^ 5 * Real.exp (-a.re) *
    (Real.exp (-a.re) + Real.exp (7 * a.re / 2 + (saddlePhaseValue a).re))

namespace WideRegion

variable {a : ℂ}

theorem modelScale_nonneg (h : WideRegion a) : 0 ≤ modelScale a := by
  have hσ := h.re_pos
  rw [modelScale]
  positivity

/-- A quantity of the size of the bulk term, `σⁿe^{c}` with `n ≤ 5`, `c ≤ −2σ`. -/
theorem le_modelScale_of_bulk (h : WideRegion a) {n : ℕ} (hn : n ≤ 5) {c : ℝ}
    (hc : c ≤ -(2 * a.re)) : a.re ^ n * Real.exp c ≤ modelScale a := by
  have hσ := h.re_pos
  have h1σ : (1 : ℝ) ≤ a.re := by linarith [h.1]
  have hp : a.re ^ n ≤ a.re ^ 5 := pow_le_pow_right₀ h1σ hn
  have he : Real.exp c ≤ Real.exp (-a.re) * Real.exp (-a.re) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h0 : 0 ≤ a.re ^ 5 * Real.exp (-a.re) *
      Real.exp (7 * a.re / 2 + (saddlePhaseValue a).re) := by positivity
  calc a.re ^ n * Real.exp c ≤ a.re ^ 5 * (Real.exp (-a.re) * Real.exp (-a.re)) :=
        mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ ≤ modelScale a := by
        rw [modelScale]
        linarith

/-- A quantity of the size of the saddle term, `σⁿe^{c}` with `n ≤ 5`, `c ≤ 5σ/2 + Re f`. -/
theorem le_modelScale_of_saddle (h : WideRegion a) {n : ℕ} (hn : n ≤ 5) {c : ℝ}
    (hc : c ≤ 5 * a.re / 2 + (saddlePhaseValue a).re) : a.re ^ n * Real.exp c ≤ modelScale a := by
  have hσ := h.re_pos
  have h1σ : (1 : ℝ) ≤ a.re := by linarith [h.1]
  have hp : a.re ^ n ≤ a.re ^ 5 := pow_le_pow_right₀ h1σ hn
  have he : Real.exp c ≤
      Real.exp (-a.re) * Real.exp (7 * a.re / 2 + (saddlePhaseValue a).re) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h0 : 0 ≤ a.re ^ 5 * Real.exp (-a.re) * Real.exp (-a.re) := by positivity
  calc a.re ^ n * Real.exp c
      ≤ a.re ^ 5 * (Real.exp (-a.re) * Real.exp (7 * a.re / 2 + (saddlePhaseValue a).re)) :=
        mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ ≤ modelScale a := by
        rw [modelScale]
        linarith

/-- The scale against the two terms. -/
theorem modelScale_le (h : WideRegion a) :
    modelScale a ≤ (1 + 1 / ‖kernelC 0‖) * (a.re ^ 5 * Real.exp (-a.re)) *
      (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
  have hσ := h.re_pos
  have hΦ : 0 < ‖kernelC 0‖ := norm_pos_iff.mpr kernelC_zero_ne_zero
  have hW : 0 ≤ a.re ^ 5 * Real.exp (-a.re) := by positivity
  have hb : Real.exp (-a.re) ≤ ‖bulkTerm a‖ / ‖kernelC 0‖ := by
    rw [le_div_iff₀ hΦ]
    linarith [h.le_norm_bulkTerm]
  have hs := h.le_norm_saddleTerm
  have h9 : ‖bulkTerm a‖ / ‖kernelC 0‖ + ‖saddleTerm a‖ ≤
      (1 + 1 / ‖kernelC 0‖) * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
    have e : (1 + 1 / ‖kernelC 0‖) * (‖bulkTerm a‖ + ‖saddleTerm a‖) =
        ‖bulkTerm a‖ + ‖saddleTerm a‖ + ‖bulkTerm a‖ / ‖kernelC 0‖ +
          ‖saddleTerm a‖ / ‖kernelC 0‖ := by ring
    have := div_nonneg (norm_nonneg (saddleTerm a)) hΦ.le
    have := norm_nonneg (bulkTerm a)
    linarith
  calc modelScale a
      ≤ a.re ^ 5 * Real.exp (-a.re) * (‖bulkTerm a‖ / ‖kernelC 0‖ + ‖saddleTerm a‖) := by
        rw [modelScale]
        exact mul_le_mul_of_nonneg_left (add_le_add hb hs) hW
    _ ≤ a.re ^ 5 * Real.exp (-a.re) *
          ((1 + 1 / ‖kernelC 0‖) * (‖bulkTerm a‖ + ‖saddleTerm a‖)) :=
        mul_le_mul_of_nonneg_left h9 hW
    _ = (1 + 1 / ‖kernelC 0‖) * (a.re ^ 5 * Real.exp (-a.re)) *
          (‖bulkTerm a‖ + ‖saddleTerm a‖) := by ring

/-- The error to the left of the saddle against the scale. For `Im a ≥ 1/2` the end at the origin
is of the size of the bulk term; below, the saddle value has nonnegative real part and the end at
the origin is of the size of the saddle term. -/
theorem leftErr_le_scale (h : WideRegion a) (R : ℝ) :
    leftErr R a ≤ 1728 * polyAbsBound riemannCuspPoly * Real.exp R * modelScale a := by
  have hσ := h.re_pos
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have h1 := h.leftErr_le R
  have h2 : a.re ^ 4 * Real.exp (a.re / 2 + (saddlePhaseValue a).re) ≤ modelScale a :=
    h.le_modelScale_of_saddle (by norm_num) (by linarith)
  have h3 : a.re ^ 4 * (Real.exp (a.re / 2) * Real.exp (-(a.im ^ 2 * (saddleTime a).re))) ≤
      modelScale a := by
    rcases le_or_gt (1 / 2) a.im with hη | hη
    · have h4 := h.exp_neg_im_sq_le hη
      have h5 : a.re ^ 4 * Real.exp (a.re / 2 + -(3 * a.re)) ≤ modelScale a :=
        h.le_modelScale_of_bulk (by norm_num) (by linarith)
      rw [Real.exp_add] at h5
      refine le_trans ?_ h5
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le)
        (by positivity)
    · have hf := h.phase_re_nonneg hη.le
      have h4 : Real.exp (-(a.im ^ 2 * (saddleTime a).re)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) h.time_re_pos.le))
      have h5 : a.re ^ 4 * Real.exp (a.re / 2) ≤ modelScale a :=
        h.le_modelScale_of_saddle (by norm_num) (by linarith)
      refine le_trans ?_ h5
      have h6 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos (a.re / 2)).le
      rw [mul_one] at h6
      exact mul_le_mul_of_nonneg_left h6 (by positivity)
  rw [Real.exp_add] at h2
  have h7 : 0 ≤ 864 * polyAbsBound riemannCuspPoly * Real.exp R := by positivity
  calc leftErr R a ≤ 864 * polyAbsBound riemannCuspPoly * Real.exp R * a.re ^ 4 *
        Real.exp (a.re / 2) * (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
          Real.exp ((saddlePhaseValue a).re)) := h1
    _ = 864 * polyAbsBound riemannCuspPoly * Real.exp R *
        (a.re ^ 4 * (Real.exp (a.re / 2) * Real.exp (-(a.im ^ 2 * (saddleTime a).re))) +
          a.re ^ 4 * (Real.exp (a.re / 2) * Real.exp ((saddlePhaseValue a).re))) := by ring
    _ ≤ 864 * polyAbsBound riemannCuspPoly * Real.exp R * (modelScale a + modelScale a) :=
        mul_le_mul_of_nonneg_left (add_le_add h3 h2) h7
    _ = 1728 * polyAbsBound riemannCuspPoly * Real.exp R * modelScale a := by ring

/-- The error at the saddle against the scale. -/
theorem exp_mul_saddleErr_le_scale (h : WideRegion a) :
    Real.exp ((saddlePhaseValue a).re) * saddleErr a ≤
      (5120 * π ^ 2 + 584 * polyAbsBound riemannCuspPoly) * Real.exp 4 * modelScale a := by
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have h1 := h.saddleErr_le
  have h2 : a.re ^ 2 * Real.exp ((saddlePhaseValue a).re + 5 * a.re / 2) ≤ modelScale a :=
    h.le_modelScale_of_saddle (by norm_num) (by linarith)
  rw [Real.exp_add] at h2
  calc Real.exp ((saddlePhaseValue a).re) * saddleErr a
      ≤ Real.exp ((saddlePhaseValue a).re) *
          ((5120 * π ^ 2 + 584 * polyAbsBound riemannCuspPoly) * Real.exp 4 * a.re ^ 2 *
            Real.exp (5 * a.re / 2)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (5120 * π ^ 2 + 584 * polyAbsBound riemannCuspPoly) * Real.exp 4 *
          (a.re ^ 2 * (Real.exp ((saddlePhaseValue a).re) * Real.exp (5 * a.re / 2))) := by ring
    _ ≤ (5120 * π ^ 2 + 584 * polyAbsBound riemannCuspPoly) * Real.exp 4 * modelScale a :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end WideRegion

/-- **The bulk term on the wide region.** For `|z| ≤ 1` the segment `[0, iη]` is half the bulk
term up to the scale: for `η ≥ 1/2` by the Gaussian at the centre value, and for `η < 1/2` because
the segment and the bulk term are bounded while the saddle term is at least `e^{7σ/2}`. -/
theorem exists_norm_bulkHalf_sub_le_scale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, WideRegion a → ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖bulkHalf (saddleTime a) a.im z - bulkTerm a / 2‖ ≤ C * modelScale a := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_norm_bulkHalf_sub_le
  have hB := polyAbsBound_nonneg riemannCuspPoly
  refine ⟨3 * Cb * (1 + 864 * polyAbsBound riemannCuspPoly) +
    864 * polyAbsBound riemannCuspPoly * Real.exp 1 + ‖kernelC 0‖, by positivity,
    fun a h z hz => ?_⟩
  have hσ := h.re_pos
  have hτ0 := h.time_re_pos
  have hmS := h.modelScale_nonneg
  rcases le_or_gt (1 / 2) a.im with hη2 | hη2
  · have ebulk : bulkTerm a / 2 =
        I * kernelC 0 / 2 * ((π : ℂ) / saddleTime a) ^ (1 / 2 : ℂ) := by
      rw [bulkTerm]
      ring
    have h1 := hCb (saddleTime a) z a.im hτ0 hη2 h.im_lt hz
    rw [← ebulk] at h1
    have h2 := h.bulk_error_le
    have h3 : a.re ^ 5 * Real.exp (-(2 * a.re)) ≤ modelScale a :=
      h.le_modelScale_of_bulk le_rfl le_rfl
    have h4 : 0 ≤ (864 * polyAbsBound riemannCuspPoly * Real.exp 1 + ‖kernelC 0‖) *
        modelScale a := by positivity
    calc ‖bulkHalf (saddleTime a) a.im z - bulkTerm a / 2‖
        ≤ Cb * (1 + stripConst a.im) / (saddleTime a).re := h1
      _ = Cb * ((1 + stripConst a.im) / (saddleTime a).re) := by ring
      _ ≤ Cb * (3 * (1 + 864 * polyAbsBound riemannCuspPoly) * a.re ^ 5 *
            Real.exp (-(2 * a.re))) := mul_le_mul_of_nonneg_left h2 hCb0
      _ = 3 * Cb * (1 + 864 * polyAbsBound riemannCuspPoly) *
            (a.re ^ 5 * Real.exp (-(2 * a.re))) := by ring
      _ ≤ 3 * Cb * (1 + 864 * polyAbsBound riemannCuspPoly) * modelScale a :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (3 * Cb * (1 + 864 * polyAbsBound riemannCuspPoly) +
            864 * polyAbsBound riemannCuspPoly * Real.exp 1 + ‖kernelC 0‖) * modelScale a := by
          linarith
  · have hf := h.phase_re_nonneg hη2.le
    have h1 := norm_bulkHalf_le (z := z) hτ0.le h.2.1 h.im_lt hz
    have h2 := h.stripConst_le
    have h3 := h.norm_bulkTerm_le
    have h4 : a.re ^ 3 * Real.exp 0 ≤ modelScale a :=
      h.le_modelScale_of_saddle (by norm_num) (by linarith)
    have h5 : a.re ^ 0 * Real.exp 0 ≤ modelScale a :=
      h.le_modelScale_of_saddle (by norm_num) (by linarith)
    rw [Real.exp_zero, mul_one] at h4 h5
    rw [pow_zero] at h5
    have h6 : ‖bulkHalf (saddleTime a) a.im z - bulkTerm a / 2‖ ≤
        stripConst a.im * Real.exp 1 + ‖bulkTerm a‖ := by
      have h7 := norm_sub_le (bulkHalf (saddleTime a) a.im z) (bulkTerm a / 2)
      have e : ‖bulkTerm a / 2‖ = ‖bulkTerm a‖ / 2 := by
        rw [norm_div]
        simp
      rw [e] at h7
      linarith [norm_nonneg (bulkTerm a)]
    have h7 : stripConst a.im * Real.exp 1 ≤
        864 * polyAbsBound riemannCuspPoly * Real.exp 1 * modelScale a := by
      calc stripConst a.im * Real.exp 1
          ≤ 864 * polyAbsBound riemannCuspPoly * a.re ^ 3 * Real.exp 1 :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = 864 * polyAbsBound riemannCuspPoly * Real.exp 1 * a.re ^ 3 := by ring
        _ ≤ 864 * polyAbsBound riemannCuspPoly * Real.exp 1 * modelScale a :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
    have h8 : ‖bulkTerm a‖ ≤ ‖kernelC 0‖ * modelScale a :=
      h3.trans (le_mul_of_one_le_right (norm_nonneg _) h5)
    have h9 : 0 ≤ 3 * Cb * (1 + 864 * polyAbsBound riemannCuspPoly) * modelScale a := by
      positivity
    calc ‖bulkHalf (saddleTime a) a.im z - bulkTerm a / 2‖
        ≤ stripConst a.im * Real.exp 1 + ‖bulkTerm a‖ := h6
      _ ≤ 864 * polyAbsBound riemannCuspPoly * Real.exp 1 * modelScale a +
            ‖kernelC 0‖ * modelScale a := add_le_add h7 h8
      _ ≤ (3 * Cb * (1 + 864 * polyAbsBound riemannCuspPoly) +
            864 * polyAbsBound riemannCuspPoly * Real.exp 1 + ‖kernelC 0‖) * modelScale a := by
          linarith

/-! ## The two-term model -/

/-- **The two-term model on the wide region.** For every window `R` there is `C` such that on the
wide region with `Re a ≥ R` and for `|ζ| ≤ R`,
`|H_{τ(a)}(ζ/a) − B₀(a) − 2S₀(a) cos ζ| ≤ C σ⁵ e^{−σ} (|B₀(a)| + |S₀(a)|)`, `σ = Re a`. The heat
family is the two segment integrals and the two line integrals of the corner contour at the height
`Im a`; the segments give `B₀`, the lines give `S₀ e^{±iζ}`. -/
theorem exists_norm_complexHeat_sub_wide_model_le (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, WideRegion a → R ≤ a.re → ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖ ≤
        C * a.re ^ 5 * Real.exp (-a.re) * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_norm_bulkHalf_sub_le_scale
  have hΦ : 0 < ‖kernelC 0‖ := norm_pos_iff.mpr kernelC_zero_ne_zero
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hπ := Real.pi_pos
  set B : ℝ := polyAbsBound riemannCuspPoly with hBdef
  set c₃ : ℝ := (5120 * π ^ 2 + 584 * B) * Real.exp 4 with hc₃
  have hc₃0 : 0 ≤ c₃ := by positivity
  set C₀ : ℝ := 2 * Cb + 3456 * B * Real.exp R + 2 * Real.exp R * c₃ with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀ * (1 + 1 / ‖kernelC 0‖), by positivity, fun a h hRa ζ hζ => ?_⟩
  have hσ := h.re_pos
  have h1σ : (1 : ℝ) ≤ a.re := by linarith [h.1]
  have ha := h.ne_zero
  have hη0 := h.2.1
  have hη := h.im_lt
  have hτ0 := h.time_re_pos
  have hmS := h.modelScale_nonneg
  -- the point `z = ζ/a`
  have hza : ζ / a * a = ζ := div_mul_cancel₀ ζ ha
  have hzn : ‖ζ / a‖ * ‖a‖ = ‖ζ‖ := by rw [← norm_mul, hza]
  have hzσ : ‖ζ / a‖ * a.re ≤ R := by
    have := mul_le_mul_of_nonneg_left ((le_abs_self a.re).trans (Complex.abs_re_le_norm a))
      (norm_nonneg (ζ / a))
    linarith
  have hz1 : ‖ζ / a‖ ≤ 1 :=
    le_of_mul_le_mul_right (by linarith : ‖ζ / a‖ * a.re ≤ 1 * a.re) hσ
  have hz1' : ‖-(ζ / a)‖ ≤ 1 := by rw [norm_neg]; exact hz1
  have hzσ' : ‖-(ζ / a)‖ * a.re ≤ R := by rw [norm_neg]; exact hzσ
  -- the four pieces
  have hb1 := hCb a h (ζ / a) hz1
  have hb2 := hCb a h (-(ζ / a)) hz1'
  have hl1 := norm_lineHalf_sub_le h1σ hη0 hη h.P_re_ge hτ0.le h.time_re_le hz1 hzσ
  have hl2 := norm_lineHalf_sub_le h1σ hη0 hη h.P_re_ge hτ0.le h.time_re_le hz1' hzσ'
  have hSE0 := h.saddleErr_nonneg
  have him := abs_le.mp ((Complex.abs_im_le_norm ζ).trans hζ)
  have hi1 : Real.exp ((saddlePhaseValue a).re - (ζ / a * a).im) ≤
      Real.exp R * Real.exp ((saddlePhaseValue a).re) := by
    rw [← Real.exp_add, hza]
    exact Real.exp_le_exp.mpr (by linarith [him.1])
  have hi2 : Real.exp ((saddlePhaseValue a).re - (-(ζ / a) * a).im) ≤
      Real.exp R * Real.exp ((saddlePhaseValue a).re) := by
    rw [← Real.exp_add, neg_mul, hza, Complex.neg_im]
    exact Real.exp_le_exp.mpr (by linarith [him.2])
  have hcos : 2 * saddleTerm a * Complex.cos ζ =
      saddleTerm a * cexp (I * (ζ / a) * a) + saddleTerm a * cexp (I * -(ζ / a) * a) := by
    have e1 : I * (ζ / a) * a = ζ * I := by rw [mul_assoc, hza, mul_comm]
    have e2 : I * -(ζ / a) * a = -ζ * I := by rw [mul_assoc, neg_mul, hza, mul_comm]
    rw [e1, e2, Complex.cos]
    ring
  have hdec : complexHeat (saddleTime a) (ζ / a) - bulkTerm a -
      2 * saddleTerm a * Complex.cos ζ =
      (bulkHalf (saddleTime a) a.im (ζ / a) - bulkTerm a / 2) +
        (bulkHalf (saddleTime a) a.im (-(ζ / a)) - bulkTerm a / 2) +
        (lineHalf (saddleTime a) a.im (ζ / a) - saddleTerm a * cexp (I * (ζ / a) * a)) +
        (lineHalf (saddleTime a) a.im (-(ζ / a)) -
          saddleTerm a * cexp (I * -(ζ / a) * a)) := by
    rw [complexHeat_eq_corner (saddleTime a) (ζ / a) hη0 hη, hcos]
    ring
  have htotal : ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a -
      2 * saddleTerm a * Complex.cos ζ‖ ≤
      2 * (Cb * modelScale a) + 2 * leftErr R a +
        2 * (Real.exp R * (Real.exp ((saddlePhaseValue a).re) * saddleErr a)) := by
    rw [hdec]
    have h3 := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hl1)) hl2)
    refine h3.trans ?_
    have h4 := mul_le_mul_of_nonneg_right hi1 hSE0
    have h5 := mul_le_mul_of_nonneg_right hi2 hSE0
    linarith
  have hF2 := h.leftErr_le_scale R
  have hF3 := mul_le_mul_of_nonneg_left h.exp_mul_saddleErr_le_scale (Real.exp_pos R).le
  calc ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖
      ≤ 2 * (Cb * modelScale a) + 2 * leftErr R a +
          2 * (Real.exp R * (Real.exp ((saddlePhaseValue a).re) * saddleErr a)) := htotal
    _ ≤ C₀ * modelScale a := by
        rw [hC₀, hc₃]
        linarith
    _ ≤ C₀ * ((1 + 1 / ‖kernelC 0‖) * (a.re ^ 5 * Real.exp (-a.re)) *
          (‖bulkTerm a‖ + ‖saddleTerm a‖)) := mul_le_mul_of_nonneg_left h.modelScale_le hC₀0
    _ = C₀ * (1 + 1 / ‖kernelC 0‖) * a.re ^ 5 * Real.exp (-a.re) *
          (‖bulkTerm a‖ + ‖saddleTerm a‖) := by ring

/-- **The two-term model with a small relative error.** For every window `R` and `ε > 0` there is
`σ₀` such that for saddles of the wide region with `Re a ≥ σ₀` and `|ζ| ≤ R`,
`|H_{τ(a)}(ζ/a) − B₀(a) − 2S₀(a) cos ζ| ≤ ε(|B₀(a)| + |S₀(a)|)`. -/
theorem exists_forall_norm_complexHeat_sub_wide_model_le (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ₀ : ℝ, ∀ a : ℂ, WideRegion a → σ₀ ≤ a.re → ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖ ≤
        ε * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_complexHeat_sub_wide_model_le R
  have ht : Tendsto (fun x : ℝ => C * (x ^ 5 * Real.exp (-x))) atTop (𝓝 (C * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).const_mul C
  rw [mul_zero] at ht
  obtain ⟨σ₀, hσ₀⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hε))
  refine ⟨max σ₀ R, fun a h hσ ζ hζ =>
    (hC a h ((le_max_right _ _).trans hσ) ζ hζ).trans ?_⟩
  have h1 := (hσ₀ a.re ((le_max_left _ _).trans hσ)).le
  have h2 : 0 ≤ ‖bulkTerm a‖ + ‖saddleTerm a‖ := by positivity
  calc C * a.re ^ 5 * Real.exp (-a.re) * (‖bulkTerm a‖ + ‖saddleTerm a‖)
      = C * (a.re ^ 5 * Real.exp (-a.re)) * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by ring
    _ ≤ ε * (‖bulkTerm a‖ + ‖saddleTerm a‖) := mul_le_mul_of_nonneg_right h1 h2

/-! ## The saddle region -/

namespace SaddleRegion

variable {a : ℂ}

theorem re_pos (h : SaddleRegion a) : 0 < a.re := h.wide.re_pos

theorem dist_le (h : SaddleRegion a) : π / 4 - a.im ≤ 1 / 50 :=
  h.2.2.trans (one_div_le_one_div_of_le (by norm_num) h.1)

theorem im_lt (h : SaddleRegion a) : a.im < π / 4 := h.wide.im_lt

theorem half_le_im (h : SaddleRegion a) : 1 / 2 ≤ a.im := by
  have := Real.pi_gt_three
  linarith [h.dist_le]

theorem im_le_one (h : SaddleRegion a) : a.im ≤ 1 := h.wide.im_le_one

theorem le_cos (h : SaddleRegion a) : 1 / (4 * a.re) ≤ Real.cos (2 * a.im) := h.wide.le_cos

theorem cos_le (h : SaddleRegion a) : Real.cos (2 * a.im) ≤ 2 / a.re := by
  have hδ0 : 0 ≤ π / 4 - a.im := by linarith [h.im_lt]
  have h1 := Real.sin_le (x := 2 * (π / 4 - a.im)) (by linarith)
  have h2 : 2 * (π / 4 - a.im) ≤ 2 / a.re := by
    rw [show (2 : ℝ) / a.re = 2 * (1 / a.re) by ring]
    linarith [h.2.2]
  rw [SaddleRegion.cos_eq]
  linarith

theorem cos_pos (h : SaddleRegion a) : 0 < Real.cos (2 * a.im) := h.wide.cos_pos

theorem half_le_sin (h : SaddleRegion a) : 1 / 2 ≤ Real.sin (2 * a.im) := by
  have hδ0 : 0 ≤ π / 4 - a.im := by linarith [h.im_lt]
  have hδ1 := h.dist_le
  have e : Real.sin (2 * a.im) = Real.cos (2 * (π / 4 - a.im)) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * (π / 4 - a.im))
  rw [e]
  nlinarith

theorem pi_exp_le (h : SaddleRegion a) :
    π * Real.exp (2 * a.re) ≤ 4 * a.re * (saddleP a).re := h.wide.pi_exp_le

theorem P_re_ge (h : SaddleRegion a) : 18 ≤ (saddleP a).re := h.wide.P_re_ge

theorem P_re_pos (h : SaddleRegion a) : 0 < (saddleP a).re := h.wide.P_re_pos

theorem normSq_bounds (h : SaddleRegion a) :
    a.re ^ 2 ≤ Complex.normSq a ∧ Complex.normSq a ≤ 2 * a.re ^ 2 := h.wide.normSq_bounds

theorem le_time_re (h : SaddleRegion a) :
    π * Real.exp (2 * a.re) / (8 * a.re ^ 2) ≤ (saddleTime a).re := h.wide.le_time_re

theorem time_re_pos (h : SaddleRegion a) : 0 < (saddleTime a).re := h.wide.time_re_pos

theorem time_re_le (h : SaddleRegion a) : 8 * (saddleTime a).re ≤ (saddleP a).re :=
  h.wide.time_re_le

theorem ne_zero (h : SaddleRegion a) : a ≠ 0 := h.wide.ne_zero

theorem norm_time_le (h : SaddleRegion a) : ‖saddleTime a‖ ≤ π * Real.exp (2 * a.re) :=
  h.wide.norm_time_le

theorem le_norm_bulkTerm (h : SaddleRegion a) :
    ‖kernelC 0‖ * Real.exp (-a.re) ≤ ‖bulkTerm a‖ := h.wide.le_norm_bulkTerm

theorem le_norm_saddleTerm (h : SaddleRegion a) :
    Real.exp (7 * a.re / 2 + (saddlePhaseValue a).re) ≤ ‖saddleTerm a‖ :=
  h.wide.le_norm_saddleTerm

end SaddleRegion

/-- The two-term model on the saddle region with the window `|ζ| ≤ 8`. -/
theorem exists_norm_complexHeat_sub_model_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, SaddleRegion a → ∀ ζ : ℂ, ‖ζ‖ ≤ 8 →
      ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖ ≤
        C * a.re ^ 5 * Real.exp (-a.re) * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_complexHeat_sub_wide_model_le 8
  exact ⟨C, hC0, fun a h ζ hζ => hC a h.wide (by linarith [h.1]) ζ hζ⟩

/-- The two-term model on the saddle region with a small relative error, window `|ζ| ≤ 8`. -/
theorem exists_forall_norm_complexHeat_sub_model_le {ε : ℝ} (hε : 0 < ε) :
    ∃ σ₀ : ℝ, ∀ a : ℂ, SaddleRegion a → σ₀ ≤ a.re → ∀ ζ : ℂ, ‖ζ‖ ≤ 8 →
      ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖ ≤
        ε * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
  obtain ⟨σ₀, h⟩ := exists_forall_norm_complexHeat_sub_wide_model_le 8 hε
  exact ⟨σ₀, fun a ha hσ ζ hζ => h a ha.wide hσ ζ hζ⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
