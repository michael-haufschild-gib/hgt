import GaloisForLFunctions.GaloisTheoryOfZeros.TheLineThroughTheSaddleIsAGaussianAtTheSaddleValue

/-!
# The heat family at a saddle time is a constant plus a cosine

Let the saddle `a = σ + iη` approach the edge `η = π/4` of the strip of the kernel at the rate
`1/(4σ) ≤ π/4 − η ≤ 1/σ` (`SaddleRegion`). The time `τ(a) = πe^{2a}/a` is then a forward time close
to the imaginary direction: `Re τ ≍ e^{2σ}/σ²` against `|τ| ≍ e^{2σ}/σ`. At this time the heat
family has two stationary contributions of comparable type,

`H_{τ(a)}(ζ/a) = B₀(a) + 2S₀(a) cos ζ + O(σ⁵e^{−σ})(|B₀(a)| + |S₀(a)|)`, `|ζ| ≤ 8`:

* the bulk term `B₀(a) = iΦ(0)(π/τ)^{1/2}` from the stationary point `x = 0` of `e^{τx²}`;
* the saddle term `S₀(a)e^{±iζ}`, `S₀(a) = 4π²e^{9a/2 + f(a)}(π/(2P − τ))^{1/2}`, from the saddles
  `±a` of `τx² − πe^{2x}`.

The zeros of the model `B₀ + 2S₀ cos ζ` collide at `ζ ∈ πℤ` when `2S₀ = ±B₀`.

* `SaddleRegion.*`: the sizes of `P`, `τ` and of the kernel constants on the region.
* `exists_norm_complexHeat_sub_model_le`: the model with the error `Cσ⁵e^{−σ}`.
* `exists_forall_norm_complexHeat_sub_model_le`: for every `ε > 0` the model holds with the
  relative error `ε` for `σ` large.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real Interval

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-- The bulk term `B₀(a) = iΦ(0)(π/τ(a))^{1/2}`. -/
def bulkTerm (a : ℂ) : ℂ := I * kernelC 0 * ((π : ℂ) / saddleTime a) ^ (1 / 2 : ℂ)

/-- The region of the saddles: `Re a ≥ 50` and `1/(4 Re a) ≤ π/4 − Im a ≤ 1/Re a`. -/
def SaddleRegion (a : ℂ) : Prop :=
  50 ≤ a.re ∧ 1 / (4 * a.re) ≤ π / 4 - a.im ∧ π / 4 - a.im ≤ 1 / a.re

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

/-! ## The saddle region -/

namespace SaddleRegion

variable {a : ℂ}

theorem re_pos (h : SaddleRegion a) : 0 < a.re := by linarith [h.1]

theorem dist_le (h : SaddleRegion a) : π / 4 - a.im ≤ 1 / 50 :=
  h.2.2.trans (one_div_le_one_div_of_le (by norm_num) h.1)

theorem im_lt (h : SaddleRegion a) : a.im < π / 4 := by
  have hσ := h.re_pos
  have h1 : 0 < 1 / (4 * a.re) := by positivity
  linarith [h.2.1]

theorem half_le_im (h : SaddleRegion a) : 1 / 2 ≤ a.im := by
  have := Real.pi_gt_three
  linarith [h.dist_le]

theorem im_le_one (h : SaddleRegion a) : a.im ≤ 1 := by
  have := h.im_lt
  have := Real.pi_lt_d2
  linarith

theorem cos_eq (a : ℂ) : Real.cos (2 * a.im) = Real.sin (2 * (π / 4 - a.im)) := by
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  ring

theorem le_cos (h : SaddleRegion a) : 1 / (4 * a.re) ≤ Real.cos (2 * a.im) := by
  have hπ := Real.pi_pos
  have hδ0 : 0 ≤ π / 4 - a.im := by linarith [h.im_lt]
  have h1 := Real.mul_le_sin (x := 2 * (π / 4 - a.im)) (by linarith)
    (by linarith [Real.pi_gt_three, h.dist_le])
  have h2 : π / 4 - a.im ≤ 2 / π * (2 * (π / 4 - a.im)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr Real.pi_le_four)]
  rw [cos_eq]
  linarith [h.2.1]

theorem cos_le (h : SaddleRegion a) : Real.cos (2 * a.im) ≤ 2 / a.re := by
  have hδ0 : 0 ≤ π / 4 - a.im := by linarith [h.im_lt]
  have h1 := Real.sin_le (x := 2 * (π / 4 - a.im)) (by linarith)
  have h2 : 2 * (π / 4 - a.im) ≤ 2 / a.re := by
    rw [show (2 : ℝ) / a.re = 2 * (1 / a.re) by ring]
    linarith [h.2.2]
  rw [cos_eq]
  linarith

theorem cos_pos (h : SaddleRegion a) : 0 < Real.cos (2 * a.im) := by
  have hσ := h.re_pos
  exact lt_of_lt_of_le (by positivity) h.le_cos

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

/-- `πe^{2σ} ≤ 4σ Re P`. -/
theorem pi_exp_le (h : SaddleRegion a) :
    π * Real.exp (2 * a.re) ≤ 4 * a.re * (saddleP a).re := by
  have hσ := h.re_pos
  have hE := Real.exp_pos (2 * a.re)
  have hπ := Real.pi_pos
  have h1 := h.le_cos
  rw [div_le_iff₀ (by positivity)] at h1
  rw [saddleP_re]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_pos hπ hE).le]

theorem P_re_ge (h : SaddleRegion a) : 18 ≤ (saddleP a).re := by
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

theorem P_re_pos (h : SaddleRegion a) : 0 < (saddleP a).re := by linarith [h.P_re_ge]

theorem time_re_eq (a : ℂ) : (saddleTime a).re =
    ((saddleP a).re * a.re + (saddleP a).im * a.im) / Complex.normSq a := by
  rw [saddleTime, Complex.div_re, ← add_div]

theorem normSq_bounds (h : SaddleRegion a) :
    a.re ^ 2 ≤ Complex.normSq a ∧ Complex.normSq a ≤ 2 * a.re ^ 2 := by
  rw [Complex.normSq_apply]
  have h1 := h.half_le_im
  have h2 := h.im_le_one
  have h3 := h.1
  constructor <;> nlinarith

/-- `Re τ ≥ πe^{2σ}/(8σ²)`: the time is forward. -/
theorem le_time_re (h : SaddleRegion a) :
    π * Real.exp (2 * a.re) / (8 * a.re ^ 2) ≤ (saddleTime a).re := by
  have hσ := h.re_pos
  have hπ := Real.pi_pos
  have hE := Real.exp_pos (2 * a.re)
  obtain ⟨hN1, hN2⟩ := h.normSq_bounds
  have hN : 0 < Complex.normSq a := lt_of_lt_of_le (by positivity) hN1
  have hp := h.P_re_pos
  have hQ : π * Real.exp (2 * a.re) / 2 ≤ (saddleP a).im := by
    rw [saddleP_im]
    nlinarith [mul_le_mul_of_nonneg_left h.half_le_sin (mul_pos hπ hE).le]
  have hη := h.half_le_im
  have hQ0 : 0 ≤ (saddleP a).im := le_trans (by positivity) hQ
  have h1 : π * Real.exp (2 * a.re) / 4 ≤ (saddleP a).im * a.im := by
    nlinarith [mul_le_mul hQ hη (by norm_num) hQ0]
  have h2 : 0 ≤ (saddleP a).re * a.re := mul_nonneg hp.le hσ.le
  have h3 : π * Real.exp (2 * a.re) * Complex.normSq a ≤
      π * Real.exp (2 * a.re) * (2 * a.re ^ 2) :=
    mul_le_mul_of_nonneg_left hN2 (mul_pos hπ hE).le
  have h4 : π * Real.exp (2 * a.re) / 4 * (8 * a.re ^ 2) ≤
      ((saddleP a).re * a.re + (saddleP a).im * a.im) * (8 * a.re ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [time_re_eq, div_le_div_iff₀ (by positivity) hN]
  linarith

theorem time_re_pos (h : SaddleRegion a) : 0 < (saddleTime a).re := by
  have hσ := h.re_pos
  have hπ := Real.pi_pos
  exact lt_of_lt_of_le (by positivity) h.le_time_re

/-- `8 Re τ ≤ Re P`. -/
theorem time_re_le (h : SaddleRegion a) : 8 * (saddleTime a).re ≤ (saddleP a).re := by
  have hσ := h.re_pos
  have hπ := Real.pi_pos
  have hE := Real.exp_pos (2 * a.re)
  obtain ⟨hN1, hN2⟩ := h.normSq_bounds
  have hN : 0 < Complex.normSq a := lt_of_lt_of_le (by positivity) hN1
  have hp := h.P_re_pos
  have hQle : (saddleP a).im ≤ π * Real.exp (2 * a.re) := by
    rw [saddleP_im]
    nlinarith [mul_le_mul_of_nonneg_left (Real.sin_le_one (2 * a.im)) (mul_pos hπ hE).le]
  have hQ0 : 0 ≤ (saddleP a).im := by
    rw [saddleP_im]
    exact mul_nonneg (mul_pos hπ hE).le (by linarith [h.half_le_sin])
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

theorem ne_zero (h : SaddleRegion a) : a ≠ 0 := by
  intro h0
  have := h.1
  rw [h0, Complex.zero_re] at this
  linarith

theorem norm_time_le (h : SaddleRegion a) : ‖saddleTime a‖ ≤ π * Real.exp (2 * a.re) := by
  have hπ := Real.pi_pos
  have h1 : 1 ≤ ‖a‖ := by linarith [(le_abs_self a.re).trans (Complex.abs_re_le_norm a), h.1]
  rw [saddleTime, norm_div, norm_saddleP]
  exact div_le_self (by positivity) h1

/-! ### The constants of the kernel on the region -/

theorem termConst_le (h : SaddleRegion a) :
    termConst riemannCuspPoly (π * Real.cos (2 * a.im) / 2) ≤
      54 * polyAbsBound riemannCuspPoly * a.re ^ 2 := by
  have hσ := h.re_pos
  have hπ := Real.pi_gt_three
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hc := h.cos_pos
  have hle := h.le_cos
  have hcl := h.cos_le
  rw [div_le_iff₀ (by positivity)] at hle
  have h50 : 2 / a.re ≤ 2 / 50 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h.1
  set a' : ℝ := π * Real.cos (2 * a.im) / 2 with ha'
  have ha0 : 0 < a' := by positivity
  have h1 : 1 ≤ 3 * a.re * a' := by
    rw [ha']
    nlinarith [mul_le_mul_of_nonneg_right hπ.le (mul_nonneg hσ.le hc.le)]
  have ha1 : a' ≤ 1 := by
    have hc2 : Real.cos (2 * a.im) ≤ 1 / 25 := by linarith
    have := mul_le_mul Real.pi_le_four hc2 hc.le (by norm_num : (0 : ℝ) ≤ 4)
    rw [ha']
    linarith
  have hdef : termConst riemannCuspPoly a' =
      polyAbsBound riemannCuspPoly * (2 / a' ^ 2 * Real.exp a') := by
    rw [termConst, natDegree_riemannCuspPoly]
    norm_num [Nat.factorial]
  have h2 : 2 / a' ^ 2 ≤ 18 * a.re ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_self_le_mul_self zero_le_one h1]
  have h3 : Real.exp a' ≤ 3 := by
    have := Real.exp_one_lt_d9
    have := Real.exp_le_exp.mpr ha1
    linarith
  have h4 : 2 / a' ^ 2 * Real.exp a' ≤ 18 * a.re ^ 2 * 3 :=
    mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
  rw [hdef]
  nlinarith [mul_le_mul_of_nonneg_left h4 hB]

/-- `K(η) ≤ 324 B σ³` on the region. -/
theorem stripConst_le (h : SaddleRegion a) :
    stripConst a.im ≤ 324 * polyAbsBound riemannCuspPoly * a.re ^ 3 := by
  have hσ := h.re_pos
  have hπ := Real.pi_gt_three
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hc := h.cos_pos
  have hle := h.le_cos
  have hcl := h.cos_le
  have hT := h.termConst_le
  rw [div_le_iff₀ (by positivity)] at hle
  have h50 : 2 / a.re ≤ 2 / 50 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h.1
  rw [stripConst]
  set a' : ℝ := π * Real.cos (2 * a.im) / 2 with ha'
  have ha0 : 0 < a' := by positivity
  have h1 : 1 ≤ 3 * a.re * a' := by
    rw [ha']
    nlinarith [mul_le_mul_of_nonneg_right hπ.le (mul_nonneg hσ.le hc.le)]
  have ha1 : a' ≤ 1 := by
    have hc2 : Real.cos (2 * a.im) ≤ 1 / 25 := by linarith
    have := mul_le_mul Real.pi_le_four hc2 hc.le (by norm_num : (0 : ℝ) ≤ 4)
    rw [ha']
    linarith
  -- `1 − e^{−a'} ≥ a'/2`
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
  have h6 : 1 / (6 * a.re) ≤ 1 - Real.exp (-a') := by
    have : 1 / (6 * a.re) ≤ a' / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have h60 : 0 < 1 / (6 * a.re) := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc termConst riemannCuspPoly a' ≤ 54 * polyAbsBound riemannCuspPoly * a.re ^ 2 := hT
    _ = 324 * polyAbsBound riemannCuspPoly * a.re ^ 3 * (1 / (6 * a.re)) := by
        field_simp
        ring
    _ ≤ 324 * polyAbsBound riemannCuspPoly * a.re ^ 3 * (1 - Real.exp (-a')) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)

theorem leadConst_le (h : SaddleRegion a) :
    leadConst a.im ≤ 56 * polyAbsBound riemannCuspPoly * a.re ^ 2 := by
  have hT := h.termConst_le
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have h1 : (1 : ℝ) ≤ a.re ^ 2 := by nlinarith [h.1]
  rw [leadConst]
  nlinarith [mul_nonneg hB (sub_nonneg.mpr h1)]

/-! ### The sizes of the two terms -/

theorem exp_neg_sq_mul_exp (σ : ℝ) : Real.exp (-σ) ^ 2 * Real.exp (2 * σ) = 1 := by
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  have : -σ + -σ + 2 * σ = 0 := by ring
  rw [this, Real.exp_zero]

/-- `|B₀(a)| ≥ |Φ(0)| e^{−σ}`. -/
theorem le_norm_bulkTerm (h : SaddleRegion a) :
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

/-- `|S₀(a)| ≥ e^{7σ/2 + Re f(a)}`. -/
theorem le_norm_saddleTerm (h : SaddleRegion a) :
    Real.exp (7 * a.re / 2 + (saddleValue a).re) ≤ ‖saddleTerm a‖ := by
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
  have h2 : (9 * a / 2 + saddleValue a).re = 9 * a.re / 2 + (saddleValue a).re := by
    have h3 : (9 * a / 2).re = 9 * a.re / 2 := by simp
    rw [Complex.add_re, h3]
  have h4 : Real.exp (7 * a.re / 2 + (saddleValue a).re) =
      Real.exp (9 * a.re / 2 + (saddleValue a).re) * Real.exp (-a.re) := by
    rw [← Real.exp_add]
    ring_nf
  have hX := Real.exp_pos (9 * a.re / 2 + (saddleValue a).re)
  rw [saddleTerm, norm_mul, norm_mul, h1, Complex.norm_exp, h2, norm_cpow_half, h4]
  calc Real.exp (9 * a.re / 2 + (saddleValue a).re) * Real.exp (-a.re)
      ≤ 4 * π ^ 2 * Real.exp (9 * a.re / 2 + (saddleValue a).re) * (Real.exp (-a.re) / 2) := by
        have h5 : (0 : ℝ) ≤ 2 * π ^ 2 - 1 := by nlinarith
        nlinarith [mul_nonneg h5 (mul_pos hX (Real.exp_pos (-a.re))).le]
    _ ≤ 4 * π ^ 2 * Real.exp (9 * a.re / 2 + (saddleValue a).re) *
          Real.sqrt (π / ‖2 * saddleP a - saddleTime a‖) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-! ### The three errors on the region -/

theorem exp_neg_two_mul_exp (σ : ℝ) : Real.exp (-(2 * σ)) * Real.exp (2 * σ) = 1 := by
  rw [← Real.exp_add]
  simp

/-- The error of the bulk term: `(1 + K(η))/Re τ ≤ 3(1 + 324B) σ⁵ e^{−2σ}`. -/
theorem bulk_error_le (h : SaddleRegion a) :
    (1 + stripConst a.im) / (saddleTime a).re ≤
      3 * (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) := by
  have hσ := h.re_pos
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hπ := Real.pi_gt_three
  have hK := h.stripConst_le
  have hτ := h.le_time_re
  have hτ0 := h.time_re_pos
  have h1 : (1 : ℝ) ≤ a.re ^ 3 := one_le_pow₀ (by linarith [h.1])
  have h2 : 1 + stripConst a.im ≤ (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 3 := by
    nlinarith
  have hX : 0 ≤ (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 3 := by positivity
  have h3 : (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 3 ≤
      3 * (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
        (π * Real.exp (2 * a.re) / (8 * a.re ^ 2)) := by
    have e : 3 * (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
        (π * Real.exp (2 * a.re) / (8 * a.re ^ 2)) =
        3 * π / 8 * ((1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 3) *
          (Real.exp (-(2 * a.re)) * Real.exp (2 * a.re)) := by
      field_simp
    rw [e, exp_neg_two_mul_exp, mul_one]
    have h4 : (1 : ℝ) ≤ 3 * π / 8 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h4 hX]
  rw [div_le_iff₀ hτ0]
  calc 1 + stripConst a.im ≤ (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 3 := h2
    _ ≤ 3 * (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
          (π * Real.exp (2 * a.re) / (8 * a.re ^ 2)) := h3
    _ ≤ 3 * (1 + 324 * polyAbsBound riemannCuspPoly) * a.re ^ 5 * Real.exp (-(2 * a.re)) *
          (saddleTime a).re := mul_le_mul_of_nonneg_left hτ (by positivity)

/-- The error to the left of the saddle. -/
theorem leftErr_le (h : SaddleRegion a) :
    leftErr a ≤ 324 * polyAbsBound riemannCuspPoly * Real.exp 8 * a.re ^ 4 *
      Real.exp (a.re / 2) * (Real.exp (-(3 * a.re)) + Real.exp ((saddleValue a).re)) := by
  have hσ := h.re_pos
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hπ := Real.pi_gt_three
  have hK := h.stripConst_le
  have hK0 := stripConst_nonneg (by linarith [h.half_le_im]) h.im_lt
  have h1 : Real.exp (-(a.im ^ 2 * (saddleTime a).re)) ≤ Real.exp (-(3 * a.re)) := by
    refine Real.exp_le_exp.mpr ?_
    have hτ := h.le_time_re
    have hE := two_thirds_pow_le_exp hσ.le
    have h2 : a.re ^ 2 / 4 ≤ (saddleTime a).re := by
      refine le_trans ?_ hτ
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hπ.le (Real.exp_pos (2 * a.re)).le]
    have h3 : (1 : ℝ) / 4 ≤ a.im ^ 2 := by nlinarith [h.half_le_im]
    have h4 : 1 / 4 * (a.re ^ 2 / 4) ≤ a.im ^ 2 * (saddleTime a).re :=
      mul_le_mul h3 h2 (by positivity) (sq_nonneg _)
    nlinarith [mul_nonneg hσ.le (by linarith [h.1] : (0 : ℝ) ≤ a.re - 48)]
  have h5 : Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re) ≤
      Real.exp ((saddleValue a).re) :=
    Real.exp_le_exp.mpr (by linarith [h.time_re_le, h.P_re_ge])
  rw [leftErr]
  calc a.re * (stripConst a.im * Real.exp (a.re / 2) * Real.exp 8 *
        (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
          Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re)))
      ≤ a.re * (324 * polyAbsBound riemannCuspPoly * a.re ^ 3 * Real.exp (a.re / 2) *
          Real.exp 8 * (Real.exp (-(3 * a.re)) + Real.exp ((saddleValue a).re))) := by
        refine mul_le_mul_of_nonneg_left ?_ hσ.le
        refine mul_le_mul ?_ (add_le_add h1 h5) (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = 324 * polyAbsBound riemannCuspPoly * Real.exp 8 * a.re ^ 4 * Real.exp (a.re / 2) *
          (Real.exp (-(3 * a.re)) + Real.exp ((saddleValue a).re)) := by ring

/-- The error at the saddle. -/
theorem saddleErr_le (h : SaddleRegion a) :
    saddleErr a ≤ (5120 * π ^ 2 + 224 * polyAbsBound riemannCuspPoly) * Real.exp 4 *
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
  have hL0 := leadConst_nonneg (by linarith [h.half_le_im]) h.im_lt
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
      224 * polyAbsBound riemannCuspPoly * Real.exp 4 * a.re ^ 2 * Real.exp (5 * a.re / 2) := by
    calc leadConst a.im * Real.exp (5 * a.re / 2) *
          (Real.exp 4 * (4 * (1 / Real.sqrt (saddleP a).re)))
        ≤ 56 * polyAbsBound riemannCuspPoly * a.re ^ 2 * Real.exp (5 * a.re / 2) *
            (Real.exp 4 * (4 * 1)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le) ?_
            (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 (by norm_num))
            (Real.exp_pos _).le
      _ = 224 * polyAbsBound riemannCuspPoly * Real.exp 4 * a.re ^ 2 *
            Real.exp (5 * a.re / 2) := by ring
  rw [saddleErr]
  linarith

theorem saddleErr_nonneg (h : SaddleRegion a) : 0 ≤ saddleErr a := by
  have hp0 := h.P_re_pos
  have hL0 := leadConst_nonneg (by linarith [h.half_le_im]) h.im_lt
  rw [saddleErr]
  positivity

end SaddleRegion

/-! ## The two-term model -/

/-- **The two-term model.** On the saddle region and for `|ζ| ≤ 8`,
`|H_{τ(a)}(ζ/a) − B₀(a) − 2S₀(a) cos ζ| ≤ C σ⁵ e^{−σ} (|B₀(a)| + |S₀(a)|)`, `σ = Re a`. The heat
family is the two segment integrals and the two line integrals of the corner contour; the segments
give `B₀`, the lines give `S₀ e^{±iζ}`. -/
theorem exists_norm_complexHeat_sub_model_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, SaddleRegion a → ∀ ζ : ℂ, ‖ζ‖ ≤ 8 →
      ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖ ≤
        C * a.re ^ 5 * Real.exp (-a.re) * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_norm_bulkHalf_sub_le
  have hΦ : 0 < ‖kernelC 0‖ := norm_pos_iff.mpr kernelC_zero_ne_zero
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have hπ := Real.pi_pos
  set B : ℝ := polyAbsBound riemannCuspPoly with hBdef
  set c₃ : ℝ := 5120 * π ^ 2 + 224 * B with hc₃
  have hc₃0 : 0 ≤ c₃ := by positivity
  set C₀ : ℝ := 6 * Cb * (1 + 324 * B) + 648 * B * Real.exp 8 + 2 * Real.exp 12 * c₃ with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀ * (1 + 1 / ‖kernelC 0‖), by positivity, fun a h ζ hζ => ?_⟩
  have hσ := h.re_pos
  have h1σ : (1 : ℝ) ≤ a.re := by linarith [h.1]
  have ha := h.ne_zero
  have hη0 : 0 ≤ a.im := by linarith [h.half_le_im]
  have hη := h.im_lt
  have hτ0 := h.time_re_pos
  -- the point `z = ζ/a`
  have hza : ζ / a * a = ζ := div_mul_cancel₀ ζ ha
  have hzn : ‖ζ / a‖ * ‖a‖ = ‖ζ‖ := by rw [← norm_mul, hza]
  have hzσ : ‖ζ / a‖ * a.re ≤ 8 := by
    have := mul_le_mul_of_nonneg_left ((le_abs_self a.re).trans (Complex.abs_re_le_norm a))
      (norm_nonneg (ζ / a))
    linarith
  have hz1 : ‖ζ / a‖ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h.1 (norm_nonneg (ζ / a))
    linarith
  have hz1' : ‖-(ζ / a)‖ ≤ 1 := by rw [norm_neg]; exact hz1
  have hzσ' : ‖-(ζ / a)‖ * a.re ≤ 8 := by rw [norm_neg]; exact hzσ
  -- the four pieces
  have hb1 := hCb (saddleTime a) (ζ / a) a.im hτ0 h.half_le_im hη hz1
  have hb2 := hCb (saddleTime a) (-(ζ / a)) a.im hτ0 h.half_le_im hη hz1'
  have hl1 := norm_lineHalf_sub_le h1σ hη0 hη h.P_re_ge hτ0.le h.time_re_le hz1 hzσ
  have hl2 := norm_lineHalf_sub_le h1σ hη0 hη h.P_re_ge hτ0.le h.time_re_le hz1' hzσ'
  have hSE0 := h.saddleErr_nonneg
  have him := abs_le.mp ((Complex.abs_im_le_norm ζ).trans hζ)
  have hi1 : Real.exp ((saddleValue a).re - (ζ / a * a).im) ≤
      Real.exp 8 * Real.exp ((saddleValue a).re) := by
    rw [← Real.exp_add, hza]
    exact Real.exp_le_exp.mpr (by linarith [him.2])
  have hi2 : Real.exp ((saddleValue a).re - (-(ζ / a) * a).im) ≤
      Real.exp 8 * Real.exp ((saddleValue a).re) := by
    rw [← Real.exp_add, neg_mul, hza, Complex.neg_im]
    exact Real.exp_le_exp.mpr (by linarith [him.1])
  have hcos : 2 * saddleTerm a * Complex.cos ζ =
      saddleTerm a * cexp (I * (ζ / a) * a) + saddleTerm a * cexp (I * -(ζ / a) * a) := by
    have e1 : I * (ζ / a) * a = ζ * I := by rw [mul_assoc, hza, mul_comm]
    have e2 : I * -(ζ / a) * a = -ζ * I := by rw [mul_assoc, neg_mul, hza, mul_comm]
    rw [e1, e2, Complex.cos]
    ring
  have hdec : complexHeat (saddleTime a) (ζ / a) - bulkTerm a -
      2 * saddleTerm a * Complex.cos ζ =
      (bulkHalf (saddleTime a) a.im (ζ / a) -
          I * kernelC 0 / 2 * ((π : ℂ) / saddleTime a) ^ (1 / 2 : ℂ)) +
        (bulkHalf (saddleTime a) a.im (-(ζ / a)) -
          I * kernelC 0 / 2 * ((π : ℂ) / saddleTime a) ^ (1 / 2 : ℂ)) +
        (lineHalf (saddleTime a) a.im (ζ / a) - saddleTerm a * cexp (I * (ζ / a) * a)) +
        (lineHalf (saddleTime a) a.im (-(ζ / a)) -
          saddleTerm a * cexp (I * -(ζ / a) * a)) := by
    rw [complexHeat_eq_corner (saddleTime a) (ζ / a) hη0 hη, hcos, bulkTerm]
    ring
  have htotal : ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a -
      2 * saddleTerm a * Complex.cos ζ‖ ≤
      2 * (Cb * ((1 + stripConst a.im) / (saddleTime a).re)) + 2 * leftErr a +
        2 * (Real.exp 8 * Real.exp ((saddleValue a).re) * saddleErr a) := by
    rw [hdec]
    have h3 := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hl1)) hl2)
    refine h3.trans ?_
    have h4 := mul_le_mul_of_nonneg_right hi1 hSE0
    have h5 := mul_le_mul_of_nonneg_right hi2 hSE0
    rw [mul_div_assoc]
    linarith
  -- the scales
  set W : ℝ := a.re ^ 5 * Real.exp (-a.re) with hW
  have hW0 : 0 ≤ W := by positivity
  set bS : ℝ := Real.exp (-a.re) with hbS
  set sS : ℝ := Real.exp (7 * a.re / 2 + (saddleValue a).re) with hsS
  have hbS0 : 0 < bS := Real.exp_pos _
  have hsS0 : 0 < sS := Real.exp_pos _
  have hp45 : a.re ^ 4 ≤ a.re ^ 5 := pow_le_pow_right₀ h1σ (by norm_num)
  have hp25 : a.re ^ 2 ≤ a.re ^ 5 := pow_le_pow_right₀ h1σ (by norm_num)
  have hWb : W * bS = a.re ^ 5 * Real.exp (-a.re + -a.re) := by
    rw [hW, hbS, Real.exp_add]
    ring
  have hWs : W * sS = a.re ^ 5 * Real.exp (-a.re + (7 * a.re / 2 + (saddleValue a).re)) := by
    rw [hW, hsS, hbS, Real.exp_add (-a.re), mul_assoc]
  -- the bulk error
  have hF1 : 2 * (Cb * ((1 + stripConst a.im) / (saddleTime a).re)) ≤
      6 * Cb * (1 + 324 * B) * (W * bS) := by
    have h1 := mul_le_mul_of_nonneg_left h.bulk_error_le hCb0
    have e : Real.exp (-(2 * a.re)) = Real.exp (-a.re + -a.re) := by ring_nf
    rw [e] at h1
    rw [hWb]
    linarith
  -- the error to the left of the saddle
  have hA1 : a.re ^ 4 * (Real.exp (a.re / 2) * Real.exp (-(3 * a.re))) ≤ W * bS := by
    rw [hWb, ← Real.exp_add]
    exact mul_le_mul hp45 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
  have hA2 : a.re ^ 4 * (Real.exp (a.re / 2) * Real.exp ((saddleValue a).re)) ≤ W * sS := by
    rw [hWs, ← Real.exp_add]
    exact mul_le_mul hp45 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
  have hF2 : 2 * leftErr a ≤ 648 * B * Real.exp 8 * (W * bS + W * sS) := by
    have h1 := h.leftErr_le
    have h2 : 0 ≤ 324 * B * Real.exp 8 := by positivity
    have h3 := mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) h2
    have e : 324 * B * Real.exp 8 * a.re ^ 4 * Real.exp (a.re / 2) *
        (Real.exp (-(3 * a.re)) + Real.exp ((saddleValue a).re)) =
        324 * B * Real.exp 8 * (a.re ^ 4 * (Real.exp (a.re / 2) * Real.exp (-(3 * a.re))) +
          a.re ^ 4 * (Real.exp (a.re / 2) * Real.exp ((saddleValue a).re))) := by ring
    rw [e] at h1
    linarith
  -- the error at the saddle
  have hF3 : 2 * (Real.exp 8 * Real.exp ((saddleValue a).re) * saddleErr a) ≤
      2 * Real.exp 12 * c₃ * (W * sS) := by
    have h1 := h.saddleErr_le
    have e12 : Real.exp 8 * Real.exp 4 = Real.exp 12 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : a.re ^ 2 * (Real.exp ((saddleValue a).re) * Real.exp (5 * a.re / 2)) ≤ W * sS := by
      rw [hWs, ← Real.exp_add]
      exact mul_le_mul hp25 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (by positivity)
    have h3 : Real.exp 8 * Real.exp ((saddleValue a).re) * saddleErr a ≤
        Real.exp 8 * Real.exp ((saddleValue a).re) *
          (c₃ * Real.exp 4 * a.re ^ 2 * Real.exp (5 * a.re / 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : Real.exp 8 * Real.exp ((saddleValue a).re) *
        (c₃ * Real.exp 4 * a.re ^ 2 * Real.exp (5 * a.re / 2)) =
        (Real.exp 8 * Real.exp 4) * c₃ *
          (a.re ^ 2 * (Real.exp ((saddleValue a).re) * Real.exp (5 * a.re / 2))) := by ring
    rw [e, e12] at h3
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ Real.exp 12 * c₃)
    linarith
  -- the scales against the two terms
  have hXb : W * bS ≤ W * (‖bulkTerm a‖ / ‖kernelC 0‖) := by
    refine mul_le_mul_of_nonneg_left ?_ hW0
    rw [le_div_iff₀ hΦ]
    linarith [h.le_norm_bulkTerm]
  have hXs : W * sS ≤ W * ‖saddleTerm a‖ :=
    mul_le_mul_of_nonneg_left h.le_norm_saddleTerm hW0
  have hXb0 : 0 ≤ W * bS := by positivity
  have hXs0 : 0 ≤ W * sS := by positivity
  have h9 : ‖bulkTerm a‖ / ‖kernelC 0‖ + ‖saddleTerm a‖ ≤
      (1 + 1 / ‖kernelC 0‖) * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
    have e : (1 + 1 / ‖kernelC 0‖) * (‖bulkTerm a‖ + ‖saddleTerm a‖) =
        ‖bulkTerm a‖ + ‖saddleTerm a‖ + ‖bulkTerm a‖ / ‖kernelC 0‖ +
          ‖saddleTerm a‖ / ‖kernelC 0‖ := by ring
    have := div_nonneg (norm_nonneg (saddleTerm a)) hΦ.le
    have := norm_nonneg (bulkTerm a)
    linarith
  calc ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖
      ≤ 2 * (Cb * ((1 + stripConst a.im) / (saddleTime a).re)) + 2 * leftErr a +
          2 * (Real.exp 8 * Real.exp ((saddleValue a).re) * saddleErr a) := htotal
    _ ≤ C₀ * (W * bS + W * sS) := by
        have g1 : 0 ≤ 6 * Cb * (1 + 324 * B) * (W * sS) := by positivity
        have g2 : 0 ≤ 2 * Real.exp 12 * c₃ * (W * bS) := by positivity
        rw [hC₀]
        linarith
    _ ≤ C₀ * (W * (‖bulkTerm a‖ / ‖kernelC 0‖) + W * ‖saddleTerm a‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hXb hXs) hC₀0
    _ = C₀ * W * (‖bulkTerm a‖ / ‖kernelC 0‖ + ‖saddleTerm a‖) := by ring
    _ ≤ C₀ * W * ((1 + 1 / ‖kernelC 0‖) * (‖bulkTerm a‖ + ‖saddleTerm a‖)) :=
        mul_le_mul_of_nonneg_left h9 (by positivity)
    _ = C₀ * (1 + 1 / ‖kernelC 0‖) * a.re ^ 5 * Real.exp (-a.re) *
          (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
        rw [hW]
        ring

/-- **The two-term model with a small relative error.** For every `ε > 0` there is `σ₀` such that
for saddles of the region with `Re a ≥ σ₀` and `|ζ| ≤ 8`,
`|H_{τ(a)}(ζ/a) − B₀(a) − 2S₀(a) cos ζ| ≤ ε(|B₀(a)| + |S₀(a)|)`. -/
theorem exists_forall_norm_complexHeat_sub_model_le {ε : ℝ} (hε : 0 < ε) :
    ∃ σ₀ : ℝ, ∀ a : ℂ, SaddleRegion a → σ₀ ≤ a.re → ∀ ζ : ℂ, ‖ζ‖ ≤ 8 →
      ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖ ≤
        ε * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_complexHeat_sub_model_le
  have ht : Tendsto (fun x : ℝ => C * (x ^ 5 * Real.exp (-x))) atTop (𝓝 (C * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).const_mul C
  rw [mul_zero] at ht
  obtain ⟨σ₀, hσ₀⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hε))
  refine ⟨σ₀, fun a h hσ ζ hζ => (hC a h ζ hζ).trans ?_⟩
  have h1 := (hσ₀ a.re hσ).le
  have h2 : 0 ≤ ‖bulkTerm a‖ + ‖saddleTerm a‖ := by positivity
  calc C * a.re ^ 5 * Real.exp (-a.re) * (‖bulkTerm a‖ + ‖saddleTerm a‖)
      = C * (a.re ^ 5 * Real.exp (-a.re)) * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by ring
    _ ≤ ε * (‖bulkTerm a‖ + ‖saddleTerm a‖) := mul_le_mul_of_nonneg_right h1 h2

end

end GaloisForLFunctions.GaloisTheoryOfZeros
