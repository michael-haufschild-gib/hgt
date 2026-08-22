import GaloisForLFunctions.RHTower.MellinHardyBridge
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyShift

/-!
# The Mellin transform of a datum with a constant head

Burnol's extended Sonine space consists of data which are *constant*, not zero, below the aperture.
The Mellin transform of the constant head `c·1_{(0,a)}` is `c a^{1-s}/(1-s)`, so the renormalised
transform `(s-1)/s · a^{s-1/2} f̂(s)` splits as `-c a^{1/2}/s` plus a bounded multiple of the
half-plane Laplace transform of the tail.  Both summands lie in the Hardy space: this is the
identification of `ℂ·1_{(0,a)} + L²(a,∞)` with `s/(s-1)A^sH²` (arXiv:math/0203120, §4).

## Main results

* `integral_head_cpow`
* `renormalised_mellin_headTail`
* `isHalfPlaneHardy_renormalisedHeadTail`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The Mellin transform of a constant head.** -/
theorem integral_head_cpow (a : ℝ) {s : ℂ} (hs : s.re < 1) :
    (∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)) = ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s) := by
  have hne : (1 : ℂ) - s ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) - s).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hr : -1 < (-s).re := by
    rw [Complex.neg_re]
    linarith
  have h := integral_cpow (a := (0 : ℝ)) (b := a) (r := -s) (Or.inl hr)
  have hsum : -s + 1 = (1 : ℂ) - s := by ring
  rw [hsum] at h
  rw [h, Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero]

theorem integral_head_cpow_Ioc {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s.re < 1) (c : ℂ) :
    (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * c)
      = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s) := by
  have hcongr : (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * c)
      = (∫ t in (0 : ℝ)..a, ((t : ℝ) : ℂ) ^ (-s)) * c := by
    rw [intervalIntegral.integral_of_le ha.le, ← MeasureTheory.integral_mul_const]
  rw [hcongr, integral_head_cpow a hs]
  ring

/-! ### The renormalising multiplier -/

theorem norm_shift_ratio_le {w : ℂ} (hw : 0 < w.re) :
    ‖(w - 1 / 2) / (w + 1 / 2)‖ ≤ 3 := by
  have hre : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hlow : (1 : ℝ) / 2 ≤ ‖w + 1 / 2‖ := by
    have h1 : (w + 1 / 2).re ≤ ‖w + 1 / 2‖ := Complex.re_le_norm _
    rw [Complex.add_re, hre] at h1
    linarith
  have hpos : (0 : ℝ) < ‖w + 1 / 2‖ := by linarith
  have hdiff : ‖w - 1 / 2‖ ≤ ‖w + 1 / 2‖ + 1 := by
    have h2 : ‖w - 1 / 2‖ - ‖w + 1 / 2‖ ≤ ‖(w - 1 / 2) - (w + 1 / 2)‖ :=
      norm_sub_norm_le _ _
    have h3 : ((w - 1 / 2) - (w + 1 / 2)) = (-1 : ℂ) := by ring
    rw [h3] at h2
    simp only [norm_neg, norm_one] at h2
    linarith
  rw [norm_div, div_le_iff₀ hpos]
  linarith

theorem differentiableOn_shift_ratio :
    DifferentiableOn ℂ (fun w : ℂ => (w - 1 / 2) / (w + 1 / 2)) {w : ℂ | 0 < w.re} := by
  refine DifferentiableOn.div (differentiableOn_id.sub_const _) (differentiableOn_id.add_const _)
    (fun w hw => ?_)
  intro hzero
  have hre : (w + 1 / 2).re = 0 := by rw [hzero]; simp
  have hw' : (0 : ℝ) < w.re := hw
  have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  rw [Complex.add_re, h2] at hre
  linarith

/-- **The renormalised Mellin transform of a datum with a constant head.** -/
theorem renormalised_mellin_headTail {a : ℝ} (ha : 0 < a) (c : ℂ) (g : ℝ → ℂ) {s : ℂ}
    (hs : s.re < 1) (hs0 : s ≠ 0) :
    ((s - 1) / s) * (((a : ℝ) : ℂ) ^ (s - 1 / 2)) *
        ((∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * c)
          + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * g t)
      = -(c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2)) / s
        + ((s - 1) / s) * laplaceRay (logChart a g) (s - 1 / 2) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hne : (1 : ℂ) - s ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) - s).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith
  rw [integral_head_cpow_Ioc ha hs c, mellinTail_eq_laplaceRay ha g s]
  have hpow1 : ((a : ℝ) : ℂ) ^ (s - 1 / 2) * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hane]
    congr 1
    ring
  have hpow2 : ((a : ℝ) : ℂ) ^ (s - 1 / 2) * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) = 1 := by
    rw [← Complex.cpow_add _ _ hane]
    have hzero : (s - 1 / 2) + ((1 : ℂ) / 2 - s) = 0 := by ring
    rw [hzero, Complex.cpow_zero]
  have hkey : ((a : ℝ) : ℂ) ^ (s - 1 / 2)
      * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)
        + ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * laplaceRay (logChart a g) (s - 1 / 2))
      = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 - s)
        + laplaceRay (logChart a g) (s - 1 / 2) := by
    have e1 : ((a : ℝ) : ℂ) ^ (s - 1 / 2) * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s))
        = c * (((a : ℝ) : ℂ) ^ (s - 1 / 2) * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)) / (1 - s) := by
      ring
    have e2 : ((a : ℝ) : ℂ) ^ (s - 1 / 2)
        * (((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * laplaceRay (logChart a g) (s - 1 / 2))
        = (((a : ℝ) : ℂ) ^ (s - 1 / 2) * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s))
          * laplaceRay (logChart a g) (s - 1 / 2) := by ring
    rw [mul_add, e1, e2, hpow1, hpow2, one_mul]
  rw [mul_assoc, hkey]
  field_simp
  ring

/-- **The renormalised Mellin transform of a datum with a constant head is a Hardy function.** -/
theorem isHalfPlaneHardy_renormalisedHeadTail {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) :
    ∃ M : ℝ, IsHalfPlaneHardy
      (fun w => -(c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2)) * (w + 1 / 2)⁻¹
        + (w - 1 / 2) / (w + 1 / 2) * laplaceRay (logChart a g) w) M := by
  have hhalf : (0 : ℝ) < ((1 : ℂ) / 2).re := by norm_num
  have h1 := isHalfPlaneHardy_inv_shift hhalf
  have h1' := isHalfPlaneHardy_const_mul h1 (-(c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2)))
  have h2 := isHalfPlaneHardy_laplaceRay (memLp_two_logChart ha hg)
  have h2' := isHalfPlaneHardy_mul_of_bounded h2 differentiableOn_shift_ratio
    (C := 3) (fun w hw => norm_shift_ratio_le hw)
  refine ⟨_, (isHalfPlaneHardy_add h1' h2').congr (fun w _ => ?_)⟩
  ring


end

end RHTower
