import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionMellin

/-!
# The analytic Bose defect kernel on the right half-plane

The kernel `h(t) = 1/t - 1/(exp t - 1)` of the chronological repair problem is
`ChronologicalTensor.fusionBoseDefect`. For the fixed-tail separation argument it has to be
recognised as the restriction of a genuinely complex analytic function, so that integrals
`u ↦ ∫ g(x) h(xu) dx` are analytic in `u` and an identity on `[1,2]` propagates to the whole
positive axis.

The removable singularity of `h` at `0` is never needed: the integrals evaluate `h` only at `x u`
with `x > 0` real, so it is enough that

  `boseKernelC z = 1/z - 1/(exp z - 1)`

is analytic on the **open right half-plane**, where `z ≠ 0` and `exp z = 1` is impossible because
`exp z = 1` forces `z.re = 0`.

Also recorded here: `h` is strictly positive on the positive axis, and its Mellin bracket
`∫₀^∞ h(y) y^(s-1) dy` is strictly positive for real `0 < s < 1`. The bracket is what gets
cancelled in the separation argument.
-/

noncomputable section
open Complex Set MeasureTheory
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-! ### The right half-plane -/

/-- The open right half-plane. -/
def rightHalfPlane_chronologicalTailKernelAnalytic : Set ℂ := {z : ℂ | 0 < z.re}

theorem mem_rightHalfPlane {z : ℂ} : z ∈ rightHalfPlane_chronologicalTailKernelAnalytic ↔ 0 < z.re := Iff.rfl

theorem isOpen_rightHalfPlane_chronologicalTailKernelAnalytic : IsOpen rightHalfPlane_chronologicalTailKernelAnalytic :=
  isOpen_lt continuous_const Complex.continuous_re

theorem convex_rightHalfPlane_chronologicalTailKernelAnalytic : Convex ℝ rightHalfPlane_chronologicalTailKernelAnalytic := by
  have : rightHalfPlane_chronologicalTailKernelAnalytic = {z : ℂ | 0 < Complex.reLm z} := rfl
  rw [this]
  exact convex_halfSpace_gt (LinearMap.isLinear Complex.reLm) 0

theorem isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane_chronologicalTailKernelAnalytic :=
  (convex_rightHalfPlane_chronologicalTailKernelAnalytic).isPreconnected

theorem ofReal_mem_rightHalfPlane {t : ℝ} (ht : 0 < t) : (t : ℂ) ∈ rightHalfPlane_chronologicalTailKernelAnalytic := by
  simpa [mem_rightHalfPlane] using ht

theorem mul_ofReal_mem_rightHalfPlane {x : ℝ} (hx : 0 < x) {u : ℂ}
    (hu : u ∈ rightHalfPlane_chronologicalTailKernelAnalytic) : (x : ℂ) * u ∈ rightHalfPlane_chronologicalTailKernelAnalytic := by
  rw [mem_rightHalfPlane, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  exact mul_pos hx hu

/-! ### The complex kernel -/

/-- The complex Bose defect kernel. -/
def boseKernelC (z : ℂ) : ℂ := 1 / z - 1 / (Complex.exp z - 1)

theorem exp_sub_one_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.exp z - 1 ≠ 0 := by
  intro h
  have h1 : Complex.exp z = 1 := by linear_combination h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  rw [hn] at hz
  simp at hz

theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h
  rw [h] at hz
  simp at hz

/-- **The kernel is analytic on the open right half-plane.** -/
theorem boseKernelC_differentiableOn :
    DifferentiableOn ℂ boseKernelC rightHalfPlane_chronologicalTailKernelAnalytic := by
  intro z hz
  have hz' : 0 < z.re := hz
  have hz0 : z ≠ 0 := ne_zero_of_re_pos hz'
  have hden : Complex.exp z - 1 ≠ 0 := exp_sub_one_ne_zero_of_re_pos hz'
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.sub ?_ ?_
  · exact (differentiableAt_const 1).div differentiableAt_id hz0
  · exact (differentiableAt_const 1).div
      ((Complex.differentiable_exp z).sub (differentiableAt_const 1)) hden

theorem boseKernelC_analyticOnNhd : AnalyticOnNhd ℂ boseKernelC rightHalfPlane_chronologicalTailKernelAnalytic :=
  boseKernelC_differentiableOn.analyticOnNhd isOpen_rightHalfPlane_chronologicalTailKernelAnalytic

/-- On the positive axis the complex kernel is the real Bose defect. -/
theorem boseKernelC_ofReal {t : ℝ} (ht : 0 < t) :
    boseKernelC (t : ℂ) = (fusionBoseDefect t : ℂ) := by
  have hexp : Complex.exp (t : ℂ) = ((Real.exp t : ℝ) : ℂ) := (Complex.ofReal_exp t).symm
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hden : Real.exp t - 1 ≠ 0 := by
    have := Real.one_lt_exp_iff.mpr ht
    linarith
  rw [boseKernelC, fusionBoseDefect, if_pos ht, hexp]
  push_cast
  ring

theorem boseKernelC_eq_fusionBoseKernel {t : ℝ} (ht : 0 < t) :
    boseKernelC (t : ℂ) = fusionBoseKernel t := by
  rw [boseKernelC_ofReal ht, fusionBoseKernel]

/-! ### Strict positivity -/

theorem fusionBoseDefect_pos {t : ℝ} (ht : 0 < t) : 0 < fusionBoseDefect t := by
  have he : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hd : 0 < Real.exp t - 1 := by linarith
  have hprod : 0 < t * (Real.exp t - 1) := mul_pos ht hd
  have hnum : 0 < Real.exp t - 1 - t := by
    have := Real.add_one_lt_exp (x := t) (ne_of_gt ht)
    linarith
  have hform : fusionBoseDefect t = (Real.exp t - 1 - t) / (t * (Real.exp t - 1)) := by
    rw [fusionBoseDefect, if_pos ht]
    field_simp
  rw [hform]
  exact div_pos hnum hprod

/-! ### The Mellin bracket -/

theorem integrableOn_boseDefect_rpow {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    IntegrableOn (fun y : ℝ => fusionBoseDefect y * y ^ (s - 1)) (Ioi 0) := by
  have hmem : (s : ℂ) ∈ fusionMellinStrip := by
    refine ⟨?_, ?_⟩
    · simpa using h0
    · simpa using h1
  have hconv := fusionBoseKernel_converges (s : ℂ) hmem
  have hnorm := hconv.norm
  refine hnorm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := hy
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, fusionBoseKernel_norm]
  rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  ring

/-- **The Mellin bracket is strictly positive.** This is the factor that gets cancelled in the
separation argument. -/
theorem boseMellinBracket_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    0 < ∫ y : ℝ in Ioi 0, fusionBoseDefect y * y ^ (s - 1) := by
  have hint := integrableOn_boseDefect_rpow h0 h1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun y : ℝ => fusionBoseDefect y * y ^ (s - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    exact mul_nonneg (fusionBoseDefect_bounds y).1 (Real.rpow_nonneg hy0.le _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsub : Ioo (1 : ℝ) 2
      ⊆ Function.support (fun y : ℝ => fusionBoseDefect y * y ^ (s - 1)) ∩ Ioi 0 := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by linarith [hy.1]
    refine ⟨?_, hy0⟩
    have : 0 < fusionBoseDefect y * y ^ (s - 1) :=
      mul_pos (fusionBoseDefect_pos hy0) (Real.rpow_pos_of_pos hy0 _)
    exact ne_of_gt this
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  norm_num

/-! ### The removable singularity at the origin -/

/-- The horizontal strip `|Im z| < 2π`. Inside it the only zero of `exp z - 1` is `z = 0`. -/
def boseStrip : Set ℂ := {z : ℂ | |z.im| < 2 * Real.pi}

theorem mem_boseStrip {z : ℂ} : z ∈ boseStrip ↔ |z.im| < 2 * Real.pi := Iff.rfl

theorem isOpen_boseStrip : IsOpen boseStrip := by
  have h : boseStrip = (fun z : ℂ => |z.im|) ⁻¹' (Iio (2 * Real.pi)) := rfl
  rw [h]
  exact IsOpen.preimage (continuous_abs.comp Complex.continuous_im) isOpen_Iio

theorem exp_sub_one_ne_zero_of_mem_boseStrip {z : ℂ} (hz : z ∈ boseStrip) (hz0 : z ≠ 0) :
    Complex.exp z - 1 ≠ 0 := by
  intro h
  have h1 : Complex.exp z = 1 := by linear_combination h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hnz : n ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp at hn
    exact hz0 hn
  have him : z.im = 2 * Real.pi * (n : ℝ) := by rw [hn]; simp; ring
  have h1n : (1 : ℝ) ≤ |(n : ℝ)| := by
    rcases lt_trichotomy n 0 with hlt | heq | hgt
    · rw [abs_of_neg (by exact_mod_cast hlt)]
      have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      linarith
    · exact absurd heq hnz
    · rw [abs_of_pos (by exact_mod_cast hgt)]
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hstrip : |z.im| < 2 * Real.pi := hz
  rw [him, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.pi)] at hstrip
  nlinarith

theorem boseKernelC_differentiableOn_punctured :
    DifferentiableOn ℂ boseKernelC (boseStrip \ {0}) := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => hz.2 (by simp [h])
  have hden := exp_sub_one_ne_zero_of_mem_boseStrip hz.1 hz0
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((differentiableAt_const 1).div differentiableAt_id hz0).sub
    ((differentiableAt_const 1).div
      ((Complex.differentiable_exp z).sub (differentiableAt_const 1)) hden)

/-- **The kernel is bounded near the origin.** The order-two cancellation between `1/z` and
`1/(exp z - 1)` is visible in the Taylor bound `‖exp z - 1 - z‖ ≤ ‖z‖²`. -/
theorem norm_boseKernelC_le_two {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1/2) :
    ‖boseKernelC z‖ ≤ 2 := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hz1 : ‖z‖ ≤ 1 := by linarith
  have htay : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hz1
  have hsplit : ‖z‖ ≤ ‖Complex.exp z - 1‖ + ‖Complex.exp z - 1 - z‖ := by
    have hid : z = (Complex.exp z - 1) - (Complex.exp z - 1 - z) := by ring
    calc ‖z‖ = ‖(Complex.exp z - 1) - (Complex.exp z - 1 - z)‖ := by rw [← hid]
      _ ≤ _ := norm_sub_le _ _
  have hlow : ‖z‖ / 2 ≤ ‖Complex.exp z - 1‖ := by nlinarith [hzn, hz, htay, hsplit]
  have hdenpos : 0 < ‖Complex.exp z - 1‖ := by linarith
  have hden : Complex.exp z - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenpos
    linarith
  have hform : boseKernelC z = (Complex.exp z - 1 - z) / (z * (Complex.exp z - 1)) := by
    rw [boseKernelC]
    field_simp
  rw [hform, norm_div, norm_mul, div_le_iff₀ (mul_pos hzn hdenpos)]
  nlinarith [htay, hlow, hzn, hdenpos]

/-- The analytic extension of the kernel across the removable singularity at the origin. -/
def boseKernelE : ℂ → ℂ :=
  Function.update boseKernelC 0 (Filter.limUnder (𝓝[≠] (0 : ℂ)) boseKernelC)

theorem boseKernelE_of_ne {z : ℂ} (hz : z ≠ 0) : boseKernelE z = boseKernelC z := by
  rw [boseKernelE]
  exact Function.update_of_ne hz _ _

theorem boseKernelE_ofReal {t : ℝ} (ht : 0 < t) :
    boseKernelE (t : ℂ) = (fusionBoseDefect t : ℂ) := by
  rw [boseKernelE_of_ne (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)), boseKernelC_ofReal ht]

theorem boseKernelE_differentiableOn_ball :
    DifferentiableOn ℂ boseKernelE (Metric.ball (0 : ℂ) (1/2)) := by
  refine Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/2)) ?_ ?_
  · refine boseKernelC_differentiableOn_punctured.mono ?_
    rintro z ⟨hz, hz0⟩
    have hzn : ‖z‖ < 1/2 := by
      simpa [Complex.dist_eq] using hz
    refine ⟨?_, hz0⟩
    have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hpi : 3 < Real.pi := Real.pi_gt_three
    exact mem_boseStrip.mpr (by linarith)
  · refine ⟨2, ?_⟩
    rintro y ⟨z, ⟨hz, hz0⟩, rfl⟩
    have hzne : z ≠ 0 := by simpa using hz0
    have hzn : ‖z‖ ≤ 1/2 := by
      have : ‖z‖ < 1/2 := by simpa [Complex.dist_eq] using hz
      linarith
    exact norm_boseKernelC_le_two hzne hzn

/-- **The kernel is analytic on the whole strip `|Im z| < 2π`.** -/
theorem boseKernelE_differentiableOn : DifferentiableOn ℂ boseKernelE boseStrip := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases hz0 : z = 0
  · subst hz0
    exact boseKernelE_differentiableOn_ball.differentiableAt
      (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/2))
  · have hopen : IsOpen (boseStrip \ {0}) := isOpen_boseStrip.sdiff isClosed_singleton
    have hmem : z ∈ boseStrip \ {0} := ⟨hz, by simpa using hz0⟩
    have heq : Set.EqOn boseKernelE boseKernelC (boseStrip \ {0}) := fun w hw =>
      boseKernelE_of_ne (by simpa using hw.2)
    have hd := boseKernelC_differentiableOn_punctured.differentiableAt (hopen.mem_nhds hmem)
    exact hd.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) heq)

theorem boseKernelE_analyticOnNhd : AnalyticOnNhd ℂ boseKernelE boseStrip :=
  boseKernelE_differentiableOn.analyticOnNhd isOpen_boseStrip

theorem boseKernelE_continuousOn : ContinuousOn boseKernelE boseStrip :=
  boseKernelE_differentiableOn.continuousOn

end RHTower
