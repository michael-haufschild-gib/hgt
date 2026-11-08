import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanComplexVKContour
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanComplexClock
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainUniversalVKAbsorption

/-!
# Universal arithmetic saving on complex clock disks

The moving Mellin rectangle controls fixed-radius disks around every large real clock. Universal polynomial absorption preserves one saving exponent throughout each disk.
-/

open Complex RHTower Filter MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- One arithmetic saving holds throughout fixed complex disks about every sufficiently large clock. -/
theorem exists_narainMeanClock_disk_universal_vk_bound (Y Z : Height) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ z ∈ Metric.closedBall (L : ℂ) (Real.pi / 16),
        ‖narainMeanComplexClock Y Z z‖ ≤ C * Real.exp (-(L * vkHadamardWidth L / 128)) := by
  obtain ⟨δ, T₀, C, N, hδ, hT₀, hTexp, hC, hcontour⟩ :=
    exists_narainMeanBoundary_complex_vk_contour_bound Y Z
  obtain ⟨B, hB, hsave⟩ := exists_narainVK_saving_universal hδ N
  let r : ℝ := Real.pi / 16
  let E : ℝ := Real.exp (r / 8) + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨(C + 1) * E * B / (2 * Real.pi), by positivity, ?_⟩
  filter_upwards [hsave, eventually_ge_atTop (max T₀ r)] with L hsave hL
  have hLT : T₀ ≤ L := (le_max_left _ _).trans hL
  have hLr : r ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 ≤ L := hr.le.trans hLr
  have hw : 0 < vkHadamardWidth (2 * L + 1) := by
    apply vkHadamardWidth_pos
    linarith only [hTexp, hLT, hL0]
  have hd : 0 ≤ narainVKWidth δ L := by unfold narainVKWidth; positivity
  have hd8 : narainVKWidth δ L ≤ 1 / 8 := by
    unfold narainVKWidth
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right δ 1)) (by norm_num)
  have hQ : 0 ≤ narainVKCost L := (zero_le_one : (0 : ℝ) ≤ 1).trans
    (one_le_narainVKCost (by linarith only [hTexp, hLT, hL0]))
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have him : |z.im| ≤ r := by
    have h := (Complex.abs_im_le_norm (z - (L : ℂ))).trans hz
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h
  have hre : L - r ≤ z.re := by
    have h := (Complex.abs_re_le_norm (z - (L : ℂ))).trans hz
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    have hlow := (abs_le.mp h).1
    dsimp only [r]
    linarith only [hlow]
  have hz0 : 0 ≤ z.re := by linarith only [hLr, hre]
  have hzstrip : |z.im| ≤ Real.pi / 8 := him.trans (by dsimp only [r]; nlinarith only [Real.pi_pos])
  have hraw := hcontour z L hz0 hzstrip hLT
  have hleft : Real.exp (-(narainVKWidth δ L * z.re)) ≤
      Real.exp (r / 8) * Real.exp (-(narainVKWidth δ L * L)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_left hre hd
    have hcost := mul_le_mul_of_nonneg_right hd8 hr.le
    nlinarith only [hprod, hcost]
  have htail : Real.exp (-(Real.pi * L / 8)) ≤ Real.exp (-(narainVKWidth δ L * L)) := by
    have hdpi : narainVKWidth δ L ≤ Real.pi / 8 :=
      hd8.trans (by linarith only [Real.pi_gt_three])
    have hprod := mul_le_mul_of_nonneg_right hdpi hL0
    apply Real.exp_le_exp.mpr
    linarith only [hprod]
  have hsum : Real.exp (-(narainVKWidth δ L * z.re)) + Real.exp (-(Real.pi * L / 8)) ≤
      E * (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4))) := by
    calc
      _ ≤ Real.exp (r / 8) * Real.exp (-(narainVKWidth δ L * L)) +
          Real.exp (-(narainVKWidth δ L * L)) := add_le_add hleft htail
      _ = E * Real.exp (-(narainVKWidth δ L * L)) := by dsimp only [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_nonneg _)) hE.le
  have hbound :
      ‖∫ t : ℝ, Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)‖ ≤
        (C + 1) * E * B * Real.exp (-(L * vkHadamardWidth L / 128)) := by
    calc
      _ ≤ C * (1 + L) ^ N * narainVKCost L *
          (E * (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4)))) :=
        hraw.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = C * E * ((1 + L) ^ N * narainVKCost L *
          (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4)))) := by ring
      _ ≤ (C + 1) * E * ((1 + L) ^ N * narainVKCost L *
          (Real.exp (-(narainVKWidth δ L * L)) + Real.exp (-(Real.pi * L / 4)))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)) hE.le)
          (by positivity)
      _ ≤ (C + 1) * E * (B * Real.exp (-(L * vkHadamardWidth L / 128))) :=
        mul_le_mul_of_nonneg_left hsave (by positivity)
      _ = _ := by ring
  rw [narainMeanComplexClock_eq_integral, norm_mul]
  have hn : ‖1 / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
  rw [hn]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((C + 1) * E * B * Real.exp (-(L * vkHadamardWidth L / 128))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

#print axioms exists_narainMeanClock_disk_universal_vk_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
