import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Confocal Abel defect flow

For a bounded complex source, the scale-dependent Bernstein ellipse excess is the confocal defect

`delta R z = |z| + |R-z| - R`.

This file proves pointwise monotonicity and the sharp uniform comparison with the transverse defect
`|z| - re z`.  Taking suprema gives a monotone source envelope with an explicit `O(1/R)` collar.
-/

open Complex Filter Topology
open scoped Real ComplexOrder

namespace HTGeometry

noncomputable section

/-- Confocal distance excess with foci `0` and `R`. -/
def confocalDefect (R : ℝ) (z : ℂ) : ℝ :=
  ‖z‖ + ‖(R : ℂ) - z‖ - R

/-- Limiting transverse defect of a complex coordinate. -/
def transverseDefect (z : ℂ) : ℝ :=
  ‖z‖ - z.re

/-- The affine Bernstein amplitude is exactly one plus the rescaled confocal defect. -/
theorem affineAmplitude_eq_one_add_confocalDefect_div
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖ =
      1 + confocalDefect R z / R := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hsub : 1 - z / (R : ℂ) = ((R : ℂ) - z) / (R : ℂ) := by
    field_simp [hR.ne']
  rw [hsub, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [confocalDefect]
  field_simp [hR.ne']
  ring

theorem transverseDefect_nonneg (z : ℂ) : 0 ≤ transverseDefect z := by
  rw [transverseDefect]
  exact sub_nonneg.mpr (Complex.re_le_norm z)

/-- Every confocal defect dominates the transverse defect. -/
theorem transverseDefect_le_confocalDefect {R : ℝ} (z : ℂ) :
    transverseDefect z ≤ confocalDefect R z := by
  rw [transverseDefect, confocalDefect]
  have h : R - z.re ≤ ‖(R : ℂ) - z‖ := by
    simpa using Complex.re_le_norm ((R : ℂ) - z)
  linarith

theorem confocalDefect_nonneg {R : ℝ} (z : ℂ) : 0 ≤ confocalDefect R z :=
  (transverseDefect_nonneg z).trans (transverseDefect_le_confocalDefect z)

/-- Increasing the second focus can only decrease the confocal excess. -/
theorem confocalDefect_antitone {R₁ R₂ : ℝ} (hR : R₁ ≤ R₂) (z : ℂ) :
    confocalDefect R₂ z ≤ confocalDefect R₁ z := by
  rw [confocalDefect, confocalDefect]
  have htri : ‖(R₂ : ℂ) - z‖ ≤ ‖((R₂ - R₁ : ℝ) : ℂ)‖ + ‖(R₁ : ℂ) - z‖ := by
    calc
      ‖(R₂ : ℂ) - z‖ =
          ‖((R₂ - R₁ : ℝ) : ℂ) + ((R₁ : ℂ) - z)‖ := by
            congr 1
            push_cast
            ring
      _ ≤ _ := norm_add_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hR)] at htri
  linarith

private theorem sqrt_sq_add_sq_sub_le
    {a b : ℝ} (ha : 0 < a) :
    0 ≤ Real.sqrt (a ^ 2 + b ^ 2) - a ∧
      Real.sqrt (a ^ 2 + b ^ 2) - a ≤ b ^ 2 / (2 * a) := by
  have hrad : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hsqa : Real.sqrt (a ^ 2) = a := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hsqrt_ge : a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    have hs0 := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
    have hs2 := Real.sq_sqrt hrad
    nlinarith [sq_nonneg b]
  constructor
  · linarith
  · let s := Real.sqrt (a ^ 2 + b ^ 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hrad
    have hden : 0 < s + a := by positivity
    have hid : s - a = b ^ 2 / (s + a) := by
      apply (eq_div_iff hden.ne').2
      nlinarith
    rw [hid]
    have hdenle : 2 * a ≤ s + a := by linarith
    exact div_le_div_of_nonneg_left (sq_nonneg b) (by positivity) hdenle

/-- Sharp pointwise collar: the confocal excess differs from its transverse limit by at most
`M²/(2(R-M))` on the closed disk of radius `M`. -/
theorem confocalDefect_sub_transverseDefect_bounds
    {M R : ℝ} (hM : 0 ≤ M) (hRM : M < R) {z : ℂ} (hz : ‖z‖ ≤ M) :
    0 ≤ confocalDefect R z - transverseDefect z ∧
      confocalDefect R z - transverseDefect z ≤ M ^ 2 / (2 * (R - M)) := by
  let a : ℝ := R - z.re
  let b : ℝ := z.im
  have hzre : z.re ≤ M := (Complex.re_le_norm z).trans hz
  have ha : 0 < a := by dsimp [a]; linarith
  have hRM0 : 0 < R - M := sub_pos.mpr hRM
  have haRM : R - M ≤ a := by dsimp [a]; linarith
  have hnorm : ‖(R : ℂ) - z‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply, map_sub, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero]
    dsimp [a, b]
    ring
  have hsqrt := sqrt_sq_add_sq_sub_le (b := b) ha
  have hbM : b ^ 2 ≤ M ^ 2 := by
    have hbabs : |b| ≤ ‖z‖ := by
      dsimp [b]
      exact Complex.abs_im_le_norm z
    have hb : |b| ≤ M := hbabs.trans hz
    rw [sq_le_sq]
    simpa [abs_of_nonneg hM] using hb
  have hdiv₁ : b ^ 2 / (2 * a) ≤ b ^ 2 / (2 * (R - M)) := by
    exact div_le_div_of_nonneg_left (sq_nonneg b) (by positivity) (by nlinarith)
  have hdiv₂ : b ^ 2 / (2 * (R - M)) ≤ M ^ 2 / (2 * (R - M)) := by
    exact div_le_div_of_nonneg_right hbM (by positivity)
  have hrewrite : confocalDefect R z - transverseDefect z =
      Real.sqrt (a ^ 2 + b ^ 2) - a := by
    rw [confocalDefect, transverseDefect, hnorm]
    dsimp [a]
    ring
  rw [hrewrite]
  exact ⟨hsqrt.1, hsqrt.2.trans (hdiv₁.trans hdiv₂)⟩

/-- A simple uniform upper bound used to justify source suprema. -/
theorem confocalDefect_le_two_mul_norm {R : ℝ} (hR : 0 ≤ R) (z : ℂ) :
    confocalDefect R z ≤ 2 * ‖z‖ := by
  rw [confocalDefect]
  have htri : ‖(R : ℂ) - z‖ ≤ ‖(R : ℂ)‖ + ‖z‖ := norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at htri
  rw [abs_of_nonneg hR] at htri
  linarith

/-- Supremal confocal defect of a source set. -/
def confocalDefectEnvelope (S : Set ℂ) (R : ℝ) : ℝ :=
  sSup (confocalDefect R '' S)

/-- Supremal limiting transverse defect of a source set. -/
def transverseDefectEnvelope (S : Set ℂ) : ℝ :=
  sSup (transverseDefect '' S)

private theorem bddAbove_confocalDefect_image
    {S : Set ℂ} {M R : ℝ} (hR : 0 ≤ R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    BddAbove (confocalDefect R '' S) := by
  refine ⟨2 * max M 0, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hzM : ‖z‖ ≤ M := hbound z hz
  exact (confocalDefect_le_two_mul_norm (R := R) hR z).trans
    (mul_le_mul_of_nonneg_left (hzM.trans (le_max_left _ _)) (by norm_num))

private theorem bddAbove_transverseDefect_image
    {S : Set ℂ} {M : ℝ} (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    BddAbove (transverseDefect '' S) := by
  refine ⟨2 * max M 0, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  rw [transverseDefect]
  have hre : -‖z‖ ≤ z.re := neg_le_of_abs_le (Complex.abs_re_le_norm z)
  have hzM := (hbound z hz).trans (le_max_left M 0)
  nlinarith

/-- The supremal confocal defect is nonnegative for a nonempty source. -/
theorem confocalDefectEnvelope_nonneg {S : Set ℂ} (hne : S.Nonempty)
    {M R : ℝ} (hR : 0 ≤ R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    0 ≤ confocalDefectEnvelope S R := by
  rcases hne with ⟨z, hz⟩
  exact (confocalDefect_nonneg z).trans
    (le_csSup (bddAbove_confocalDefect_image hR hbound) ⟨z, hz, rfl⟩)

/-- Source envelopes inherit the pointwise antitone flow. -/
theorem confocalDefectEnvelope_antitone
    {S : Set ℂ} (hne : S.Nonempty) {M R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR : R₁ ≤ R₂)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    confocalDefectEnvelope S R₂ ≤ confocalDefectEnvelope S R₁ := by
  rw [confocalDefectEnvelope, confocalDefectEnvelope]
  apply csSup_le (hne.image _)
  rintro y ⟨z, hz, rfl⟩
  exact (confocalDefect_antitone hR z).trans
    (le_csSup (bddAbove_confocalDefect_image hR₁ hbound) ⟨z, hz, rfl⟩)

/-- Sharp two-sided collar for a bounded nonempty source. -/
theorem transverseDefectEnvelope_le_confocalDefectEnvelope_le
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hRM : M < R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    transverseDefectEnvelope S ≤ confocalDefectEnvelope S R ∧
      confocalDefectEnvelope S R ≤
        transverseDefectEnvelope S + M ^ 2 / (2 * (R - M)) := by
  have hR0 : 0 ≤ R := le_trans hM hRM.le
  have hbConf := bddAbove_confocalDefect_image hR0 hbound
  have hbTrans := bddAbove_transverseDefect_image hbound
  constructor
  · rw [transverseDefectEnvelope]
    apply csSup_le (hne.image _)
    rintro y ⟨z, hz, rfl⟩
    exact (transverseDefect_le_confocalDefect z).trans
      (le_csSup hbConf ⟨z, hz, rfl⟩)
  · rw [confocalDefectEnvelope]
    apply csSup_le (hne.image _)
    rintro y ⟨z, hz, rfl⟩
    have hpoint := (confocalDefect_sub_transverseDefect_bounds hM hRM (hbound z hz)).2
    have hsup : transverseDefect z ≤ transverseDefectEnvelope S := by
      exact le_csSup hbTrans ⟨z, hz, rfl⟩
    linarith

/-- The scale-dependent affine-amplitude envelope, written intrinsically through the confocal
defect.  Pointwise this is `|z/R|+|1-z/R|`. -/
def confocalAmplitudeEnvelope (S : Set ℂ) (R : ℝ) : ℝ :=
  1 + confocalDefectEnvelope S R / R

/-- Abel radius selected by the squared affine-amplitude envelope. -/
def confocalAbelRadius (S : Set ℂ) (R : ℝ) : ℝ :=
  (confocalAmplitudeEnvelope S R ^ 2)⁻¹

/-- The intrinsic amplitude envelope agrees with the literal supremum of affine Bernstein
amplitudes. -/
theorem sSup_affineAmplitude_eq_confocalAmplitudeEnvelope
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ} (hR : 0 < R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    sSup ((fun z : ℂ => ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖) '' S) =
      confocalAmplitudeEnvelope S R := by
  let A : ℝ := sSup ((fun z : ℂ => ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖) '' S)
  have hbDef := bddAbove_confocalDefect_image hR.le hbound
  have hbAmp : BddAbove
      ((fun z : ℂ => ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖) '' S) := by
    refine ⟨1 + 2 * max M 0 / R, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    change ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖ ≤ 1 + 2 * max M 0 / R
    rw [affineAmplitude_eq_one_add_confocalDefect_div hR]
    have hδ := (confocalDefect_le_two_mul_norm hR.le z).trans
      (mul_le_mul_of_nonneg_left
        ((hbound z hz).trans (le_max_left M 0)) (by norm_num))
    simpa only [add_comm] using
      add_le_add_left (div_le_div_of_nonneg_right hδ hR.le) 1
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro y ⟨z, hz, rfl⟩
    change ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖ ≤
      confocalAmplitudeEnvelope S R
    rw [affineAmplitude_eq_one_add_confocalDefect_div hR, confocalAmplitudeEnvelope,
      confocalDefectEnvelope]
    simpa only [add_comm] using
      add_le_add_left
        (div_le_div_of_nonneg_right
          (le_csSup hbDef ⟨z, hz, rfl⟩) hR.le) 1
  · have hpoint : ∀ z ∈ S,
        confocalDefect R z ≤ R * (A - 1) := by
      intro z hz
      have hamp : ‖z / (R : ℂ)‖ + ‖1 - z / (R : ℂ)‖ ≤ A :=
        le_csSup hbAmp ⟨z, hz, rfl⟩
      rw [affineAmplitude_eq_one_add_confocalDefect_div hR] at hamp
      have hquot : confocalDefect R z / R ≤ A - 1 := by
        linarith
      have hmul := (div_le_iff₀ hR).mp hquot
      simpa only [mul_comm] using hmul
    have hsup : confocalDefectEnvelope S R ≤ R * (A - 1) := by
      rw [confocalDefectEnvelope]
      apply csSup_le (hne.image _)
      rintro y ⟨z, hz, rfl⟩
      exact hpoint z hz
    rw [confocalAmplitudeEnvelope]
    have hquot : confocalDefectEnvelope S R / R ≤ A - 1 :=
      (div_le_iff₀ hR).2 (by simpa only [mul_comm] using hsup)
    change 1 + confocalDefectEnvelope S R / R ≤ A
    linarith

/-- Vanishing transverse defect is exactly positivity of every occupied coordinate on the real
axis. -/
theorem transverseDefectEnvelope_eq_zero_iff
    {S : Set ℂ} (hne : S.Nonempty) {M : ℝ}
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    transverseDefectEnvelope S = 0 ↔ ∀ z ∈ S, 0 ≤ z := by
  have hbTrans := bddAbove_transverseDefect_image hbound
  constructor
  · intro hzero z hz
    have hle : transverseDefect z ≤ 0 := by
      rw [← hzero]
      exact le_csSup hbTrans ⟨z, hz, rfl⟩
    have heq : transverseDefect z = 0 :=
      le_antisymm hle (transverseDefect_nonneg z)
    rw [transverseDefect, sub_eq_zero] at heq
    exact Complex.re_eq_norm.mp heq.symm
  · intro hpos
    rw [transverseDefectEnvelope]
    have himage : transverseDefect '' S = {0} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hre := Complex.re_eq_norm.mpr (hpos z hz)
        simp [transverseDefect, hre]
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rcases hne with ⟨z, hz⟩
        refine ⟨z, hz, ?_⟩
        have hre := Complex.re_eq_norm.mpr (hpos z hz)
        simpa [transverseDefect, hre] using hy.symm
    rw [himage, csSup_singleton]

/-- If the transverse envelope vanishes, then every sufficiently large confocal envelope vanishes
exactly, not merely asymptotically. -/
theorem confocalDefectEnvelope_eq_zero_of_transverse_eq_zero
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ} (hRM : M < R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) (hzero : transverseDefectEnvelope S = 0) :
    confocalDefectEnvelope S R = 0 := by
  have hpos := (transverseDefectEnvelope_eq_zero_iff hne hbound).mp hzero
  rw [confocalDefectEnvelope]
  have himage : confocalDefect R '' S = {0} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzpos := hpos z hz
      have hre : z.im = 0 := hzpos.2.symm
      have hzre : 0 ≤ z.re := hzpos.1
      have hzM : z.re ≤ M := (Complex.re_le_norm z).trans (hbound z hz)
      have hRz : 0 ≤ R - z.re := by linarith
      rw [confocalDefect, Complex.norm_def, Complex.norm_def]
      simp [Complex.normSq_apply, hre, hzre, hRz]
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rcases hne with ⟨z, hz⟩
      refine ⟨z, hz, ?_⟩
      have hzpos := hpos z hz
      have hre : z.im = 0 := hzpos.2.symm
      have hzre : 0 ≤ z.re := hzpos.1
      have hzM : z.re ≤ M := (Complex.re_le_norm z).trans (hbound z hz)
      have hRz : 0 ≤ R - z.re := by linarith
      rw [hy]
      rw [confocalDefect, Complex.norm_def, Complex.norm_def]
      simp [Complex.normSq_apply, hre, hzre, hRz]
  rw [himage, csSup_singleton]

/-- Exact critical-phase selection: above the source radius, unit amplitude is equivalent to
vanishing transverse defect. -/
theorem confocalAmplitudeEnvelope_eq_one_iff
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ} (hM : 0 ≤ M) (hRM : M < R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    confocalAmplitudeEnvelope S R = 1 ↔ transverseDefectEnvelope S = 0 := by
  have hR : 0 < R := hM.trans_lt hRM
  constructor
  · intro hB
    have hD : confocalDefectEnvelope S R = 0 := by
      rw [confocalAmplitudeEnvelope] at hB
      have hdiv : confocalDefectEnvelope S R / R = 0 := by
        linarith
      exact (div_eq_zero_iff.mp hdiv).resolve_right hR.ne'
    have hcollar :=
      transverseDefectEnvelope_le_confocalDefectEnvelope_le hne hM hRM hbound
    have hnonneg : 0 ≤ transverseDefectEnvelope S := by
      rcases hne with ⟨z, hz⟩
      exact (transverseDefect_nonneg z).trans
        (le_csSup (bddAbove_transverseDefect_image hbound) ⟨z, hz, rfl⟩)
    linarith
  · intro hzero
    rw [confocalAmplitudeEnvelope,
      confocalDefectEnvelope_eq_zero_of_transverse_eq_zero hne hRM hbound hzero]
    simp

/-- Equivalent exact selection statement for the Abel radius. -/
theorem confocalAbelRadius_eq_one_iff
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ} (hM : 0 ≤ M) (hRM : M < R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    confocalAbelRadius S R = 1 ↔ transverseDefectEnvelope S = 0 := by
  rw [confocalAbelRadius]
  have hBnonneg : 0 ≤ confocalAmplitudeEnvelope S R := by
    rw [confocalAmplitudeEnvelope]
    have hR : 0 < R := hM.trans_lt hRM
    have hD := confocalDefectEnvelope_nonneg hne hR.le hbound
    positivity
  constructor
  · intro hA
    have hBsq : confocalAmplitudeEnvelope S R ^ 2 = 1 := by
      exact inv_eq_one.mp hA
    have hB : confocalAmplitudeEnvelope S R = 1 := by nlinarith
    exact (confocalAmplitudeEnvelope_eq_one_iff hne hM hRM hbound).mp hB
  · intro hzero
    rw [(confocalAmplitudeEnvelope_eq_one_iff hne hM hRM hbound).mpr hzero]
    norm_num

private theorem tendsto_confocal_collar_zero (M : ℝ) :
    Tendsto (fun R : ℝ => M ^ 2 / (2 * (R - M))) atTop (nhds 0) := by
  have hshift : Tendsto (fun R : ℝ => R - M) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-M) tendsto_id)
  have hden : Tendsto (fun R : ℝ => 2 * (R - M)) atTop atTop :=
    hshift.const_mul_atTop (by norm_num)
  simpa only [Function.comp_apply, div_eq_mul_inv, zero_mul, mul_zero] using
    (tendsto_inv_atTop_zero.comp hden).const_mul (M ^ 2)

/-- The confocal envelope decreases to the normalization-free transverse envelope. -/
theorem tendsto_confocalDefectEnvelope_atTop
    {S : Set ℂ} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    Tendsto (confocalDefectEnvelope S) atTop
      (nhds (transverseDefectEnvelope S)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop M] with R hRM
    exact ha.trans_le
      (transverseDefectEnvelope_le_confocalDefectEnvelope_le hne hM hRM hbound).1
  · intro b hb
    have hgap : 0 < b - transverseDefectEnvelope S := sub_pos.mpr hb
    have hevent : ∀ᶠ R : ℝ in atTop,
        M ^ 2 / (2 * (R - M)) < b - transverseDefectEnvelope S :=
      (tendsto_order.1 (tendsto_confocal_collar_zero M)).2 _ hgap
    filter_upwards [eventually_gt_atTop M, hevent] with R hRM hsmall
    have hu :=
      (transverseDefectEnvelope_le_confocalDefectEnvelope_le hne hM hRM hbound).2
    linarith

/-- The affine-amplitude envelope tends to the unit boundary. -/
theorem tendsto_confocalAmplitudeEnvelope_atTop
    {S : Set ℂ} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    Tendsto (confocalAmplitudeEnvelope S) atTop (nhds 1) := by
  have hD := tendsto_confocalDefectEnvelope_atTop hne hM hbound
  have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  simpa only [confocalAmplitudeEnvelope, div_eq_mul_inv, mul_zero, add_zero] using
    tendsto_const_nhds.add (hD.mul hinv)

/-- First-order recession of the squared affine-amplitude envelope. -/
theorem tendsto_mul_confocalAmplitudeEnvelope_sq_sub_one
    {S : Set ℂ} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    Tendsto
      (fun R : ℝ => R * (confocalAmplitudeEnvelope S R ^ 2 - 1))
      atTop (nhds (2 * transverseDefectEnvelope S)) := by
  have hD := tendsto_confocalDefectEnvelope_atTop hne hM hbound
  have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hmodel : Tendsto
      (fun R : ℝ => 2 * confocalDefectEnvelope S R +
        confocalDefectEnvelope S R ^ 2 * R⁻¹)
      atTop (nhds (2 * transverseDefectEnvelope S)) := by
    simpa using (hD.const_mul 2).add ((hD.pow 2).mul hinv)
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [confocalAmplitudeEnvelope]
  field_simp [hR.ne']
  ring

/-- The exact Abel radii tend to one. -/
theorem tendsto_confocalAbelRadius_atTop
    {S : Set ℂ} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    Tendsto (confocalAbelRadius S) atTop (nhds 1) := by
  have hB := tendsto_confocalAmplitudeEnvelope_atTop hne hM hbound
  simpa only [confocalAbelRadius, one_pow, inv_one] using
    (hB.pow 2).inv₀ (pow_ne_zero 2 (by norm_num : (1 : ℝ) ≠ 0))

/-- First-order recession of the Abel-radius defect. -/
theorem tendsto_mul_one_sub_confocalAbelRadius
    {S : Set ℂ} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    Tendsto (fun R : ℝ => R * (1 - confocalAbelRadius S R))
      atTop (nhds (2 * transverseDefectEnvelope S)) := by
  have hnum := tendsto_mul_confocalAmplitudeEnvelope_sq_sub_one hne hM hbound
  have hB := tendsto_confocalAmplitudeEnvelope_atTop hne hM hbound
  have hdenInv : Tendsto
      (fun R : ℝ => (confocalAmplitudeEnvelope S R ^ 2)⁻¹)
      atTop (nhds 1) := by
    simpa using (hB.pow 2).inv₀ (pow_ne_zero 2 (by norm_num : (1 : ℝ) ≠ 0))
  have hmodel : Tendsto
      (fun R : ℝ => R * (confocalAmplitudeEnvelope S R ^ 2 - 1) *
        (confocalAmplitudeEnvelope S R ^ 2)⁻¹)
      atTop (nhds (2 * transverseDefectEnvelope S)) := by
    simpa only [mul_one] using hnum.mul hdenInv
  have hBpos : ∀ᶠ R : ℝ in atTop, 0 < confocalAmplitudeEnvelope S R :=
    (tendsto_order.1 hB).1 0 (by norm_num)
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hBpos] with R hR hBposR
  rw [confocalAbelRadius]
  field_simp [hR.ne', hBposR.ne']

end

end HTGeometry
