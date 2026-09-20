import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

open UpperHalfPlane Set Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

/-! A globally smooth, positive retraction to a prescribed positive height. -/

noncomputable def heightRetraction (ε y : ℝ) : ℝ :=
  ε + (y - ε) * Real.smoothTransition (y / ε)

/-- Above the cutoff, the height retraction is the identity. -/
lemma heightRetraction_eq_self {ε y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) :
    heightRetraction ε y = y := by
  have hratio : 1 ≤ y / ε := (le_div_iff₀ hε).mpr (by simpa using hy)
  rw [heightRetraction, Real.smoothTransition.one_of_one_le hratio]
  ring

/-- The height retraction never leaves the upper half-plane. -/
lemma heightRetraction_pos {ε y : ℝ} (hε : 0 < ε) : 0 < heightRetraction ε y := by
  by_cases hy : y ≤ 0
  · rw [heightRetraction, Real.smoothTransition.zero_of_nonpos]
    · linarith
    · exact div_nonpos_of_nonpos_of_nonneg hy hε.le
  by_cases hεy : ε ≤ y
  · rw [heightRetraction_eq_self hε hεy]
    exact lt_of_not_ge hy
  have hypos : 0 < y := lt_of_not_ge hy
  have hyε : y ≤ ε := le_of_not_ge hεy
  have hs0 : 0 ≤ Real.smoothTransition (y / ε) := Real.smoothTransition.nonneg _
  have hs1 : Real.smoothTransition (y / ε) ≤ 1 := Real.smoothTransition.le_one _
  have hprod : 0 ≤ (ε - y) * (1 - Real.smoothTransition (y / ε)) :=
    mul_nonneg (sub_nonneg.mpr hyε) (sub_nonneg.mpr hs1)
  have hle : y ≤ heightRetraction ε y := by
    rw [heightRetraction]
    nlinarith
  exact hypos.trans_le hle

/-- The retraction is smooth, so it preserves `C¹` chart regularity under composition. -/
lemma contDiff_heightRetraction (ε : ℝ) : ContDiff ℝ ∞ (heightRetraction ε) := by
  unfold heightRetraction
  fun_prop

/-- Strictly above its cutoff, the retraction agrees with the identity on a whole neighborhood. -/
lemma heightRetraction_eventuallyEq_id {ε y : ℝ} (hε : 0 < ε) (hy : ε < y) :
    heightRetraction ε =ᶠ[𝓝 y] id := by
  filter_upwards [Ioi_mem_nhds hy] with t ht
  simpa only [id_eq] using heightRetraction_eq_self hε ht.le

/-- A real rectangle is sent smoothly into the complex upper half-plane. -/
noncomputable def retractedPoint (ε : ℝ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) + (heightRetraction ε p.2 : ℂ) * Complex.I

lemma retractedPoint_im (ε : ℝ) (p : ℝ × ℝ) :
    (retractedPoint ε p).im = heightRetraction ε p.2 := by
  simp [retractedPoint]

lemma retractedPoint_im_pos {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    0 < (retractedPoint ε p).im := by
  rw [retractedPoint_im]
  exact heightRetraction_pos hε

lemma retractedPoint_eq_of_le {ε x y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) :
    retractedPoint ε (x, y) = (x : ℂ) + (y : ℂ) * Complex.I := by
  rw [retractedPoint, heightRetraction_eq_self hε hy]

lemma contDiff_retractedPoint (ε : ℝ) : ContDiff ℝ ∞ (retractedPoint ε) := by
  have hRe : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hIm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (heightRetraction ε p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_heightRetraction ε).comp contDiff_snd)
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
    (p.1 : ℂ) + (heightRetraction ε p.2 : ℂ) * Complex.I)
  exact hRe.add (hIm.mul contDiff_const)

/-- At every height strictly above the cutoff, retraction has the original two-dimensional germ. -/
lemma retractedPoint_eventuallyEq_standard {ε x y : ℝ} (hε : 0 < ε) (hy : ε < y) :
    retractedPoint ε =ᶠ[𝓝 (x, y)]
      fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  have h := (heightRetraction_eventuallyEq_id hε hy).comp_tendsto
    (continuous_snd.tendsto (x, y))
  filter_upwards [h] with p hp
  change heightRetraction ε p.2 = p.2 at hp
  simp [retractedPoint, hp]

/-- A `C¹` upper-half-plane chart field has a global `C¹` pullback through the positive retraction. -/
lemma contDiff_retractedField {F : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hF : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im}) :
    ContDiff ℝ 1 (fun p => F (retractedPoint ε p)) := by
  refine contDiff_iff_contDiffAt.mpr fun p => ?_
  exact (hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
    (retractedPoint_im_pos hε p))).comp p
      ((contDiff_retractedPoint ε).of_le (by simp)).contDiffAt

end GaloisForLFunctions.HTGeometry
