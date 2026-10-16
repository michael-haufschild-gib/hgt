import GaloisForLFunctions.RHTower.WeilDilationRayCriterion
import GaloisForLFunctions.RHTower.WeilLevyHarmonicDoublingPairCoupling
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# The dilation ray at short scales

For `T ≤ 1/9` the dilate `φ_T = φ(·/T)` of the reference bump has autocorrelation supported in
`[−4T, 4T] ⊂ (−log 2, log 2)`, so its Weil functional is independent of the weights: it is the
pole-plus-archimedean part of the translated test `φ_T(· − 2T)`, which is nonnegative and supported in
`(0, 4T)` with `4T ≤ 4/9`.  The unconditional window positivity of the corpus then gives
`W_lam(φ_T ⋆ φ̃_T) ≥ 0` for every weight `lam` and every `0 < T ≤ 1/9`
(`weilFullFunctional_dilate_nonneg_of_le_ninth`).  The ray inequality of the dilation-ray criterion
is therefore open only at scales `T > 1/9`, where the nodes `log 2, log 3, …` enter.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

noncomputable section

namespace RHTower.OddResolvent
open WeilOneSided

/-- The translated real dilate `φ((x − 2T)/T)`, supported in `(0, 4T)`. -/
def shiftedDilate (T x : ℝ) : ℝ := refProfile ((x - 2 * T) / T)

theorem shiftedDilate_nonneg (T x : ℝ) : 0 ≤ shiftedDilate T x := refProfile_nonneg _

theorem contDiff_shiftedDilate (T : ℝ) : ContDiff ℝ 2 (shiftedDilate T) :=
  contDiff_refProfile.comp ((contDiff_id.sub contDiff_const).div_const T)

theorem shiftedDilate_eq_zero {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : x ∉ Ioo 0 (4 * T)) :
    shiftedDilate T x = 0 := by
  unfold shiftedDilate
  apply refProfile_eq_zero
  rw [abs_div, abs_of_pos hT, le_div_iff₀ hT]
  rw [Set.mem_Ioo, not_and_or] at hx
  rcases hx with hx | hx
  · have := not_lt.mp hx
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have := not_lt.mp hx
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem hasCompactSupport_shiftedDilate {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (shiftedDilate T) :=
  HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 4 * T)) fun _ hx =>
    shiftedDilate_eq_zero hT fun h => hx ⟨h.1.le, h.2.le⟩

/-- Translation does not change the autocorrelation. -/
theorem weilTest_shiftedDilate (T : ℝ) :
    EF.weilTest (fun u => (shiftedDilate T u : ℂ)) (fun u => (shiftedDilate T u : ℂ)) =
      EF.weilTest (dilate T) (dilate T) := by
  have h := weilTest_comp_add_const (dilate T) (-(2 * T))
  refine Eq.trans ?_ h
  have e : (fun u => (shiftedDilate T u : ℂ)) = fun t => dilate T (t + -(2 * T)) := by
    funext u
    simp only [shiftedDilate, dilate]
    congr 2
  rw [e]

/-- The dilate vanishes outside `[−2T, 2T]`. -/
theorem dilate_eq_zero_of_lt {T : ℝ} (hT : 0 < T) {u : ℝ} (hu : 2 * T < |u|) : dilate T u = 0 := by
  simp only [dilate]
  rw [refProfile_eq_zero, Complex.ofReal_zero]
  rw [abs_div, abs_of_pos hT, le_div_iff₀ hT]
  linarith

/-- **At scales `T ≤ 1/9` every weight is positive on the dilate.** -/
theorem weilFullFunctional_dilate_nonneg_of_le_ninth (lam : ℕ → ℝ) {T : ℝ} (hT : 0 < T)
    (hT9 : T ≤ 1 / 9) :
    0 ≤ (weilFullFunctional lam (EF.weilTest (dilate T) (dilate T))).re := by
  set f : WeilTestFn := ⟨dilate T, contDiff_dilate T, hasCompactSupport_dilate hT⟩ with hf
  have hsplit := re_weilFullFunctional_eq lam f
  have hzero : logVector f = 0 := by
    ext j
    rw [logVector_apply, logValue]
    have hlog : 2 * (2 * T) < |Real.log (j : ℕ)| := by
      rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (le_trans one_le_two j.2)))]
      have h2 : Real.log 2 ≤ Real.log (j : ℕ) :=
        Real.log_le_log two_pos (by exact_mod_cast j.2)
      have := Real.log_two_gt_d9
      linarith
    have hlog' : 2 * (2 * T) < |-Real.log (j : ℕ)| := by rwa [abs_neg]
    rw [weilTest_self_eq_zero (fun u hu => dilate_eq_zero_of_lt hT hu) hlog,
      weilTest_self_eq_zero (fun u hu => dilate_eq_zero_of_lt hT hu) hlog', add_zero,
      Complex.zero_re, zero_div]
    simp
  rw [hsplit, hzero, map_zero, sub_zero]
  have hpos := WeilLevyHarmonicDoubling.weilArchRe_nonneg_of_support_Ioo_le_four_ninths
    (contDiff_shiftedDilate T) (hasCompactSupport_shiftedDilate hT) (shiftedDilate_nonneg T)
    (L := 4 * T) (by linarith) (fun u hu => shiftedDilate_eq_zero hT hu)
  rwa [weilTest_shiftedDilate] at hpos

end RHTower.OddResolvent
