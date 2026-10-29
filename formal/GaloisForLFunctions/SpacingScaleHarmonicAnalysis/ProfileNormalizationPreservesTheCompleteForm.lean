import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRobinConstantOfAnAtom
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.OverlapCoordinates

/-!
# Profile support normalization preserves the complete form

Changing a profile supported in `[a,b]` to a profile on `[0,1]` multiplies
the atom width by `b-a` and translates every atom by the same amount.
The complete Weil form and actual squared mass are translation invariant.
Thus overlap and inverse-width height retain the profile-span convention.
-/

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight

open ArithmeticElectrostatics

/-- Affine reparametrization of a profile's enclosing support interval. -/
def unitIntervalProfile (φ : ℝ → ℝ) (a b : ℝ) (u : ℝ) : ℝ :=
  φ (a + (b - a) * u)

theorem unitIntervalProfile_eq_zero_outside {φ : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc a b → φ u = 0) (hab : a < b) {u : ℝ}
    (hu : u ∉ Set.Icc 0 1) : unitIntervalProfile φ a b u = 0 := by
  apply hsupp
  intro h
  have hd : 0 < b - a := sub_pos.mpr hab
  have hlo : 0 ≤ u := by nlinarith only [h.1, hd]
  have hhi : u ≤ 1 := by nlinarith only [h.2, hd]
  exact hu ⟨hlo, hhi⟩

/-- An atom is a common translate of the normalized-profile atom at the rescaled width. -/
theorem atomDilate_profile_normalization (φ : ℝ → ℝ) {a b w : ℝ}
    (hab : a < b) (hw : 0 < w) :
    atomDilate φ w = fun u =>
      atomDilate (unitIntervalProfile φ a b) ((b - a) * w) (u - a * w) := by
  funext u
  dsimp only [atomDilate, unitIntervalProfile]
  congr 1
  field_simp [(sub_pos.mpr hab).ne', hw.ne'] <;> ring

/-- All logarithmic atoms undergo the same translation, so every coefficient vector is retained. -/
theorem atomicTest_profile_normalization (φ : ℝ → ℝ) {a b w : ℝ}
    (hab : a < b) (hw : 0 < w) (N : ℕ) (x : ℕ → ℝ) :
    atomicTest N x (atomDilate φ w) = fun u =>
      atomicTest N x (atomDilate (unitIntervalProfile φ a b) ((b - a) * w)) (u - a * w) := by
  funext u
  change (∑ n ∈ Icc 1 N, x n * atomDilate φ w (u - Real.log n)) = _
  rw [atomDilate_profile_normalization φ hab hw]
  apply sum_congr rfl
  intro n hn
  congr 2
  ring

/-- Profile support normalization preserves the full Weil value, including its polar part. -/
theorem weilQuad_atomicTest_profile_normalization (φ : ℝ → ℝ) {a b w : ℝ}
    (hab : a < b) (hw : 0 < w) (N : ℕ) (x : ℕ → ℝ) :
    weilQuad (atomicTest N x (atomDilate φ w)) =
      weilQuad (atomicTest N x (atomDilate (unitIntervalProfile φ a b) ((b - a) * w))) := by
  rw [atomicTest_profile_normalization φ hab hw N x, weilQuad_comp_sub]

/-- Actual synthesized squared mass is preserved by the same normalization. -/
theorem integral_atomicTest_sq_profile_normalization (φ : ℝ → ℝ) {a b w : ℝ}
    (hab : a < b) (hw : 0 < w) (N : ℕ) (x : ℕ → ℝ) :
    (∫ u, atomicTest N x (atomDilate φ w) u ^ 2) =
      ∫ u, atomicTest N x
        (atomDilate (unitIntervalProfile φ a b) ((b - a) * w)) u ^ 2 := by
  rw [atomicTest_profile_normalization φ hab hw N x]
  exact integral_sub_right_eq_self _ _

/-- One atom's mass is preserved, hence so is normalization by coefficient mass. -/
theorem integral_atomDilate_sq_profile_normalization (φ : ℝ → ℝ) {a b w : ℝ}
    (hab : a < b) (hw : 0 < w) :
    (∫ u, atomDilate φ w u ^ 2) =
      ∫ u, atomDilate (unitIntervalProfile φ a b) ((b - a) * w) u ^ 2 := by
  rw [atomDilate_profile_normalization φ hab hw]
  exact integral_sub_right_eq_self _ _

/-- The atom-mass-normalized complete quadratic form is independent of profile support coordinates. -/
theorem normalized_weilQuad_profile_normalization (φ : ℝ → ℝ) {a b w : ℝ}
    (hab : a < b) (hw : 0 < w) (N : ℕ) (x : ℕ → ℝ) :
    weilQuad (atomicTest N x (atomDilate φ w)) / (∫ u, atomDilate φ w u ^ 2) =
      weilQuad (atomicTest N x (atomDilate (unitIntervalProfile φ a b) ((b - a) * w))) /
        (∫ u, atomDilate (unitIntervalProfile φ a b) ((b - a) * w) u ^ 2) := by
  rw [weilQuad_atomicTest_profile_normalization φ hab hw N x,
    integral_atomDilate_sq_profile_normalization φ hab hw]

/-- Fixing unit profile span multiplies overlap by the original span and divides height by it. -/
theorem height_profile_normalization (X c a b : ℝ) :
    height X ((b - a) * c) = height X c / (b - a) := by
  unfold height
  rw [div_div, mul_comm]

/-- A symmetric profile at overlap `c` has exactly the same complete value as its unit-interval
reparametrization at overlap `2c`. -/
theorem weilQuad_symmetric_profile_overlap (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    weilQuad (atomicTest N x (atomDilate φ (c / N))) =
      weilQuad (atomicTest N x (atomDilate (unitIntervalProfile φ (-1) 1) (2 * c / N))) := by
  have h := weilQuad_atomicTest_profile_normalization φ (by norm_num : (-1 : ℝ) < 1)
    (div_pos hc (show (0 : ℝ) < N by exact_mod_cast hN)) N x
  simpa only [show ((1 : ℝ) - -1) * (c / N) = 2 * c / N by ring] using h

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.atomicTest_profile_normalization
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.normalized_weilQuad_profile_normalization
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.weilQuad_symmetric_profile_overlap
