import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedThreePointLocalizationLaw
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedTwoNodeStrictLaw

/-!
# Pairwise-strict ternary localization for the theta-cusp packet

The two-node theta-cusp problem is strictly positive at every nonzero displacement, whereas every
possible three-node failure is localized to one bounded middle shell.  Hence failure cannot be
detected on any pairwise sector: it is exactly a negative cubic determinant of the full ternary
packet, confined away from both coalescence and infinity.
-/

namespace RHTower

noncomputable section

/-- A failure certificate which records both bounded localization and the strict positivity of all
three pairwise gaps of the same ordered three-node packet. -/
def ThetaCuspPairwiseStrictTernaryLocalizationCertificate (a : ℝ) : Prop :=
  ∃ coalescenceRadius outerCutoff : ℝ,
    0 < coalescenceRadius ∧
    coalescenceRadius ≤ outerCutoff ∧
    (∀ x y : ℝ,
      0 < x → x < coalescenceRadius → 0 < y → y < coalescenceRadius →
        Matrix.PosDef (thetaCuspCenterMixedThreePointMatrix a x y)) ∧
    (∀ x y : ℝ,
      0 < x → 0 < y → outerCutoff ≤ x ∨ outerCutoff ≤ y →
        Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)) ∧
    (∀ x y : ℝ,
      0 < x → 0 < y →
        ¬ Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) →
          (coalescenceRadius ≤ x ∨ coalescenceRadius ≤ y) ∧
          x < outerCutoff ∧ y < outerCutoff ∧
          Matrix.PosDef (thetaCuspCenterMixedTwoNodeMatrix a x) ∧
          Matrix.PosDef (thetaCuspCenterMixedTwoNodeMatrix a y) ∧
          Matrix.PosDef (thetaCuspCenterMixedTwoNodeMatrix a (x + y)) ∧
          thetaCuspCenterMixedThreePointDeterminant a x y < 0) ∧
    ((∀ x y : ℝ, 0 < x → 0 < y →
          Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)) ↔
      (∀ x y : ℝ, 0 < x → 0 < y →
        coalescenceRadius ≤ x ∨ coalescenceRadius ≤ y →
        x < outerCutoff → y < outerCutoff →
          Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)))

/-- **Pairwise-strict ternary localization law.**  Every possible failure of the center-mixed
theta three-point problem is a bounded, genuinely ternary determinant obstruction: all three
two-node sectors of that same packet remain positive definite. -/
theorem thetaCusp_pairwiseStrict_ternaryLocalizationUniversality
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ThetaCuspPairwiseStrictTernaryLocalizationCertificate a := by
  obtain ⟨delta, Y, hdelta, hdeltaY, hnear, hfar, hfailure, hlocal⟩ :=
    thetaCuspCenterMixedThreePoint_localizationLaw ha0 ha
  refine ⟨delta, Y, hdelta, hdeltaY, hnear, hfar, ?_, hlocal⟩
  intro x y hx hy hnot
  obtain ⟨hinner, hxY, hyY⟩ := hfailure x y hx hy hnot
  have hxy : 0 < x + y := add_pos hx hy
  have hdet : thetaCuspCenterMixedThreePointDeterminant a x y < 0 := by
    rw [← not_le]
    intro hnonneg
    exact hnot ((thetaCuspCenterMixedThreePointMatrix_posSemidef_iff ha0 ha hx).2 hnonneg)
  exact ⟨hinner, hxY, hyY,
    thetaCuspCenterMixedTwoNodeMatrix_posDef ha0 ha hx.ne',
    thetaCuspCenterMixedTwoNodeMatrix_posDef ha0 ha hy.ne',
    thetaCuspCenterMixedTwoNodeMatrix_posDef ha0 ha hxy.ne', hdet⟩

end

end RHTower
