import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedReflectionRigidity

/-!
# Retained defect grades of the Euler primitive boundary

The explicit head/tail source is a genuine direct grading.  Its singular odd Hodge map exchanges
the two grades, the four-unit score is a head vector, and the reflection fracture is the tail part
of the augmented source.  Thus the missing global theorem is preservation of these already-built
grades through source-native graph landing.
-/

namespace RHTower

noncomputable section

/-- Compact-head source grade. -/
def eulerPrimitiveBoundaryHeadGrade :
    Submodule ℂ EulerPrimitiveBoundaryPolarizedFeature where
  carrier := {x | x.2 = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change x.2 + y.2 = 0
    rw [hx, hy, zero_add]
  smul_mem' c x hx := by
    change c • x.2 = 0
    rw [hx, smul_zero]

/-- Escaping Hardy-tail source grade. -/
def eulerPrimitiveBoundaryTailGrade :
    Submodule ℂ EulerPrimitiveBoundaryPolarizedFeature where
  carrier := {x | x.1 = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change x.1 + y.1 = 0
    rw [hx, hy, zero_add]
  smul_mem' c x hx := by
    change c • x.1 = 0
    rw [hx, smul_zero]

/-- Head and tail retain disjoint defect information. -/
theorem eulerPrimitiveBoundaryHeadGrade_disjoint_tailGrade :
    Disjoint eulerPrimitiveBoundaryHeadGrade
      eulerPrimitiveBoundaryTailGrade := by
  rw [Submodule.disjoint_def]
  intro x hxHead hxTail
  change x.2 = 0 at hxHead
  change x.1 = 0 at hxTail
  apply Prod.ext
  · exact hxTail
  · exact hxHead

/-- Every polarized source vector splits into its head and tail grades. -/
theorem eulerPrimitiveBoundaryHeadGrade_sup_tailGrade :
    eulerPrimitiveBoundaryHeadGrade ⊔
        eulerPrimitiveBoundaryTailGrade = ⊤ := by
  apply top_unique
  intro x _hx
  have hHead : (x.1, 0) ∈ eulerPrimitiveBoundaryHeadGrade := rfl
  have hTail : (0, x.2) ∈ eulerPrimitiveBoundaryTailGrade := rfl
  have hsum := Submodule.add_mem
    (eulerPrimitiveBoundaryHeadGrade ⊔
      eulerPrimitiveBoundaryTailGrade)
    (Submodule.mem_sup_left hHead) (Submodule.mem_sup_right hTail)
  simpa using hsum

/-- The pole-centered four-unit score is retained in the compact-head grade. -/
theorem eulerPrimitiveBoundaryPolarizedScore_mem_headGrade :
    eulerPrimitiveBoundaryPolarizedScore ∈
      eulerPrimitiveBoundaryHeadGrade := by
  rfl

/-- The singular odd Hodge map sends head vectors to the tail grade. -/
theorem eulerPrimitiveBoundaryOddHodge_mem_tailGrade_of_mem_headGrade
    {x : EulerPrimitiveBoundaryPolarizedFeature}
    (hx : x ∈ eulerPrimitiveBoundaryHeadGrade) :
    eulerPrimitiveBoundaryOddHodge x ∈
      eulerPrimitiveBoundaryTailGrade := by
  change x.2 = 0 at hx
  change (eulerPrimitiveBoundaryOddHodge x).1 = 0
  funext t
  simp [eulerPrimitiveBoundaryOddHodge, hx]

/-- The singular odd Hodge map sends tail vectors to the head grade. -/
theorem eulerPrimitiveBoundaryOddHodge_mem_headGrade_of_mem_tailGrade
    {x : EulerPrimitiveBoundaryPolarizedFeature}
    (hx : x ∈ eulerPrimitiveBoundaryTailGrade) :
    eulerPrimitiveBoundaryOddHodge x ∈
      eulerPrimitiveBoundaryHeadGrade := by
  change x.1 = 0 at hx
  change (eulerPrimitiveBoundaryOddHodge x).2 = 0
  funext t
  simp [eulerPrimitiveBoundaryOddHodge, hx]

/-- The entire displacement-dependent part of the augmented source is retained in the tail
grade, separately from the four-unit head score. -/
theorem eulerPrimitiveBoundaryFractureAugmentedSource_sub_score_mem_tailGrade
    (a : ℝ) :
    eulerPrimitiveBoundaryFractureAugmentedSource a -
        eulerPrimitiveBoundaryPolarizedScore ∈
      eulerPrimitiveBoundaryTailGrade := by
  change
    eulerPrimitiveBoundaryPolarizedScore.1 -
      eulerPrimitiveBoundaryPolarizedScore.1 = 0
  exact sub_self _

end

end RHTower
