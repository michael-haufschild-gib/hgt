import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Order-two rational period-deletion phase split

This module formalizes the unconditional labelled-period geometry behind the order-two
multiple-elliptic-gamma phase split.  Two explicit four-entry frames have the same rational rank
three.  Deleting any structural period from the circuit frame preserves rank three, whereas
deleting the distinguished third period from the coloop frame drops the rank to two.

The result is a genuine nonproduct law: total rational rank does not determine the labelled
deletion profile.  The analytic identification of this profile with transverse differential-
algebraic depth still requires the exact non-rational order-one elliptic-gamma theorem.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The common rationally independent rank-three core of both explicit frames. -/
def orderTwoIrrationalPeriodTriple : Fin 3 → ℂ :=
  ![1, Complex.I, (Real.sqrt 2 : ℂ) + Complex.I]

theorem orderTwoIrrationalPeriodTriple_linearIndependent :
    LinearIndependent ℚ orderTwoIrrationalPeriodTriple := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp [Fin.sum_univ_succ, orderTwoIrrationalPeriodTriple] at hre him
  change (g 0 : ℝ) + (g 2 : ℝ) * Real.sqrt 2 = 0 at hre
  have hg2 : g 2 = 0 := by
    by_contra hg2
    apply irrational_sqrt_two.ne_rat (-(g 0) / g 2)
    have hg2r : ((g 2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hg2
    push_cast
    apply (eq_div_iff hg2r).2
    linarith
  have hg0 : g 0 = 0 := by
    rw [hg2] at hre
    simpa using hre
  have hg1 : g 1 = 0 := by
    rw [hg2] at him
    simpa using him
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- Irrationality of `sqrt 2` kills every two-term rational relation with `1`. -/
theorem rational_sqrtTwo_relation (a b : ℚ)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply irrational_sqrt_two.ne_rat (-a / b)
    have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast
    apply (eq_div_iff hbr).2
    linarith
  constructor
  · rw [hb] at h
    simpa using h
  · exact hb

/-- The full-support circuit frame `(1, i, sqrt 2 + i, sqrt 2 + 2i)`. -/
def orderTwoCircuitPeriodFrame : Fin 4 → ℂ :=
  ![1, Complex.I, (Real.sqrt 2 : ℂ) + Complex.I,
    (Real.sqrt 2 : ℂ) + 2 * Complex.I]

/-- The coloop frame `(1, i, 2i, sqrt 2 + i)`. -/
def orderTwoColoopPeriodFrame : Fin 4 → ℂ :=
  ![1, Complex.I, 2 * Complex.I, (Real.sqrt 2 : ℂ) + Complex.I]

/-- The order-preserving inclusion which deletes structural period `j`, whose frame index is
`j + 1`, while retaining the distinguished constant period at index zero. -/
def orderTwoDeletePeriod (j : Fin 3) : Fin 3 → Fin 4 := fun k =>
  if k ≤ j then ⟨k, by omega⟩ else ⟨k + 1, by omega⟩

/-- The residual three-entry period face after deleting structural period `j`. -/
def orderTwoDeletionFace (v : Fin 4 → ℂ) (j : Fin 3) : Fin 3 → ℂ :=
  fun k => v (orderTwoDeletePeriod j k)

/-- The circuit frame has its unique displayed full-support rational relation. -/
theorem orderTwoCircuitPeriodFrame_relation :
    orderTwoCircuitPeriodFrame 3 =
      orderTwoCircuitPeriodFrame 1 + orderTwoCircuitPeriodFrame 2 := by
  simp [orderTwoCircuitPeriodFrame]
  ring

/-- The coloop frame has the displayed two-entry rational relation. -/
theorem orderTwoColoopPeriodFrame_relation :
    orderTwoColoopPeriodFrame 2 = 2 * orderTwoColoopPeriodFrame 1 := by
  simp [orderTwoColoopPeriodFrame]

/-- Every labelled deletion of the circuit frame leaves a rationally independent triple. -/
theorem orderTwoCircuitDeletion_linearIndependent (j : Fin 3) :
    LinearIndependent ℚ (orderTwoDeletionFace orderTwoCircuitPeriodFrame j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  fin_cases j
  · simp [Fin.sum_univ_succ, orderTwoDeletionFace, orderTwoDeletePeriod,
      orderTwoCircuitPeriodFrame] at hre him
    simp only [Rat.smul_def] at hre him
    have hr : (g 0 : ℝ) + ((g 1 + g 2 : ℚ) : ℝ) * Real.sqrt 2 = 0 := by
      push_cast
      nlinarith [hre]
    obtain ⟨hg0, hgsum⟩ := rational_sqrtTwo_relation _ _ hr
    have hgsumr : (g 1 : ℝ) + (g 2 : ℝ) = 0 := by exact_mod_cast hgsum
    have hg1r : (g 1 : ℝ) = 0 := by linarith
    have hg2r : (g 2 : ℝ) = 0 := by linarith
    have hg1 : g 1 = 0 := by exact_mod_cast hg1r
    have hg2 : g 2 = 0 := by exact_mod_cast hg2r
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  · simp [Fin.sum_univ_succ, orderTwoDeletionFace, orderTwoDeletePeriod,
      orderTwoCircuitPeriodFrame] at hre him
    simp only [Rat.smul_def] at hre him
    have hr : (g 0 : ℝ) + (g 2 : ℝ) * Real.sqrt 2 = 0 := by
      nlinarith [hre]
    obtain ⟨hg0, hg2⟩ := rational_sqrtTwo_relation _ _ hr
    have hg2r : (g 2 : ℝ) = 0 := by exact_mod_cast hg2
    have hg1r : (g 1 : ℝ) = 0 := by linarith
    have hg1 : g 1 = 0 := by exact_mod_cast hg1r
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  · simp [Fin.sum_univ_succ, orderTwoDeletionFace, orderTwoDeletePeriod,
      orderTwoCircuitPeriodFrame] at hre him
    simp only [Rat.smul_def] at hre him
    have hr : (g 0 : ℝ) + (g 2 : ℝ) * Real.sqrt 2 = 0 := by
      nlinarith [hre]
    obtain ⟨hg0, hg2⟩ := rational_sqrtTwo_relation _ _ hr
    have hi : g 1 + g 2 = 0 := by exact_mod_cast him
    have hg1 : g 1 = 0 := by linarith
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2

/-- Deleting the first structural period from the coloop frame leaves rank three. -/
theorem orderTwoColoopDeleteZero_linearIndependent :
    LinearIndependent ℚ (orderTwoDeletionFace orderTwoColoopPeriodFrame 0) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp [Fin.sum_univ_succ, orderTwoDeletionFace, orderTwoDeletePeriod,
    orderTwoColoopPeriodFrame] at hre him
  simp only [Rat.smul_def] at hre him
  have hr : (g 0 : ℝ) + (g 2 : ℝ) * Real.sqrt 2 = 0 := by
    nlinarith [hre]
  obtain ⟨hg0, hg2⟩ := rational_sqrtTwo_relation _ _ hr
  have hg2r : (g 2 : ℝ) = 0 := by exact_mod_cast hg2
  have hg1r : (g 1 : ℝ) = 0 := by linarith
  have hg1 : g 1 = 0 := by exact_mod_cast hg1r
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- Deleting the second structural period from the coloop frame leaves rank three. -/
theorem orderTwoColoopDeleteOne_linearIndependent :
    LinearIndependent ℚ (orderTwoDeletionFace orderTwoColoopPeriodFrame 1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp [Fin.sum_univ_succ, orderTwoDeletionFace, orderTwoDeletePeriod,
    orderTwoColoopPeriodFrame] at hre him
  simp only [Rat.smul_def] at hre him
  have hr : (g 0 : ℝ) + (g 2 : ℝ) * Real.sqrt 2 = 0 := by
    nlinarith [hre]
  obtain ⟨hg0, hg2⟩ := rational_sqrtTwo_relation _ _ hr
  have hi : g 1 + g 2 = 0 := by exact_mod_cast him
  have hg1 : g 1 = 0 := by linarith
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- Deleting the third structural period exposes the commensurable pair `(i, 2i)`. -/
theorem orderTwoColoopDeleteTwo_not_linearIndependent :
    ¬ LinearIndependent ℚ (orderTwoDeletionFace orderTwoColoopPeriodFrame 2) := by
  intro h
  rw [Fintype.linearIndependent_iff] at h
  let g : Fin 3 → ℚ := ![0, -2, 1]
  have hg : ∑ i, g i • orderTwoDeletionFace orderTwoColoopPeriodFrame 2 i = 0 := by
    simp [g, Fin.sum_univ_succ, orderTwoDeletionFace, orderTwoDeletePeriod,
      orderTwoColoopPeriodFrame, Rat.smul_def]
  have hzero := h g hg 2
  simp [g] at hzero

/-- Exact labelled independence profile of the coloop frame. -/
theorem orderTwoColoopDeletion_linearIndependent_iff (j : Fin 3) :
    LinearIndependent ℚ (orderTwoDeletionFace orderTwoColoopPeriodFrame j) ↔ j ≠ 2 := by
  fin_cases j
  · simp [orderTwoColoopDeleteZero_linearIndependent]
  · simp [orderTwoColoopDeleteOne_linearIndependent]
  · simp [orderTwoColoopDeleteTwo_not_linearIndependent]

/-- Rational dimension of the span of a finite labelled complex period frame. -/
def rationalPeriodRank {n : ℕ} (v : Fin n → ℂ) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ (Set.range v))

theorem span_orderTwoCircuitPeriodFrame_eq_irrationalPeriodTriple :
    Submodule.span ℚ (Set.range orderTwoCircuitPeriodFrame) =
      Submodule.span ℚ (Set.range orderTwoIrrationalPeriodTriple) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span
        ⟨0, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · exact Submodule.subset_span
        ⟨1, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · exact Submodule.subset_span
        ⟨2, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · change orderTwoCircuitPeriodFrame 3 ∈
        Submodule.span ℚ (Set.range orderTwoIrrationalPeriodTriple)
      rw [orderTwoCircuitPeriodFrame_relation]
      exact add_mem
        (Submodule.subset_span
          ⟨1, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩)
        (Submodule.subset_span
          ⟨2, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span
        ⟨0, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · exact Submodule.subset_span
        ⟨1, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · exact Submodule.subset_span
        ⟨2, by simp [orderTwoCircuitPeriodFrame, orderTwoIrrationalPeriodTriple]⟩

theorem span_orderTwoColoopPeriodFrame_eq_irrationalPeriodTriple :
    Submodule.span ℚ (Set.range orderTwoColoopPeriodFrame) =
      Submodule.span ℚ (Set.range orderTwoIrrationalPeriodTriple) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span
        ⟨0, by simp [orderTwoColoopPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · exact Submodule.subset_span
        ⟨1, by simp [orderTwoColoopPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · change orderTwoColoopPeriodFrame 2 ∈
        Submodule.span ℚ (Set.range orderTwoIrrationalPeriodTriple)
      rw [orderTwoColoopPeriodFrame_relation]
      exact Submodule.smul_mem _ (2 : ℚ)
        (Submodule.subset_span
          ⟨1, by simp [orderTwoColoopPeriodFrame, orderTwoIrrationalPeriodTriple]⟩)
    · exact Submodule.subset_span
        ⟨2, by simp [orderTwoColoopPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span
        ⟨0, by simp [orderTwoColoopPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · exact Submodule.subset_span
        ⟨1, by simp [orderTwoColoopPeriodFrame, orderTwoIrrationalPeriodTriple]⟩
    · exact Submodule.subset_span
        ⟨3, by simp [orderTwoColoopPeriodFrame, orderTwoIrrationalPeriodTriple]⟩

/-- The circuit frame has total rational period rank three. -/
theorem orderTwoCircuitPeriodFrame_rationalPeriodRank :
    rationalPeriodRank orderTwoCircuitPeriodFrame = 3 := by
  rw [rationalPeriodRank, span_orderTwoCircuitPeriodFrame_eq_irrationalPeriodTriple]
  simpa using finrank_span_eq_card orderTwoIrrationalPeriodTriple_linearIndependent

/-- The coloop frame also has total rational period rank three. -/
theorem orderTwoColoopPeriodFrame_rationalPeriodRank :
    rationalPeriodRank orderTwoColoopPeriodFrame = 3 := by
  rw [rationalPeriodRank, span_orderTwoColoopPeriodFrame_eq_irrationalPeriodTriple]
  simpa using finrank_span_eq_card orderTwoIrrationalPeriodTriple_linearIndependent

theorem rationalPeriodRank_eq_card_of_linearIndependent
    {n : ℕ} {v : Fin n → ℂ} (hv : LinearIndependent ℚ v) :
    rationalPeriodRank v = n := by
  unfold rationalPeriodRank
  simpa using finrank_span_eq_card hv

/-- Every circuit-frame deletion has rational rank three. -/
theorem orderTwoCircuitDeletion_rationalPeriodRank (j : Fin 3) :
    rationalPeriodRank (orderTwoDeletionFace orderTwoCircuitPeriodFrame j) = 3 :=
  rationalPeriodRank_eq_card_of_linearIndependent
    (orderTwoCircuitDeletion_linearIndependent j)

def standardPeriodPair : Fin 2 → ℂ := ![1, Complex.I]

theorem standardPeriodPair_linearIndependent :
    LinearIndependent ℚ standardPeriodPair := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp [Fin.sum_univ_succ, standardPeriodPair] at hre him
  intro i
  fin_cases i
  · exact hre
  · exact him

theorem span_orderTwoColoopDeleteTwo_eq_standardPeriodPair :
    Submodule.span ℚ
        (Set.range (orderTwoDeletionFace orderTwoColoopPeriodFrame 2)) =
      Submodule.span ℚ (Set.range standardPeriodPair) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨0, by
        simp [orderTwoDeletionFace, orderTwoDeletePeriod, orderTwoColoopPeriodFrame,
          standardPeriodPair]⟩
    · exact Submodule.subset_span ⟨1, by
        simp [orderTwoDeletionFace, orderTwoDeletePeriod, orderTwoColoopPeriodFrame,
          standardPeriodPair]⟩
    · exact Submodule.smul_mem _ (2 : ℚ)
        (Submodule.subset_span ⟨1, by
          simp [standardPeriodPair]⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨0, by
        simp [orderTwoDeletionFace, orderTwoDeletePeriod, orderTwoColoopPeriodFrame,
          standardPeriodPair]⟩
    · exact Submodule.subset_span ⟨1, by
        simp [orderTwoDeletionFace, orderTwoDeletePeriod, orderTwoColoopPeriodFrame,
          standardPeriodPair]⟩

/-- The exceptional coloop deletion has exact rational rank two. -/
theorem orderTwoColoopDeleteTwo_rationalPeriodRank :
    rationalPeriodRank (orderTwoDeletionFace orderTwoColoopPeriodFrame 2) = 2 := by
  rw [rationalPeriodRank, span_orderTwoColoopDeleteTwo_eq_standardPeriodPair]
  simpa using finrank_span_eq_card standardPeriodPair_linearIndependent

/-- Exact labelled deletion-rank profile of the coloop frame. -/
theorem orderTwoColoopDeletion_rationalPeriodRank (j : Fin 3) :
    rationalPeriodRank (orderTwoDeletionFace orderTwoColoopPeriodFrame j) =
      if j = 2 then 2 else 3 := by
  fin_cases j
  · simpa using rationalPeriodRank_eq_card_of_linearIndependent
      orderTwoColoopDeleteZero_linearIndependent
  · simpa using rationalPeriodRank_eq_card_of_linearIndependent
      orderTwoColoopDeleteOne_linearIndependent
  · simpa using orderTwoColoopDeleteTwo_rationalPeriodRank

/-- **Equal-total-rank, distinct-deletion-profile phase split.**  The two explicit frames have
the same total rational rank, but their complete labelled deletion-rank profiles differ. -/
theorem orderTwo_equal_totalRank_distinct_labelledDeletionProfile :
    rationalPeriodRank orderTwoCircuitPeriodFrame =
        rationalPeriodRank orderTwoColoopPeriodFrame ∧
      (∀ j, rationalPeriodRank
        (orderTwoDeletionFace orderTwoCircuitPeriodFrame j) = 3) ∧
      (∀ j, rationalPeriodRank
        (orderTwoDeletionFace orderTwoColoopPeriodFrame j) =
          if j = 2 then 2 else 3) := by
  exact ⟨orderTwoCircuitPeriodFrame_rationalPeriodRank.trans
      orderTwoColoopPeriodFrame_rationalPeriodRank.symm,
    orderTwoCircuitDeletion_rationalPeriodRank,
    orderTwoColoopDeletion_rationalPeriodRank⟩

end

end GaloisForLFunctions.HTGeometry
