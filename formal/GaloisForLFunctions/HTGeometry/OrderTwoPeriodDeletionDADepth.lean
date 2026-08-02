import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTransverseDADepth
import GaloisForLFunctions.HTGeometry.OrderTwoPeriodDeletionPhaseSplit

/-!
# The order-two transverse differential-algebraic depth phase split

Two explicit order-two period frames

`τ_circuit = (i, √2 + i, √2 + 2i)`,  `τ_coloop = (i, 2i, √2 + i)`

have the same augmented rational period rank three, hence the same rank excess one.  Their
transverse differential-algebraic depths nevertheless differ: the circuit frame needs two distinct
structural differences to reach the differentially algebraic locus, while for the coloop frame the
single difference deleting the last period already suffices, because that deletion exposes the
commensurable pair `(i, 2i)`.

Total rational rank therefore does not determine transverse differential-algebraic depth; the
labelled rational deletion geometry does.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-! ## The two structural period triples -/

/-- Structural periods of the circuit frame: the full-support rational relation
`τ 2 = τ 0 + τ 1` holds. -/
def orderTwoCircuitPeriods : Fin 3 → ℂ :=
  ![Complex.I, (Real.sqrt 2 : ℂ) + Complex.I, (Real.sqrt 2 : ℂ) + 2 * Complex.I]

/-- Structural periods of the coloop frame: the first two are commensurable. -/
def orderTwoColoopPeriods : Fin 3 → ℂ :=
  ![Complex.I, 2 * Complex.I, (Real.sqrt 2 : ℂ) + Complex.I]

theorem orderTwoCircuitPeriods_im_pos (j : Fin 3) : 0 < (orderTwoCircuitPeriods j).im := by
  fin_cases j <;> simp [orderTwoCircuitPeriods] <;> norm_num

theorem orderTwoColoopPeriods_im_pos (j : Fin 3) : 0 < (orderTwoColoopPeriods j).im := by
  fin_cases j <;> simp [orderTwoColoopPeriods] <;> norm_num

/-- The structural triple sits inside the labelled four-entry frame. -/
theorem orderTwoCircuitPeriods_eq_frame (j : Fin 3) :
    orderTwoCircuitPeriods j = orderTwoCircuitPeriodFrame j.succ := by
  fin_cases j <;> simp [orderTwoCircuitPeriods, orderTwoCircuitPeriodFrame]

theorem orderTwoColoopPeriods_eq_frame (j : Fin 3) :
    orderTwoColoopPeriods j = orderTwoColoopPeriodFrame j.succ := by
  fin_cases j <;> simp [orderTwoColoopPeriods, orderTwoColoopPeriodFrame]

/-! ## Rational independence of the surviving pairs -/

/-- Swapping the two nonunit entries preserves rational independence. -/
theorem ellipticGammaSourcePeriods_linearIndependent_swap {a b : ℂ}
    (h : LinearIndependent ℚ (ellipticGammaSourcePeriods a b)) :
    LinearIndependent ℚ (ellipticGammaSourcePeriods b a) := by
  have hcomp := h.comp (Equiv.swap (1 : Fin 3) 2) (Equiv.injective _)
  have hfun : (ellipticGammaSourcePeriods a b) ∘ (Equiv.swap (1 : Fin 3) 2) =
      ellipticGammaSourcePeriods b a := by
    funext i
    fin_cases i <;>
      simp [ellipticGammaSourcePeriods, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
  rwa [hfun] at hcomp

theorem orderTwoCircuitPeriods_sourcePeriods_zero_one :
    ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 1) =
      orderTwoDeletionFace orderTwoCircuitPeriodFrame 2 := by
  funext i
  fin_cases i <;>
    simp [ellipticGammaSourcePeriods, orderTwoCircuitPeriods, orderTwoDeletionFace,
      orderTwoDeletePeriod, orderTwoCircuitPeriodFrame, Fin.le_def]

theorem orderTwoCircuitPeriods_sourcePeriods_zero_two :
    ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 2) =
      orderTwoDeletionFace orderTwoCircuitPeriodFrame 1 := by
  funext i
  fin_cases i <;>
    simp [ellipticGammaSourcePeriods, orderTwoCircuitPeriods, orderTwoDeletionFace,
      orderTwoDeletePeriod, orderTwoCircuitPeriodFrame, Fin.le_def]

theorem orderTwoCircuitPeriods_sourcePeriods_one_two :
    ellipticGammaSourcePeriods (orderTwoCircuitPeriods 1) (orderTwoCircuitPeriods 2) =
      orderTwoDeletionFace orderTwoCircuitPeriodFrame 0 := by
  funext i
  fin_cases i <;>
    simp [ellipticGammaSourcePeriods, orderTwoCircuitPeriods, orderTwoDeletionFace,
      orderTwoDeletePeriod, orderTwoCircuitPeriodFrame, Fin.le_def]

theorem orderTwoColoopPeriods_sourcePeriods_zero_one :
    ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 1) =
      orderTwoDeletionFace orderTwoColoopPeriodFrame 2 := by
  funext i
  fin_cases i <;>
    simp [ellipticGammaSourcePeriods, orderTwoColoopPeriods, orderTwoDeletionFace,
      orderTwoDeletePeriod, orderTwoColoopPeriodFrame, Fin.le_def]

theorem orderTwoColoopPeriods_sourcePeriods_zero_two :
    ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 2) =
      orderTwoDeletionFace orderTwoColoopPeriodFrame 1 := by
  funext i
  fin_cases i <;>
    simp [ellipticGammaSourcePeriods, orderTwoColoopPeriods, orderTwoDeletionFace,
      orderTwoDeletePeriod, orderTwoColoopPeriodFrame, Fin.le_def]

theorem orderTwoColoopPeriods_sourcePeriods_one_two :
    ellipticGammaSourcePeriods (orderTwoColoopPeriods 1) (orderTwoColoopPeriods 2) =
      orderTwoDeletionFace orderTwoColoopPeriodFrame 0 := by
  funext i
  fin_cases i <;>
    simp [ellipticGammaSourcePeriods, orderTwoColoopPeriods, orderTwoDeletionFace,
      orderTwoDeletePeriod, orderTwoColoopPeriodFrame, Fin.le_def]

/-- **Circuit frame: every surviving pair is rationally independent with the unit period.** -/
theorem orderTwoCircuitPeriods_pair_linearIndependent (q r : Fin 3) (hqr : q ≠ r) :
    LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods q) (orderTwoCircuitPeriods r)) := by
  have h01 : LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 1)) := by
    rw [orderTwoCircuitPeriods_sourcePeriods_zero_one]
    exact orderTwoCircuitDeletion_linearIndependent 2
  have h02 : LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 2)) := by
    rw [orderTwoCircuitPeriods_sourcePeriods_zero_two]
    exact orderTwoCircuitDeletion_linearIndependent 1
  have h12 : LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods 1) (orderTwoCircuitPeriods 2)) := by
    rw [orderTwoCircuitPeriods_sourcePeriods_one_two]
    exact orderTwoCircuitDeletion_linearIndependent 0
  fin_cases q <;> fin_cases r <;> first
    | exact absurd rfl hqr
    | exact h01
    | exact h02
    | exact h12
    | exact ellipticGammaSourcePeriods_linearIndependent_swap h01
    | exact ellipticGammaSourcePeriods_linearIndependent_swap h02
    | exact ellipticGammaSourcePeriods_linearIndependent_swap h12

/-- The coloop frame's exceptional pair `(i, 2i)` is rationally dependent with `1`. -/
theorem orderTwoColoopPeriods_zero_one_not_linearIndependent :
    ¬ LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 1)) := by
  rw [orderTwoColoopPeriods_sourcePeriods_zero_one]
  exact orderTwoColoopDeleteTwo_not_linearIndependent

theorem orderTwoColoopPeriods_one_zero_not_linearIndependent :
    ¬ LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods 1) (orderTwoColoopPeriods 0)) := by
  intro h
  exact orderTwoColoopPeriods_zero_one_not_linearIndependent
    (ellipticGammaSourcePeriods_linearIndependent_swap h)

theorem orderTwoColoopPeriods_zero_two_linearIndependent :
    LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 2)) := by
  rw [orderTwoColoopPeriods_sourcePeriods_zero_two]
  exact orderTwoColoopDeleteOne_linearIndependent

theorem orderTwoColoopPeriods_one_two_linearIndependent :
    LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods 1) (orderTwoColoopPeriods 2)) := by
  rw [orderTwoColoopPeriods_sourcePeriods_one_two]
  exact orderTwoColoopDeleteZero_linearIndependent

/-! ## Counting survivors of a labelled deletion -/

theorem exists_two_survivors_of_card_lt_two {J : Finset (Fin 3)} (hJ : J.card < 2) :
    ∃ q r : Fin 3, q ∉ J ∧ r ∉ J ∧ q ≠ r := by
  have hcompl : Jᶜ.card = 3 - J.card := by
    simpa using Finset.card_compl J
  have hlt : 1 < Jᶜ.card := by omega
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp hlt
  exact ⟨q, r, Finset.mem_compl.mp hq, Finset.mem_compl.mp hr, hqr⟩

/-! ## The two depths -/

/-- Deleting the two labels `{0, 1}` from the circuit frame leaves the single surviving period
`√2 + 2i`, and a one-period family is differentially algebraic. -/
theorem orderTwoCircuit_face_zero_one_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero orderTwoCircuitPeriods
        orderTwoCircuitPeriods_im_pos {0, 1}) := by
  refine differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_unique_survivor
    orderTwoCircuitPeriods orderTwoCircuitPeriods_im_pos {0, 1} (q := 2) (by decide) ?_
  decide

/-- No deletion of fewer than two circuit-frame labels is differentially algebraic: two of its
periods always remain rationally independent with `1`. -/
theorem orderTwoCircuit_face_not_differentialAlgebraic_of_card_lt_two
    (J : Finset (Fin 3)) (hJ : J.card < 2) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero orderTwoCircuitPeriods
        orderTwoCircuitPeriods_im_pos J) := by
  obtain ⟨q, r, hq, hr, hqr⟩ := exists_two_survivors_of_card_lt_two hJ
  exact not_differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_independentPair
    orderTwoCircuitPeriods orderTwoCircuitPeriods_im_pos J hq hr hqr
    (orderTwoCircuitPeriods_pair_linearIndependent q r hqr)

/-- **Circuit-frame depth two.** -/
theorem orderTwoCircuit_transverseDADepth :
    multipleEllipticGammaTransverseDADepth orderTwoCircuitPeriods
      orderTwoCircuitPeriods_im_pos = 2 := by
  refine multipleEllipticGammaTransverseDADepth_eq_of_min _ _ 2
    ⟨{0, 1}, by decide, orderTwoCircuit_face_zero_one_differentialAlgebraic⟩ ?_
  intro J hJ
  exact orderTwoCircuit_face_not_differentialAlgebraic_of_card_lt_two J hJ

/-- Deleting the single label `2` from the coloop frame exposes the commensurable pair
`(i, 2i)`, which is differentially algebraic. -/
theorem orderTwoColoop_face_two_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero orderTwoColoopPeriods
        orderTwoColoopPeriods_im_pos {2}) := by
  refine differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_no_independentPair
    orderTwoColoopPeriods orderTwoColoopPeriods_im_pos {2} (q₀ := 0) (by decide) ?_
  intro q r hq hr hqr
  have hq' : q = 0 ∨ q = 1 := by fin_cases q <;> simp_all <;> revert hq <;> decide
  have hr' : r = 0 ∨ r = 1 := by fin_cases r <;> simp_all <;> revert hr <;> decide
  rcases hq' with rfl | rfl <;> rcases hr' with rfl | rfl
  · exact absurd rfl hqr
  · exact orderTwoColoopPeriods_zero_one_not_linearIndependent
  · exact orderTwoColoopPeriods_one_zero_not_linearIndependent
  · exact absurd rfl hqr

/-- The undeleted coloop source is not differentially algebraic: the pair `(i, √2 + i)` survives. -/
theorem orderTwoColoop_face_empty_not_differentialAlgebraic :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero orderTwoColoopPeriods
        orderTwoColoopPeriods_im_pos ∅) :=
  not_differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_independentPair
    orderTwoColoopPeriods orderTwoColoopPeriods_im_pos ∅ (q := 0) (r := 2)
    (by decide) (by decide) (by decide)
    orderTwoColoopPeriods_zero_two_linearIndependent

/-- **Coloop-frame depth one.** -/
theorem orderTwoColoop_transverseDADepth :
    multipleEllipticGammaTransverseDADepth orderTwoColoopPeriods
      orderTwoColoopPeriods_im_pos = 1 := by
  refine multipleEllipticGammaTransverseDADepth_eq_of_min _ _ 1
    ⟨{2}, by decide, orderTwoColoop_face_two_differentialAlgebraic⟩ ?_
  intro J hJ
  have hJempty : J = ∅ := Finset.card_eq_zero.mp (by omega)
  subst hJempty
  exact orderTwoColoop_face_empty_not_differentialAlgebraic

/-! ## Equal rank, distinct depth -/

theorem orderTwoCircuitPeriods_augmented_span :
    insert (1 : ℂ) (Set.range orderTwoCircuitPeriods) =
      Set.range orderTwoCircuitPeriodFrame := by
  apply Set.Subset.antisymm
  · rintro x (rfl | ⟨j, rfl⟩)
    · exact ⟨0, by simp [orderTwoCircuitPeriodFrame]⟩
    · exact ⟨j.succ, (orderTwoCircuitPeriods_eq_frame j).symm⟩
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert_iff.mpr (Or.inl (by simp [orderTwoCircuitPeriodFrame]))
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨0, by
        simp [orderTwoCircuitPeriods, orderTwoCircuitPeriodFrame]⟩)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨1, by
        simp [orderTwoCircuitPeriods, orderTwoCircuitPeriodFrame]⟩)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨2, by
        simp [orderTwoCircuitPeriods, orderTwoCircuitPeriodFrame]⟩)

theorem orderTwoColoopPeriods_augmented_span :
    insert (1 : ℂ) (Set.range orderTwoColoopPeriods) =
      Set.range orderTwoColoopPeriodFrame := by
  apply Set.Subset.antisymm
  · rintro x (rfl | ⟨j, rfl⟩)
    · exact ⟨0, by simp [orderTwoColoopPeriodFrame]⟩
    · exact ⟨j.succ, (orderTwoColoopPeriods_eq_frame j).symm⟩
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert_iff.mpr (Or.inl (by simp [orderTwoColoopPeriodFrame]))
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨0, by
        simp [orderTwoColoopPeriods, orderTwoColoopPeriodFrame]⟩)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨1, by
        simp [orderTwoColoopPeriods, orderTwoColoopPeriodFrame]⟩)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨2, by
        simp [orderTwoColoopPeriods, orderTwoColoopPeriodFrame]⟩)

/-- Both structural triples have augmented rational period rank three. -/
theorem orderTwoCircuitPeriods_augmentedPeriodRank :
    multipleEllipticGammaAugmentedPeriodRank orderTwoCircuitPeriods = 3 := by
  rw [multipleEllipticGammaAugmentedPeriodRank, orderTwoCircuitPeriods_augmented_span]
  exact orderTwoCircuitPeriodFrame_rationalPeriodRank

theorem orderTwoColoopPeriods_augmentedPeriodRank :
    multipleEllipticGammaAugmentedPeriodRank orderTwoColoopPeriods = 3 := by
  rw [multipleEllipticGammaAugmentedPeriodRank, orderTwoColoopPeriods_augmented_span]
  exact orderTwoColoopPeriodFrame_rationalPeriodRank

/-- **Order-two period-deletion phase split.**  Two order-two multiple elliptic gamma sources with
the same augmented rational period rank three — hence the same rank excess one — have distinct
transverse differential-algebraic depths, two and one.  Total rational rank does not determine the
depth. -/
theorem orderTwo_equalRank_distinct_transverseDADepth :
    multipleEllipticGammaAugmentedPeriodRank orderTwoCircuitPeriods =
        multipleEllipticGammaAugmentedPeriodRank orderTwoColoopPeriods ∧
      multipleEllipticGammaTransverseDADepth orderTwoCircuitPeriods
          orderTwoCircuitPeriods_im_pos = 2 ∧
      multipleEllipticGammaTransverseDADepth orderTwoColoopPeriods
          orderTwoColoopPeriods_im_pos = 1 ∧
      multipleEllipticGammaTransverseDADepth orderTwoCircuitPeriods
          orderTwoCircuitPeriods_im_pos ≠
        multipleEllipticGammaTransverseDADepth orderTwoColoopPeriods
          orderTwoColoopPeriods_im_pos :=
  ⟨orderTwoCircuitPeriods_augmentedPeriodRank.trans
      orderTwoColoopPeriods_augmentedPeriodRank.symm,
    orderTwoCircuit_transverseDADepth,
    orderTwoColoop_transverseDADepth,
    by rw [orderTwoCircuit_transverseDADepth, orderTwoColoop_transverseDADepth]; decide⟩

end

end GaloisForLFunctions.HTGeometry
