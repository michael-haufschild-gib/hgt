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

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-! ## The two structural period triples -/

/-- Structural periods of the circuit frame: the full-support rational relation
`τ 2 = τ 0 + τ 1` holds. -/
def orderTwoCircuitPeriods : Fin 3 → ℂ :=
  ![Complex.I, (Real.sqrt 2 : ℂ) + Complex.I, (Real.sqrt 2 : ℂ) + 2 * Complex.I]

/-- Structural periods of the coloop frame: the first two are commensurable. -/
def orderTwoColoopPeriods : Fin 3 → ℂ :=
  ![Complex.I, 2 * Complex.I, (Real.sqrt 2 : ℂ) + Complex.I]

theorem orderTwoCircuitPeriods_im_pos (j : Fin 3) : 0 < (orderTwoCircuitPeriods j).im := by
  fin_cases j <;> simp [orderTwoCircuitPeriods]

theorem orderTwoColoopPeriods_im_pos (j : Fin 3) : 0 < (orderTwoColoopPeriods j).im := by
  fin_cases j <;> simp [orderTwoColoopPeriods]

/-- The structural triple is the labelled four-entry frame with its unit period removed. -/
theorem orderTwoCircuitPeriods_eq_frame (j : Fin 3) :
    orderTwoCircuitPeriods j = orderTwoCircuitPeriodFrame j.succ := by
  fin_cases j <;> rfl

theorem orderTwoColoopPeriods_eq_frame (j : Fin 3) :
    orderTwoColoopPeriods j = orderTwoColoopPeriodFrame j.succ := by
  fin_cases j <;> rfl

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

/-- Each labelled deletion of a four-entry frame is the source-period triple of its two surviving
structural labels; all six identifications are definitional. -/
theorem orderTwoCircuitPeriods_sourcePeriods_zero_one :
    ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 1) =
      orderTwoDeletionFace orderTwoCircuitPeriodFrame 2 := by
  funext i; fin_cases i <;> rfl

theorem orderTwoCircuitPeriods_sourcePeriods_zero_two :
    ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 2) =
      orderTwoDeletionFace orderTwoCircuitPeriodFrame 1 := by
  funext i; fin_cases i <;> rfl

theorem orderTwoCircuitPeriods_sourcePeriods_one_two :
    ellipticGammaSourcePeriods (orderTwoCircuitPeriods 1) (orderTwoCircuitPeriods 2) =
      orderTwoDeletionFace orderTwoCircuitPeriodFrame 0 := by
  funext i; fin_cases i <;> rfl

theorem orderTwoColoopPeriods_sourcePeriods_zero_one :
    ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 1) =
      orderTwoDeletionFace orderTwoColoopPeriodFrame 2 := by
  funext i; fin_cases i <;> rfl

theorem orderTwoColoopPeriods_sourcePeriods_zero_two :
    ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 2) =
      orderTwoDeletionFace orderTwoColoopPeriodFrame 1 := by
  funext i; fin_cases i <;> rfl

theorem orderTwoColoopPeriods_sourcePeriods_one_two :
    ellipticGammaSourcePeriods (orderTwoColoopPeriods 1) (orderTwoColoopPeriods 2) =
      orderTwoDeletionFace orderTwoColoopPeriodFrame 0 := by
  funext i; fin_cases i <;> rfl

/-- **Circuit frame: every surviving pair is rationally independent with the unit period.** -/
theorem orderTwoCircuitPeriods_pair_linearIndependent (q r : Fin 3) (hqr : q ≠ r) :
    LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods q) (orderTwoCircuitPeriods r)) := by
  have h01 : LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 1)) :=
    orderTwoCircuitPeriods_sourcePeriods_zero_one ▸ orderTwoCircuitDeletion_linearIndependent 2
  have h02 : LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods 0) (orderTwoCircuitPeriods 2)) :=
    orderTwoCircuitPeriods_sourcePeriods_zero_two ▸ orderTwoCircuitDeletion_linearIndependent 1
  have h12 : LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoCircuitPeriods 1) (orderTwoCircuitPeriods 2)) :=
    orderTwoCircuitPeriods_sourcePeriods_one_two ▸ orderTwoCircuitDeletion_linearIndependent 0
  fin_cases q <;> fin_cases r <;> first
    | exact absurd rfl hqr
    | exact h01
    | exact h02
    | exact h12
    | exact ellipticGammaSourcePeriods_linearIndependent_swap h01
    | exact ellipticGammaSourcePeriods_linearIndependent_swap h02
    | exact ellipticGammaSourcePeriods_linearIndependent_swap h12

/-- **Coloop frame: no surviving pair of the face deleting the last label is rationally
independent with `1`.** -/
theorem orderTwoColoopPeriods_commensurable_pair_not_linearIndependent
    {q r : Fin 3} (hq : q ≠ 2) (hr : r ≠ 2) (hqr : q ≠ r) :
    ¬ LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods q) (orderTwoColoopPeriods r)) := by
  have h01 : ¬ LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 1)) :=
    orderTwoColoopPeriods_sourcePeriods_zero_one ▸
      orderTwoColoopDeleteTwo_not_linearIndependent
  fin_cases q <;> fin_cases r <;> first
    | exact absurd rfl hq
    | exact absurd rfl hr
    | exact absurd rfl hqr
    | exact h01
    | exact fun h => h01 (ellipticGammaSourcePeriods_linearIndependent_swap h)

theorem orderTwoColoopPeriods_zero_two_linearIndependent :
    LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods 0) (orderTwoColoopPeriods 2)) :=
  orderTwoColoopPeriods_sourcePeriods_zero_two ▸ orderTwoColoopDeleteOne_linearIndependent

theorem orderTwoColoopPeriods_one_two_linearIndependent :
    LinearIndependent ℚ
      (ellipticGammaSourcePeriods (orderTwoColoopPeriods 1) (orderTwoColoopPeriods 2)) :=
  orderTwoColoopPeriods_sourcePeriods_one_two ▸ orderTwoColoopDeleteZero_linearIndependent

/-! ## Counting survivors of a labelled deletion -/

theorem exists_two_survivors_of_card_lt_two {J : Finset (Fin 3)} (hJ : J.card < 2) :
    ∃ q r : Fin 3, q ∉ J ∧ r ∉ J ∧ q ≠ r := by
  have hcompl : Jᶜ.card = 3 - J.card := by simpa using Finset.card_compl J
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp (show 1 < Jᶜ.card by omega)
  exact ⟨q, r, Finset.mem_compl.mp hq, Finset.mem_compl.mp hr, hqr⟩

/-! ## The two depths -/

/-- Deleting the two labels `{0, 1}` from the circuit frame leaves the single surviving period
`√2 + 2i`, and a one-period family is differentially algebraic. -/
theorem orderTwoCircuit_face_zero_one_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero orderTwoCircuitPeriods
        orderTwoCircuitPeriods_im_pos {0, 1}) :=
  differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_unique_survivor
    orderTwoCircuitPeriods orderTwoCircuitPeriods_im_pos {0, 1} (q := 2) (by decide) (by decide)

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
      orderTwoCircuitPeriods_im_pos = 2 :=
  multipleEllipticGammaTransverseDADepth_eq_of_min _ _ 2
    ⟨{0, 1}, by decide, orderTwoCircuit_face_zero_one_differentialAlgebraic⟩
    orderTwoCircuit_face_not_differentialAlgebraic_of_card_lt_two

/-- Deleting the single label `2` from the coloop frame exposes the commensurable pair
`(i, 2i)`, which is differentially algebraic. -/
theorem orderTwoColoop_face_two_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero orderTwoColoopPeriods
        orderTwoColoopPeriods_im_pos {2}) :=
  differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_no_independentPair
    orderTwoColoopPeriods orderTwoColoopPeriods_im_pos {2} (q₀ := 0) (by decide)
    (fun _ _ hq hr hqr =>
      orderTwoColoopPeriods_commensurable_pair_not_linearIndependent
        (by simpa using hq) (by simpa using hr) hqr)

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
    ⟨{2}, by decide, orderTwoColoop_face_two_differentialAlgebraic⟩ fun J hJ => ?_
  rw [Finset.card_eq_zero.mp (by omega : J.card = 0)]
  exact orderTwoColoop_face_empty_not_differentialAlgebraic

/-! ## The individual hierarchy statements behind the two depths -/

/-- **Circuit frame, step one.** Every single structural difference of the circuit source is
hypertranscendental: deleting one label leaves two rationally independent periods. -/
theorem orderTwoCircuit_singleton_difference_hypertranscendental (j : Fin 3) :
    HypertranscendentalOver (RatFunc ℂ)
      (transverseDifferenceMero (orderTwoCircuitPeriods j)
        (multipleEllipticGammaLogDerivMero orderTwoCircuitPeriods
          orderTwoCircuitPeriods_im_pos)) := by
  rw [transverseDifferenceMero_multipleEllipticGammaLogDerivMero]
  exact orderTwoCircuit_face_not_differentialAlgebraic_of_card_lt_two {j} (by simp)

/-- **Circuit frame, step two.** The circuit source itself is hypertranscendental. -/
theorem orderTwoCircuit_source_hypertranscendental :
    HypertranscendentalOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivMero orderTwoCircuitPeriods
        orderTwoCircuitPeriods_im_pos) := by
  rw [← multipleEllipticGammaLogDerivFaceMero_empty]
  exact orderTwoCircuit_face_not_differentialAlgebraic_of_card_lt_two ∅ (by simp)

/-- **Coloop frame, step one.** The structural difference in the last direction is differentially
algebraic, because the deletion exposes the commensurable pair `(i, 2i)`. -/
theorem orderTwoColoop_lastDifference_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (transverseDifferenceMero (orderTwoColoopPeriods 2)
        (multipleEllipticGammaLogDerivMero orderTwoColoopPeriods
          orderTwoColoopPeriods_im_pos)) := by
  rw [transverseDifferenceMero_multipleEllipticGammaLogDerivMero]
  exact orderTwoColoop_face_two_differentialAlgebraic

/-- **Coloop frame, step two.** The coloop source itself is still hypertranscendental. -/
theorem orderTwoColoop_source_hypertranscendental :
    HypertranscendentalOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivMero orderTwoColoopPeriods
        orderTwoColoopPeriods_im_pos) := by
  rw [← multipleEllipticGammaLogDerivFaceMero_empty]
  exact orderTwoColoop_face_empty_not_differentialAlgebraic

/-! ## Equal rank, distinct depth -/

theorem orderTwoCircuitPeriods_augmented_span :
    insert (1 : ℂ) (Set.range orderTwoCircuitPeriods) =
      Set.range orderTwoCircuitPeriodFrame := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j.succ, (orderTwoCircuitPeriods_eq_frame j).symm⟩
  · rintro ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨j, (orderTwoCircuitPeriods_eq_frame j).symm⟩

theorem orderTwoColoopPeriods_augmented_span :
    insert (1 : ℂ) (Set.range orderTwoColoopPeriods) =
      Set.range orderTwoColoopPeriodFrame := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j.succ, (orderTwoColoopPeriods_eq_frame j).symm⟩
  · rintro ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨j, (orderTwoColoopPeriods_eq_frame j).symm⟩

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
    by rw [orderTwoCircuit_transverseDADepth, orderTwoColoop_transverseDADepth]; omega⟩

end

end GaloisForLFunctions.HTGeometry
