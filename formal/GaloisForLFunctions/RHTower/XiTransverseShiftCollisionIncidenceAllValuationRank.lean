import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionIncidenceMatroid
import GaloisForLFunctions.HTGeometry.DifferentialPairwiseCommonMode
import GaloisForLFunctions.RHTower.XiTransverseShiftPairwiseValue
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Collision-quotient Xi incidence rank over all scalar valuation layers

The arbitrary-label incidence law remains exact after adjoining every scalar prime-valuation
layer. This leaf is separate from the rational-coordinate theorem to bound elaboration pressure.
-/

namespace RHTower

open Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

open scoped UpperEndDifferentialInstances

/-- The corrected Xi values at every occupied nonzero shift label of an arbitrary family remain
jointly differentially independent over the full scalar valuation-layer field. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_pointedOccupiedLabelSupport_differentialIndependent
    {V : Type} (shift : V → ℕ) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun q : pointedOccupiedLabelSupport shift 0 ↦
        xiTransverseShiftUpperEndCarrier q) := by
  apply
    xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers_of_injective_ne_zero
      (fun q : pointedOccupiedLabelSupport shift 0 ↦ (q : ℕ))
  · exact Subtype.val_injective
  · intro q
    exact q.property.2

/-- The corrected Xi values at the occupied nonzero shift labels remain jointly differentially
independent after adjoining every scalar prime-valuation layer. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_pointedCollisionSupport_differentialIndependent
    {V : Type} [Fintype V] (shift : V → ℕ) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun q : pointedCollisionIncidenceSupport shift 0 ↦
        xiTransverseShiftUpperEndCarrier q) := by
  apply
    xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers_of_injective_ne_zero
      (fun q : pointedCollisionIncidenceSupport shift 0 ↦ (q : ℕ))
  · exact Subtype.val_injective
  · intro q
    exact (Finset.mem_erase.mp q.property).1

/-- **All-valuation exact Xi common-mode classifier.** The complete ordered pairwise corrected-Xi
reporter recovers the vertex differential field over the full scalar valuation-layer base exactly
when the finite shift family contains zero; repetitions are allowed. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices_iff_zero_mem_range
    {V : Type} (anchor : V) (shift : V → ℕ) :
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift Prod.snd Prod.fst)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) ↔
      0 ∈ Set.range shift := by
  have hx0 : xiTransverseShiftUpperEndCarrier 0 = 0 :=
    xiTransverseShiftUpperEndCarrier_zero
  have hx :=
    xiTransverseShiftUpperEndCarrier_allValuation_pointedOccupiedLabelSupport_differentialIndependent
      shift
  change
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun p : V × V ↦
          xiTransverseShiftUpperEndCarrier (shift p.1) -
            xiTransverseShiftUpperEndCarrier (shift p.2)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) ↔
      0 ∈ Set.range shift
  exact differentialAdjoin_range_gradedPairwiseDifferences_eq_iff_loop_mem_range_arbitrary
    (F := analyticScalarValuationLayerDifferentialField) (K := upperEndMeroField)
    (V := V) (L := ℕ) anchor shift 0
    xiTransverseShiftUpperEndCarrier hx0 hx

/-- **All-valuation arbitrary-observation DA law.** Even after every scalar valuation layer is
adjoined, a corrected Xi value is differentially algebraic over a selected subfamily exactly when
its shift is zero or its shift label is already observed. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_differentialAlgebraicOver_differentialAdjoin_image_iff_zero_or_observed
    {V : Type*} (shift : V → ℕ) (I : Set V) (anchor : V) :
    DifferentialAlgebraicOver
        (differentialAdjoin analyticScalarValuationLayerDifferentialField
          ((fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) '' I))
        (xiTransverseShiftUpperEndCarrier (shift anchor)) ↔
      shift anchor = 0 ∨ shift anchor ∈ shift '' I := by
  exact
    differentialAlgebraicOver_differentialAdjoin_image_iff_loop_or_observedLabel_of_pointedCollisionMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) shift 0 I anchor
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
        shift)

/-- **All-valuation arbitrary-observation HT law.** The marked corrected-Xi value remains
hypertranscendental over the selected observation field exactly when its positive shift label is
absent from that packet. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_hypertranscendentalOver_differentialAdjoin_image_iff_pos_unobserved
    {V : Type*} (shift : V → ℕ) (I : Set V) (anchor : V) :
    HypertranscendentalOver
        (differentialAdjoin analyticScalarValuationLayerDifferentialField
          ((fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) '' I))
        (xiTransverseShiftUpperEndCarrier (shift anchor)) ↔
      shift anchor ≠ 0 ∧ shift anchor ∉ shift '' I := by
  exact
    hypertranscendentalOver_differentialAdjoin_image_iff_nonloop_unobservedLabel_of_pointedCollisionMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) shift 0 I anchor
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
        shift)

/-- **All-valuation corrected-Xi circuit classification.** The same exact singleton/pair circuit
spectrum survives after every scalar valuation layer is adjoined to the coefficient field. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_differentialFamilyMatroid_isCircuit_iff
    {V : Type*} (shift : V → ℕ) (C : Set V) :
    (differentialFamilyMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun v ↦ xiTransverseShiftUpperEndCarrier (shift v))).IsCircuit C ↔
      (∃ i, C = {i} ∧ shift i = 0) ∨
        ∃ i j, i ≠ j ∧ C = {i, j} ∧
          shift i = shift j ∧ shift i ≠ 0 := by
  rw [xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_isCircuit_iff]

/-- **All-valuation relative corrected-Xi HT spectrum.** Even over the full scalar valuation
layer, a corrected Xi value is hypertranscendental over every other family value exactly when its
positive shift label is unique. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_hypertranscendentalOver_differentialAdjoin_compl_iff_unique_pos
    {V : Type*} (anchor : V) (shift : V → ℕ) :
    HypertranscendentalOver
        (differentialAdjoin analyticScalarValuationLayerDifferentialField
          ((fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) ''
            (Set.univ \ {anchor})))
        (xiTransverseShiftUpperEndCarrier (shift anchor)) ↔
      shift anchor ≠ 0 ∧ ∀ j, shift j = shift anchor → j = anchor := by
  exact
    hypertranscendentalOver_differentialAdjoin_compl_iff_unique_nonloop_of_pointedCollisionMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) shift 0 anchor
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
        shift)

/-- Over the full valuation layer, relative differential algebraicity is still exactly zero shift
or repetition of the anchor's shift label. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_differentialAlgebraicOver_differentialAdjoin_compl_iff_zero_or_repeated
    {V : Type*} (anchor : V) (shift : V → ℕ) :
    DifferentialAlgebraicOver
        (differentialAdjoin analyticScalarValuationLayerDifferentialField
          ((fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) ''
            (Set.univ \ {anchor})))
        (xiTransverseShiftUpperEndCarrier (shift anchor)) ↔
      shift anchor = 0 ∨ ∃ j, j ≠ anchor ∧ shift j = shift anchor := by
  exact
    differentialAlgebraicOver_differentialAdjoin_compl_iff_loop_or_collision_of_pointedCollisionMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) shift 0 anchor
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
        shift)

/-- **All-valuation exact corrected-Xi common-mode spectrum.** After every scalar valuation layer
is adjoined, a corrected completed-Xi value is hypertranscendental over the complete pairwise
reporter exactly when shift zero is absent. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_hypertranscendentalOver_completePairDifferences_iff_zero_not_mem_range
    {V : Type} (anchor : V) (shift : V → ℕ) :
    HypertranscendentalOver
      (differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift Prod.snd Prod.fst)))
      (xiTransverseShiftUpperEndCarrier (shift anchor)) ↔
      0 ∉ Set.range shift := by
  have hx :=
    xiTransverseShiftUpperEndCarrier_allValuation_pointedOccupiedLabelSupport_differentialIndependent
      shift
  change HypertranscendentalOver
    (differentialAdjoin analyticScalarValuationLayerDifferentialField
      (Set.range fun p : V × V ↦
        xiTransverseShiftUpperEndCarrier (shift p.1) -
          xiTransverseShiftUpperEndCarrier (shift p.2)))
    (xiTransverseShiftUpperEndCarrier (shift anchor)) ↔ 0 ∉ Set.range shift
  exact hypertranscendentalOver_gradedPairwiseDifferences_iff_loop_not_mem_range
    (F := analyticScalarValuationLayerDifferentialField) (K := upperEndMeroField)
    anchor shift 0 xiTransverseShiftUpperEndCarrier
    xiTransverseShiftUpperEndCarrier_zero hx

/-- The corrected-Xi contracted nonloop phase transition survives after adjoining every scalar
valuation observable to the coefficient field. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_contract_completePairDifferences_isNonloop_iff_zero_not_mem_range
    {V : Type} (anchor : V) (shift : V → ℕ) :
    (Matroid.contract
        (differentialMatroid analyticScalarValuationLayerDifferentialField upperEndMeroField)
        (Set.range
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift Prod.snd Prod.fst))).IsNonloop
      (xiTransverseShiftUpperEndCarrier (shift anchor)) ↔
        0 ∉ Set.range shift := by
  rw [differentialMatroid_contract_isNonloop_iff_hypertranscendentalOver]
  exact
    xiTransverseShiftUpperEndCarrier_allValuation_hypertranscendentalOver_completePairDifferences_iff_zero_not_mem_range
      anchor shift

/-- **All-valuation arbitrary-label Xi incidence law.** Repeated and zero integral shifts are
classified by the same occupied-label quotient incidence matroid over the enlarged base. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) shift 0 tail head := by
  have hx0 : xiTransverseShiftUpperEndCarrier 0 = 0 :=
    xiTransverseShiftUpperEndCarrier_zero
  have hx :=
    xiTransverseShiftUpperEndCarrier_allValuation_pointedCollisionSupport_differentialIndependent
      shift
  simpa [xiTransverseShiftPairDifferenceUpperEndCarrier] using
    (differentialFamilyMatroid_gradedPairwiseDifferences_eq_pointedCollisionIncidenceMatroid
      (C := analyticScalarValuationLayerDifferentialField) shift 0 tail head
      xiTransverseShiftUpperEndCarrier hx0 hx)

/-- All-valuation Prop interface for every arbitrary-label Xi edge packet. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) (I : Set E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : I ↦ xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      (pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) shift 0 tail head).Indep I := by
  let y := xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

/-- Full occupied-shift quotient Kirchhoff interface over the all-valuation base. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_pointedCollisionVertexConservation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) (I : Finset E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : ↑(↑I : Set E) ↦
          xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      ∀ weight : ↑(↑I : Set E) →
          analyticScalarValuationLayerDifferentialField,
        (∀ q : pointedCollisionIncidenceVertex shift 0,
          (∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf shift 0
                (head (e : E)) = q then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf shift 0
                (tail (e : E)) = q then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence
      shift tail head (↑I : Set E),
    pointedCollisionIncidenceMatroid_indep_iff_vertex_conservation]

/-- Exact all-valuation differential rank after collapsing repeated shift labels. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_pointedCollisionIncidence_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)).eRk I =
      (pointedCollisionIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) shift 0 tail head).eRk I := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

end

end RHTower
