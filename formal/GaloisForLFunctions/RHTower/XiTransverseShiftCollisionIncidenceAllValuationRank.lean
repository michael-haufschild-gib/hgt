import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionIncidenceMatroid
import GaloisForLFunctions.HTGeometry.DifferentialPairwiseCommonMode
import GaloisForLFunctions.RHTower.XiTransverseShiftPairwiseValue
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank

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

local instance xiCollisionIncidenceLayerUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiCollisionIncidenceLayerUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiCollisionIncidenceLayerUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiCollisionIncidenceLayerUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiCollisionIncidenceLayerCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiCollisionIncidenceLayerCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiCollisionIncidenceLayerAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiCollisionIncidenceLayerAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

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
