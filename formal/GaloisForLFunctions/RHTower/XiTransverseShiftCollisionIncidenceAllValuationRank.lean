import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionIncidenceMatroid
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
  have hx : DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun q : pointedCollisionIncidenceSupport shift 0 ↦
        xiTransverseShiftUpperEndCarrier q) := by
    apply
      xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers_of_injective_ne_zero
        (fun q : pointedCollisionIncidenceSupport shift 0 ↦ (q : ℕ))
    · exact Subtype.val_injective
    · intro q
      exact (Finset.mem_erase.mp q.property).1
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
