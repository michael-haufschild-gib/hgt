import GaloisForLFunctions.HTGeometry.DifferentialConstantLinearFamilyMatroid
import GaloisForLFunctions.RHTower.XiTransverseShiftCollisionIncidenceAllValuationRank
import GaloisForLFunctions.RHTower.XiTransverseShiftPairwiseValue
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Pairwise integral completed-Xi rank over every valuation layer

This module transports the arbitrary integral pairwise completed-Xi laws to the differential base
obtained by adjoining every scalar prime-valuation layer. It is kept separate from the value and
rational-coordinate leaf so each theorem cluster compiles with bounded elaboration pressure.
-/

namespace RHTower

open Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

open scoped UpperEndDifferentialInstances

/-- The complete arbitrary integral pairwise family preserves the full generated field over the
all-valuation base. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices
    {V : Type} (root : V) (shift : V → ℕ) (hroot : shift root = 0) :
    differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift Prod.snd Prod.fst)) =
      differentialAdjoin analyticScalarValuationLayerDifferentialField
        (Set.range fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) := by
  let x := fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)
  have hx0 : x root = 0 := by
    simp [x, hroot]
  have h := differentialAdjoin_range_pairwiseDifferences_eq_of_root_zero
    (F := analyticScalarValuationLayerDifferentialField) (K := upperEndMeroField) root x hx0
  simpa only [x, xiTransverseShiftPairDifferenceUpperEndCarrier] using h

/-- **All-valuation all-integral pairwise Xi incidence law.** The corrected completed-Xi
pairwise differences represent exactly the rooted incidence matroid after every scalar valuation
layer has been adjoined. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      rootedIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) root tail head := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid]
  simpa [hroot] using
    (pointedCollisionIncidenceMatroid_eq_rootedIncidenceMatroid_of_injective
      (C := analyticScalarValuationLayerDifferentialField) shift root hinj tail head)

/-- All-valuation Prop interface for every selected all-integral pairwise packet. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Set E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : I ↦ xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      (rootedIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) root tail head).Indep I := by
  let y := xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
      root shift hroot hinj tail head]

/-- Explicit all-valuation Kirchhoff interface for all-integral pairwise Xi packets. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_vertexConservation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Finset E) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : ↑(↑I : Set E) ↦
          xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      ∀ weight : ↑(↑I : Set E) → analyticScalarValuationLayerDifferentialField,
        (∀ v : V,
          (∑ e : ↑(↑I : Set E),
              if head (e : E) = v then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if tail (e : E) = v then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff
      root shift hroot hinj tail head (↑I : Set E),
    rootedIncidenceMatroid_indep_iff_vertex_conservation]

/-- Exact all-valuation differential rank of every all-integral pairwise edge packet. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)).eRk I =
      (rootedIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) root tail head).eRk I := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
    root shift hroot hinj tail head]

end

end RHTower
