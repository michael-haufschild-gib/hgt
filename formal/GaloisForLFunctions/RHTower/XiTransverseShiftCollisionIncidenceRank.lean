import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionIncidenceMatroid
import GaloisForLFunctions.RHTower.XiTransverseShiftPairwiseValue

/-!
# Collision-quotient incidence rank of arbitrary integral Xi shift families

Repeated shift labels and zero-shift vertices are retained rather than excluded. Pairwise
corrected completed-Xi values represent the incidence matroid of the finite occupied-shift
quotient, with the zero-shift column deleted.
-/

namespace RHTower

open Complex Filter Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiCollisionIncidenceUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiCollisionIncidenceUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiCollisionIncidenceUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiCollisionIncidenceUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiCollisionIncidenceCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiCollisionIncidenceCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

/-- **Arbitrary-label Xi incidence law.** For every finite integral shift family, including
repeated and zero shifts, the pairwise corrected completed-Xi reporters represent exactly the
incidence matroid after equal shift labels are collapsed and the zero label is deleted. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) shift 0 tail head := by
  have hx0 : xiTransverseShiftUpperEndCarrier 0 = 0 :=
    xiTransverseShiftUpperEndCarrier_zero
  have hx : DifferentialIndependent upperEndRationalCoordinateField
      (fun q : pointedCollisionIncidenceSupport shift 0 ↦
        xiTransverseShiftUpperEndCarrier q) := by
    apply xiTransverseShiftUpperEndCarrier_differentialIndependent_of_injective_ne_zero
      (fun q : pointedCollisionIncidenceSupport shift 0 ↦ (q : ℕ))
    · exact Subtype.val_injective
    · intro q
      exact (Finset.mem_erase.mp q.property).1
  simpa [xiTransverseShiftPairDifferenceUpperEndCarrier] using
    (differentialFamilyMatroid_gradedPairwiseDifferences_eq_pointedCollisionIncidenceMatroid
      (C := upperEndRationalCoordinateField) shift 0 tail head
      xiTransverseShiftUpperEndCarrier hx0 hx)

/-- Prop interface for every selected packet of an arbitrary-label Xi edge family. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) (I : Set E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : I ↦ xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      (pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) shift 0 tail head).Indep I := by
  let y := xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

/-- Exact differential rank of every packet after collapsing repeated shift labels. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_pointedCollisionIncidence_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)).eRk I =
      (pointedCollisionIncidenceMatroid
        (C := upperEndRationalCoordinateField) shift 0 tail head).eRk I := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid]

end

end RHTower
