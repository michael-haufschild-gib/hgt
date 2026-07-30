import GaloisForLFunctions.HTGeometry.DifferentialConstantLinearFamilyMatroid
import GaloisForLFunctions.RHTower.XiTransverseShiftCollisionIncidenceRank
import GaloisForLFunctions.RHTower.XiTransverseShiftPairwiseValue
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Pairwise differential rank of every integral completed-Xi shift

The arbitrary integral transverse source family already has the pointed collision matroid of its
shift labels, and every source carrier is the actual completed-Xi shift defect after its exact
archimedean correction. Taking oriented pairwise differences converts that collision law into an
exact rooted incidence matroid over the rational coordinate base.

Consequently all differential relations among any finite pairwise packet are exactly Kirchhoff
circulations. For the complete ordered pair family, the pairwise reporters generate the same
differential field as the vertex family. These statements are unconditional and apply to odd as
well as even integral shifts; no rationality claim is made for the odd-shift correction.
-/

namespace RHTower

open Complex Filter Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

open scoped UpperEndDifferentialInstances

/-! ## Complete pairwise generated fields -/

/-- All ordered pairwise corrected integral-shift reporters generate exactly the vertex field over
the rational coordinate base as soon as the family contains a zero-shift root. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices
    {V : Type} (root : V) (shift : V → ℕ) (hroot : shift root = 0) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift Prod.snd Prod.fst)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)) := by
  let x := fun v ↦ xiTransverseShiftUpperEndCarrier (shift v)
  have hx0 : x root = 0 := by
    simp [x, hroot]
  have h := differentialAdjoin_range_pairwiseDifferences_eq_of_root_zero
    (F := upperEndRationalCoordinateField) (K := upperEndMeroField) root x hx0
  simpa only [x, xiTransverseShiftPairDifferenceUpperEndCarrier] using! h

/-! ## Rational-coordinate incidence matroid -/

/-- **All-integral pairwise Xi incidence law.** For every finite oriented edge family on distinct
integral shift labels with a zero root, the corrected completed-Xi pairwise differences represent
exactly the rooted incidence matroid over the rational coordinate field. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      rootedIncidenceMatroid
        (C := upperEndRationalCoordinateField) root tail head := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid]
  simpa [hroot] using
    (pointedCollisionIncidenceMatroid_eq_rootedIncidenceMatroid_of_injective
      (C := upperEndRationalCoordinateField) shift root hinj tail head)

/-- Rational-base Prop interface for every selected all-integral pairwise packet. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_iff
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Set E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : I ↦ xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      (rootedIncidenceMatroid
        (C := upperEndRationalCoordinateField) root tail head).Indep I := by
  let y := xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head
  rw [← differentialFamilyMatroid_indep_iff y I,
    xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
      root shift hroot hinj tail head]

/-- Explicit rational-base Kirchhoff interface for all-integral pairwise Xi packets. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_finset_iff_vertexConservation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Finset E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : ↑(↑I : Set E) ↦
          xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      ∀ weight : ↑(↑I : Set E) → upperEndRationalCoordinateField,
        (∀ v : V,
          (∑ e : ↑(↑I : Set E),
              if head (e : E) = v then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if tail (e : E) = v then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_iff
      root shift hroot hinj tail head (↑I : Set E),
    rootedIncidenceMatroid_indep_iff_vertex_conservation]

/-- Exact rational-base differential rank of every all-integral pairwise edge packet. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eRk
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)).eRk I =
      (rootedIncidenceMatroid
        (C := upperEndRationalCoordinateField) root tail head).eRk I := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
    root shift hroot hinj tail head]

end

end RHTower
