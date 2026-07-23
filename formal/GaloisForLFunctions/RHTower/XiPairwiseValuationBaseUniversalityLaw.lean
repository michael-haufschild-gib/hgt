import GaloisForLFunctions.RHTower.XiTransverseShiftPairwiseDifferentialRank
import GaloisForLFunctions.RHTower.XiTransverseShiftPairwiseAllValuationRank

/-!
# Pairwise Xi valuation-base universality

Rooted incidence independence is independent of every characteristic-zero coefficient field.
Consequently adjoining the complete scalar prime-valuation layer preserves the entire differential
matroid of every finite corrected integral-shift pair-difference packet, not only its rank or one
chosen independence predicate.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- **Characteristic-zero rooted-incidence universality.** The oriented incidence matroid of a
finite edge family is unchanged when its coefficients are interpreted in any other
characteristic-zero field. -/
theorem rootedIncidenceMatroid_charZero_eq
    {C D V E : Type} [Field C] [Field D] [CharZero C] [CharZero D]
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (tail head : E → V) :
    rootedIncidenceMatroid (C := C) root tail head =
      rootedIncidenceMatroid (C := D) root tail head := by
  apply Matroid.ext_indep
  · simp
  · intro I _hI
    rw [rootedIncidenceMatroid_indep_iff,
      rootedIncidenceMatroid_indep_iff]
    have hC :
        (fun e : I ↦ rootedIncidenceMatrix (C := C) root tail head e) =
          fun e : I ↦ algebraMap ℚ C ∘
            rootedIncidenceMatrix (C := ℚ) root tail head e := by
      funext e v
      simp only [rootedIncidenceMatrix, Function.comp_apply, map_sub]
      congr <;> split_ifs <;> simp_all
    have hD :
        (fun e : I ↦ rootedIncidenceMatrix (C := D) root tail head e) =
          fun e : I ↦ algebraMap ℚ D ∘
            rootedIncidenceMatrix (C := ℚ) root tail head e := by
      funext e v
      simp only [rootedIncidenceMatrix, Function.comp_apply, map_sub]
      congr <;> split_ifs <;> simp_all
    rw [hC, hD, linearIndependent_algebraMap_comp_iff,
      linearIndependent_algebraMap_comp_iff]

end GaloisForLFunctions.HTGeometry

namespace RHTower

open Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiPairwiseBaseLawUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiPairwiseBaseLawUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiPairwiseBaseLawUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiPairwiseBaseLawUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiPairwiseBaseLawCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiPairwiseBaseLawCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiPairwiseBaseLawAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiPairwiseBaseLawAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- **Pairwise Xi valuation-base universality.** Adjoining every scalar prime-valuation layer
preserves the complete differential matroid of every finite corrected integral-shift edge
packet. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_base_eq_allValuation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) := by
  rw [
    xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
      root shift hroot hinj tail head,
    xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
      root shift hroot hinj tail head]
  exact rootedIncidenceMatroid_charZero_eq root tail head

/-- Every selected corrected pair-difference packet is differentially independent over the
rational-coordinate base exactly when it remains so over the all-valuation base. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_base_iff_allValuation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Set E) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun e : I ↦ xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun e : I ↦ xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head e) := by
  rw [
    xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_iff
      root shift hroot hinj tail head I,
    xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff
      root shift hroot hinj tail head I,
    rootedIncidenceMatroid_charZero_eq
      (C := upperEndRationalCoordinateField)
      (D := analyticScalarValuationLayerDifferentialField) root tail head]

/-- Every selected corrected pair-difference packet has the same differential rank before and
after adjoining all scalar prime-valuation layers. -/
theorem xiTransverseShiftPairDifferenceUpperEndCarrier_differentialRank_base_eq_allValuation
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (hinj : Function.Injective shift) (tail head : E → V) (I : Set E) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)).eRk I =
      (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)).eRk I := by
  rw [xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_base_eq_allValuation
    root shift hroot hinj tail head]

end


end RHTower
