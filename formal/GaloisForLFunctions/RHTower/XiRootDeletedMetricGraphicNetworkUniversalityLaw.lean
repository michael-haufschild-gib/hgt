import GaloisForLFunctions.RHTower.XiPairwiseValuationBaseUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransversePrimeSourceHilbertMetric

/-!
# Xi root-deleted metric/graphic-network universality

A cofinite positive prime-source metric on the nonroot transverse carriers detects all vertex
collisions. When the root has shift zero, this local Hilbert certificate forces global shift
injectivity and therefore determines the complete differential matroid of every corrected
pair-difference network over both the rational-coordinate and all-valuation bases.
-/

namespace RHTower

open Set
open scoped ComplexOrder Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiRootMetricUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiRootMetricUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiRootMetricUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiRootMetricUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiRootMetricCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiRootMetricCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiRootMetricAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiRootMetricAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- **Xi root-deleted metric/graphic-network universality law.**  A positive cofinite aperture
metric on all nonroot vertices promotes one-prime Hilbert separation to global vertex injectivity;
every corrected edge-difference packet is then exactly the rooted incidence matroid, independently
of adjoining all scalar valuation layers. -/
theorem xiTransverse_rootDeletedMetric_graphicNetworkUniversality
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (shift : V → ℕ) (hroot : shift root = 0)
    (tail head : E → V) (m : ℕ)
    (hmetric :
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : {v : V // v ≠ root} × Fin (m + 1) →
            {p : Nat.Primes // p ∉ forbidden},
          (xiTransversePrimeJetApertureGram
            (fun v : {v : V // v ≠ root} => shift v) m forbidden points).PosDef) :
    Function.Injective shift ∧
      differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
        rootedIncidenceMatroid
          (C := upperEndRationalCoordinateField) root tail head ∧
      differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
        rootedIncidenceMatroid
          (C := analyticScalarValuationLayerDifferentialField) root tail head ∧
      differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
        differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) := by
  have hcollision :
      Function.Injective (fun v : {v : V // v ≠ root} => shift v) ∧
        ∀ v : {v : V // v ≠ root}, shift v ≠ 0 :=
    (xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero
      (fun v : {v : V // v ≠ root} => shift v) m).1 hmetric
  have hinj : Function.Injective shift := by
    intro x y hxy
    by_cases hx : x = root
    · subst x
      by_contra hy
      have hyzero : shift y = 0 := hxy.symm.trans hroot
      exact hcollision.2 ⟨y, Ne.symm hy⟩ hyzero
    · by_cases hy : y = root
      · subst y
        have hxzero : shift x = 0 := hxy.trans hroot
        exact False.elim (hcollision.2 ⟨x, hx⟩ hxzero)
      · exact congrArg Subtype.val
          (hcollision.1 (show shift (⟨x, hx⟩ : {v : V // v ≠ root}) =
            shift (⟨y, hy⟩ : {v : V // v ≠ root}) from hxy))
  have hbase :=
    xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid
      root shift hroot hinj tail head
  have hall :=
    xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid
      root shift hroot hinj tail head
  have hinvariant :=
    xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_base_eq_allValuation
      root shift hroot hinj tail head
  exact ⟨hinj, hbase, hall, hinvariant⟩

end

end RHTower
