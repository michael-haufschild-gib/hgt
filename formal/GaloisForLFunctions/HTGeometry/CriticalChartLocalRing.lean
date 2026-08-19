import GaloisForLFunctions.HTGeometry.CriticalChartCentreHeight
import GaloisForLFunctions.HTGeometry.LocalizationAtPrimeDivisorDVR

/-!
# The local ring of the observation chart at the Schur centre

The centre of the Schur place on the observation chart ring has height one, and the chart ring is a
normal Noetherian domain, so the local ring there is a discrete valuation ring with the observation
field as its fraction field.  Its structure map lands in the observation Schur valuation ring, and
elements of the chart ring outside the centre become units there.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The local ring of the observation chart at the centre of the Schur place. -/
abbrev criticalChartLocalRing (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (m n : ℕ)
    [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)] :=
  Localization.AtPrime (criticalSchurChartUnder K (m := m) (n := n))

instance criticalChartLocalRing_isDVR :
    IsDiscreteValuationRing (criticalChartLocalRing K m n) :=
  isDiscreteValuationRing_localizationAtPrime (criticalSchurChartUnder_height K)

noncomputable instance criticalChartLocalRingAlgebra :
    Algebra (criticalChartLocalRing K m n) (criticalObservationField K m n) :=
  (IsLocalization.lift (M := (criticalSchurChartUnder K (m := m) (n := n)).primeCompl)
    (g := algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n))
    (fun y => by
      refine (Ne.isUnit ?_)
      intro h
      exact y.2 (by
        have hy0 : (y : criticalObservationChartRing K m n) = 0 :=
          IsFractionRing.injective (criticalObservationChartRing K m n)
            (criticalObservationField K m n) (by rw [h, map_zero])
        rw [hy0]
        exact Ideal.zero_mem _))).toAlgebra

instance criticalChartLocalRingTower :
    IsScalarTower (criticalObservationChartRing K m n) (criticalChartLocalRing K m n)
      (criticalObservationField K m n) :=
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

instance criticalChartLocalRing_isFractionRing :
    IsFractionRing (criticalChartLocalRing K m n) (criticalObservationField K m n) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (criticalSchurChartUnder K (m := m) (n := n)).primeCompl _ _

/-- Membership in the centre is detected at the Schur place. -/
theorem mem_criticalSchurChartUnder_iff (r : criticalObservationChartRing K m n) :
    r ∈ criticalSchurChartUnder K (m := m) (n := n) ↔
      algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAlgebra K (m := m) (n := n)) r ∈
        criticalSchurChartPrime K (m := m) (n := n) := Iff.rfl

theorem algebraMap_chartRing_observationField_mem_schur
    (r : criticalObservationChartRing K m n) :
    algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) r ∈
      criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) := by
  rw [mem_criticalSchurObservationValuationSubring_iff, ← IsScalarTower.algebraMap_apply]
  exact chartRing_mem_schur K Fact.out Fact.out r

theorem isUnit_chartRing_schur_of_notMem (s : criticalObservationChartRing K m n)
    (hs : s ∉ criticalSchurChartUnder K (m := m) (n := n)) :
    IsUnit (⟨algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) s,
      chartRing_mem_schur K Fact.out Fact.out s⟩ :
      criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  refine IsLocalRing.notMem_maximalIdeal.mp ?_
  intro hmem
  exact hs hmem

theorem isUnit_chartRing_observation_of_notMem (s : criticalObservationChartRing K m n)
    (hs : s ∉ criticalSchurChartUnder K (m := m) (n := n)) :
    IsUnit (⟨algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) s,
      algebraMap_chartRing_observationField_mem_schur K s⟩ :
      criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  refine isUnit_of_map_unit (algebraMap
    (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))) _ ?_
  have heq : (algebraMap
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      ⟨algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) s,
        algebraMap_chartRing_observationField_mem_schur K s⟩)
      = ⟨algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) s,
        chartRing_mem_schur K Fact.out Fact.out s⟩ := by
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply (criticalObservationChartRing K m n)
      (criticalObservationField K m n) (criticalSourceField K m n) s).symm
  rw [heq]
  exact isUnit_chartRing_schur_of_notMem K s hs

end

end GaloisForLFunctions.HTGeometry
