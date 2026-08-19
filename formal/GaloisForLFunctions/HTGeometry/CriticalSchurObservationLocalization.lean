import GaloisForLFunctions.HTGeometry.CriticalSchurObservationChartLocal

/-!
# The observation Schur place as a localization of the chart ring

Packaging the chart-local identification as an `IsLocalization` instance, together with the algebra
towers from the observation coordinate ring and the chart ring down to the two Schur valuation
rings.  These are the structures through which the differential of an arbitrary element of the
observation Schur place is reduced to the differentials of the observation coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The chart ring acts on the observation Schur valuation ring. -/
noncomputable def chartRingToObservationSchur :
    criticalObservationChartRing K m n →+*
      criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) where
  toFun r := ⟨algebraMap (criticalObservationChartRing K m n)
      (criticalObservationField K m n) r,
    algebraMap_chartRing_observationField_mem_schur K r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

noncomputable instance chartRingObservationSchurAlgebra :
    Algebra (criticalObservationChartRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  (chartRingToObservationSchur K).toAlgebra

/-- **The observation Schur valuation ring is the localization of the chart ring at the centre.** -/
instance criticalSchurObservation_isLocalization :
    IsLocalization (criticalSchurChartUnder K (m := m) (n := n)).primeCompl
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  constructor; constructor
  · rintro ⟨y, hy⟩
    exact isUnit_chartRing_observation_of_notMem K y hy
  · intro a
    obtain ⟨z, hz⟩ := criticalSchurObservation_isInteger_chartLocal K a
    obtain ⟨⟨r, ⟨sv, hsv⟩⟩, hrs⟩ := IsLocalization.surj
      (M := (criticalSchurChartUnder K (m := m) (n := n)).primeCompl) z
    refine ⟨⟨r, ⟨sv, hsv⟩⟩, ?_⟩
    apply Subtype.ext
    have hF := congrArg (algebraMap (criticalChartLocalRing K m n)
      (criticalObservationField K m n)) hrs
    rw [map_mul, hz, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hF
    exact hF
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) x
        = algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) y :=
      congrArg Subtype.val hxy
    rw [IsFractionRing.injective (criticalObservationChartRing K m n)
      (criticalObservationField K m n) this]

noncomputable instance chartRingSchurSourceAlgebra :
    Algebra (criticalObservationChartRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  ((algebraMap
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))).comp
    (chartRingToObservationSchur K)).toAlgebra

instance chartRingSchurSourceTower :
    IsScalarTower (criticalObservationChartRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance observationRingSchurSourceAlgebra :
    Algebra (criticalObservationRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  ((algebraMap (criticalObservationChartRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))).comp
    (algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n))).toAlgebra

instance observationRingChartSchurTower :
    IsScalarTower (criticalObservationRing K m n) (criticalObservationChartRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem coe_algebraMap_observationRing_schur (p : criticalObservationRing K m n) :
    ((algebraMap (criticalObservationRing K m n)
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) p :
        criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
      criticalSourceField K m n)
      = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n) p := by
  rw [IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationChartRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)),
    IsScalarTower.algebraMap_apply (criticalObservationChartRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))]
  show algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
      (algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n)
        (algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n) p)) = _
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

instance observationRingSchurGroundTower :
    IsScalarTower K (criticalObservationRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  apply Subtype.ext
  rw [coe_algebraMap_ground_criticalSchurSourceValuation K Fact.out Fact.out c,
    coe_algebraMap_observationRing_schur K, ← IsScalarTower.algebraMap_apply]

instance chartRingSchurGroundTower :
    IsScalarTower K (criticalObservationChartRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [IsScalarTower.algebraMap_apply K (criticalObservationRing K m n)
      (criticalObservationChartRing K m n),
    ← IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationChartRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)),
    ← IsScalarTower.algebraMap_apply K (criticalObservationRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))]

instance observationSchurGroundTower :
    IsScalarTower K
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  criticalSchurObservationSourceTower K Fact.out Fact.out

end

end GaloisForLFunctions.HTGeometry
