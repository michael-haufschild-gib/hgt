import GaloisForLFunctions.HTGeometry.Critical.Chart.LocalRing

/-!
# The observation Schur place is the local ring of the chart at its centre

The local ring of the observation chart at the centre of the Schur place is a discrete valuation
ring contained in the observation Schur valuation ring.  A valuation ring has no proper overring
inside its fraction field other than the field, and the observation Schur valuation ring is proper,
so the two coincide:

```text
criticalSchurObservation_isInteger_chartLocal :
    every element of the observation Schur valuation ring is a ratio r / s of chart-ring elements
    with s outside the centre
```

This is the statement that makes the differential of an arbitrary element of the observation Schur
place expressible through the differentials of the observation coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing

set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

theorem notUnit_chartRing_observation_of_mem (r : criticalObservationChartRing K m n)
    (hr : r ∈ criticalSchurChartUnder K (m := m) (n := n)) :
    ¬ IsUnit (⟨algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) r,
      algebraMap_chartRing_observationField_mem_schur K r⟩ :
      criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  intro hu
  have hmap := hu.map (algebraMap
    (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
  have heq : (algebraMap
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      ⟨algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) r,
        algebraMap_chartRing_observationField_mem_schur K r⟩)
      = ⟨algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) r,
        chartRing_mem_schur K Fact.out Fact.out r⟩ := by
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply (criticalObservationChartRing K m n)
      (criticalObservationField K m n) (criticalSourceField K m n) r).symm
  rw [heq] at hmap
  exact (IsLocalRing.notMem_maximalIdeal.mpr hmap) hr

/-- **The observation Schur valuation ring is the local ring of the chart at the centre.** -/
theorem criticalSchurObservation_isInteger_chartLocal
    (a : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    IsLocalization.IsInteger (criticalChartLocalRing K m n)
      ((a : criticalObservationField K m n)) := by
  rcases ValuationRing.isInteger_or_isInteger (criticalChartLocalRing K m n)
    ((a : criticalObservationField K m n)) with h | h
  · exact h
  obtain ⟨x, hx⟩ := h
  by_cases ha0 : (a : criticalObservationField K m n) = 0
  · exact ⟨0, by rw [map_zero, ha0]⟩
  by_cases hxu : IsUnit x
  · obtain ⟨u, rfl⟩ := hxu
    refine ⟨((u⁻¹ : (criticalChartLocalRing K m n)ˣ) : criticalChartLocalRing K m n), ?_⟩
    have h1 : algebraMap (criticalChartLocalRing K m n) (criticalObservationField K m n)
        ((u⁻¹ : (criticalChartLocalRing K m n)ˣ) : criticalChartLocalRing K m n) *
        algebraMap (criticalChartLocalRing K m n) (criticalObservationField K m n)
          ((u : (criticalChartLocalRing K m n)ˣ) : criticalChartLocalRing K m n) = 1 := by
      rw [← map_mul]
      simp
    rw [hx] at h1
    field_simp at h1
    exact h1
  · exfalso
    obtain ⟨⟨r, ⟨sv, hsv⟩⟩, hrs⟩ := IsLocalization.surj
      (M := (criticalSchurChartUnder K (m := m) (n := n)).primeCompl) x
    have hr : r ∈ criticalSchurChartUnder K (m := m) (n := n) := by
      by_contra hrn
      apply hxu
      have hru : IsUnit (algebraMap (criticalObservationChartRing K m n)
          (criticalChartLocalRing K m n) r) :=
        IsLocalization.map_units (M := (criticalSchurChartUnder K (m := m) (n := n)).primeCompl)
          (criticalChartLocalRing K m n)
          (⟨r, hrn⟩ : (criticalSchurChartUnder K (m := m) (n := n)).primeCompl)
      rw [← hrs] at hru
      exact (isUnit_of_mul_isUnit_left hru)
    have hF := congrArg (algebraMap (criticalChartLocalRing K m n)
      (criticalObservationField K m n)) hrs
    rw [map_mul, hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hF
    have hAeq : (⟨algebraMap (criticalObservationChartRing K m n)
        (criticalObservationField K m n) sv,
        algebraMap_chartRing_observationField_mem_schur K sv⟩ :
        criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        = a * ⟨algebraMap (criticalObservationChartRing K m n)
          (criticalObservationField K m n) r,
          algebraMap_chartRing_observationField_mem_schur K r⟩ := by
      apply Subtype.ext
      show algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) sv
        = (a : criticalObservationField K m n) *
          algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) r
      rw [← hF]
      field_simp
    have hsunit := isUnit_chartRing_observation_of_notMem K sv hsv
    rw [hAeq] at hsunit
    exact notUnit_chartRing_observation_of_mem K r hr (isUnit_of_mul_isUnit_right hsunit)

end

end GaloisForLFunctions.HTGeometry
