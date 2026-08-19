import GaloisForLFunctions.HTGeometry.CriticalObservationCoordinateRing
import GaloisForLFunctions.HTGeometry.CriticalSourceSubringIntegrality
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The marked observation chart ring, and the integral chart algebra

Inverting the marked product in the observation coordinate ring gives the coordinate ring of the
chart.  It is a localization of a polynomial ring, hence integrally closed, and every raw and
reciprocal coordinate of the horizon is integral over it — the finiteness of the critical map in
the form the going-down theorem consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)]

theorem isUnit_algebraMap_criticalObservationMarked :
    IsUnit (algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
      (criticalObservationMarked K)) := by
  rw [algebraMap_criticalObservationMarked K]
  exact (mul_ne_zero (criticalSourceRaw_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSourceRecip_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n))).isUnit

/-- Coordinate ring of the marked observation chart. -/
abbrev criticalObservationChartRing (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :=
  Localization.Away (criticalObservationMarked K (m := m) (n := n))

/-- The chart ring acts on the source field. -/
noncomputable instance criticalObservationChartRingAlgebra :
    Algebra (criticalObservationChartRing K m n) (criticalSourceField K m n) :=
  (IsLocalization.Away.lift (S := criticalObservationChartRing K m n)
    (criticalObservationMarked K)
    (isUnit_algebraMap_criticalObservationMarked K)).toAlgebra

instance criticalObservationChartRingTower :
    IsScalarTower (criticalObservationRing K m n) (criticalObservationChartRing K m n)
      (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp _ _).symm

theorem criticalObservationMarked_ne_zero :
    criticalObservationMarked K (m := m) (n := n) ≠ 0 := by
  intro h
  exact (mul_ne_zero (criticalSourceRaw_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSourceRecip_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n)))
    (by rw [← algebraMap_criticalObservationMarked K, h, map_zero])

instance criticalObservationChartRing_isIntegrallyClosed :
    IsIntegrallyClosed (criticalObservationChartRing K m n) :=
  isIntegrallyClosed_of_isLocalization _
    (Submonoid.powers (criticalObservationMarked K (m := m) (n := n)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (criticalObservationMarked_ne_zero K))

theorem algebraMap_chartRing_invSelf :
    algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
        (IsLocalization.Away.invSelf (criticalObservationMarked K (m := m) (n := n)))
      = (criticalSourceRaw K m n ⟨m, by have := (Fact.out : 0 < n); omega⟩ *
          criticalSourceRecip K m n ⟨n, by have := (Fact.out : 0 < m); omega⟩)⁻¹ := by
  have hmul := IsLocalization.Away.mul_invSelf
    (S := criticalObservationChartRing K m n) (criticalObservationMarked K (m := m) (n := n))
  have := congrArg (algebraMap (criticalObservationChartRing K m n)
    (criticalSourceField K m n)) hmul
  rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply,
    algebraMap_criticalObservationMarked K] at this
  exact eq_inv_of_mul_eq_one_right this

theorem criticalObservationChart_subset_range (hm : 0 < m) (hn : 0 < n) :
    criticalObservationChart K hm hn ⊆
      ((algebraMap (criticalObservationChartRing K m n)
        (criticalSourceField K m n)).range : Set (criticalSourceField K m n)) := by
  have hmarkraw := criticalSourceRaw_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n)
  have hmarkrec := criticalSourceRecip_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n)
  have hbase : ∀ p : criticalObservationRing K m n,
      algebraMap (criticalObservationRing K m n) (criticalSourceField K m n) p ∈
        (algebraMap (criticalObservationChartRing K m n)
          (criticalSourceField K m n)).range := by
    intro p
    exact ⟨algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n) p,
      (IsScalarTower.algebraMap_apply _ _ _ p).symm⟩
  rintro x (((⟨i, rfl⟩) | (⟨j, rfl⟩)) | hx)
  · dsimp only
    rw [← algebraMap_criticalObservationRing_X_inl K i]; exact hbase _
  · dsimp only
    rw [← algebraMap_criticalObservationRing_X_inr K j]; exact hbase _
  · rcases hx with rfl | rfl
    · refine ⟨IsLocalization.Away.invSelf (criticalObservationMarked K (m := m) (n := n)) *
        algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n)
          (MvPolynomial.X (Sum.inr (⟨0, Fact.out⟩ : Fin m))), ?_⟩
      rw [map_mul, algebraMap_chartRing_invSelf K, ← IsScalarTower.algebraMap_apply,
        algebraMap_criticalObservationRing_X_inr K]
      have hcast : (⟨n + ((⟨0, Fact.out⟩ : Fin m) : ℕ), by
          have := (Fact.out : 0 < m); omega⟩ : Fin (m + n))
          = ⟨n, by have := (Fact.out : 0 < m); omega⟩ := Fin.ext (by simp)
      rw [hcast]
      field_simp
    · refine ⟨IsLocalization.Away.invSelf (criticalObservationMarked K (m := m) (n := n)) *
        algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n)
          (MvPolynomial.X (Sum.inl (⟨0, Fact.out⟩ : Fin n))), ?_⟩
      rw [map_mul, algebraMap_chartRing_invSelf K, ← IsScalarTower.algebraMap_apply,
        algebraMap_criticalObservationRing_X_inl K]
      have hcast : (⟨m + ((⟨0, Fact.out⟩ : Fin n) : ℕ), by
          have := (Fact.out : 0 < n); omega⟩ : Fin (m + n))
          = ⟨m, by have := (Fact.out : 0 < n); omega⟩ := Fin.ext (by simp)
      rw [hcast]
      field_simp

/-- **Every horizon coordinate is integral over the chart ring.** -/
theorem criticalSourceCoordinate_isIntegral_chartRing :
    ∀ x ∈ criticalSourceCoordinateSet K m n,
      IsIntegral (criticalObservationChartRing K m n) x := by
  have hm : (0 : ℕ) < m := Fact.out
  have hn : (0 : ℕ) < n := Fact.out
  have hlow := criticalSourceLow_isIntegral_subring K hm hn
    (algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)).range
    (criticalObservationChart_subset_range K hm hn)
  rintro x ((⟨j, rfl⟩) | (⟨j, rfl⟩))
  · by_cases hj : (j : ℕ) < m
    · have := hlow.1 ⟨(j : ℕ), hj⟩
      exact isIntegral_of_isIntegral_range (by simpa using this)
    · have hj' : (j : ℕ) - m < n := by omega
      have hx : criticalSourceRaw K m n j
          = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
            (MvPolynomial.X (Sum.inl (⟨(j : ℕ) - m, hj'⟩ : Fin n))) := by
        rw [algebraMap_criticalObservationRing_X_inl K]
        congr 1
        exact Fin.ext (by simp; omega)
      rw [hx, IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
        (criticalObservationChartRing K m n) (criticalSourceField K m n)]
      exact isIntegral_algebraMap
  · by_cases hj : (j : ℕ) < n
    · have := hlow.2 ⟨(j : ℕ), hj⟩
      exact isIntegral_of_isIntegral_range (by simpa using this)
    · have hj' : (j : ℕ) - n < m := by omega
      have hx : criticalSourceRecip K m n j
          = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
            (MvPolynomial.X (Sum.inr (⟨(j : ℕ) - n, hj'⟩ : Fin m))) := by
        rw [algebraMap_criticalObservationRing_X_inr K]
        congr 1
        exact Fin.ext (by simp; omega)
      rw [hx, IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
        (criticalObservationChartRing K m n) (criticalSourceField K m n)]
      exact isIntegral_algebraMap

/-- The chart algebra: the horizon coordinates adjoined to the chart ring. -/
noncomputable def criticalSourceChartAlgebra :
    Subalgebra (criticalObservationChartRing K m n) (criticalSourceField K m n) :=
  Algebra.adjoin (criticalObservationChartRing K m n) (criticalSourceCoordinateSet K m n)

instance criticalSourceChartAlgebra_isIntegral :
    Algebra.IsIntegral (criticalObservationChartRing K m n)
      (criticalSourceChartAlgebra K (m := m) (n := n)) :=
  Algebra.IsIntegral.adjoin (criticalSourceCoordinate_isIntegral_chartRing K)

end

end GaloisForLFunctions.HTGeometry
