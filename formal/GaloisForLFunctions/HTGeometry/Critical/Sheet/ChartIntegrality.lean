import GaloisForLFunctions.HTGeometry.Critical.Schur.SheetLift
import GaloisForLFunctions.HTGeometry.Critical.Schur.ChartInclusion
import GaloisForLFunctions.HTGeometry.Critical.Schur.NormalFibreReduction
import GaloisForLFunctions.HTGeometry.Critical.Schur.ChartClearing

/-!
# Sheets keep the chart algebra integral at the Schur place

Every geometric sheet maps the chart algebra into the chosen normal-closure Schur valuation ring:
the low coordinates are integral because the marked residue does not vanish, the high coordinates
come from the observation field, and the chart ring itself is a quotient of two observation
elements.

This is the first step of the reduced-fibre dictionary: it makes the pullback of the
normal-closure valuation along a sheet a valuation ring containing the chart algebra.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)]

/-- An element of the source field that comes from the observation field and is integral at the
Schur place stays integral along every sheet. -/
theorem sheet_mem_normalClosureSchur_of_observationRange
    (σ : criticalGeometricSheet K m n) {y : criticalObservationField K m n}
    (hyB : algebraMap (criticalObservationField K m n) (criticalSourceField K m n) y
      ∈ criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    σ (algebraMap (criticalObservationField K m n) (criticalSourceField K m n) y)
      ∈ criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) := by
  have hy : y ∈ criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n) :=
    (mem_criticalSchurObservationValuationSubring_iff K _ _ y).mpr hyB
  have hcomm : σ (algebraMap (criticalObservationField K m n)
      (criticalSourceField K m n) y)
      = criticalObservationNormalClosureMap K m n y := σ.commutes y
  rw [hcomm]
  exact criticalNormalClosureSchurValuationSubring_observation_mem K _ _ ⟨y, hy⟩

/-- Every raw source coordinate stays integral along every sheet. -/
theorem criticalSourceRaw_sheet_mem_normalClosureSchur
    (hm : 1 < m) (hn : 1 < n) (σ : criticalGeometricSheet K m n) (j : Fin (m + n)) :
    σ (criticalSourceRaw K m n j)
      ∈ criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) := by
  by_cases hj : (j : ℕ) < m
  · have hcoeff := (criticalGeometricSheetToSchurFieldFibre_coefficients_mem K hm hn
      (criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ)).1 ⟨(j : ℕ), hj⟩
    have hval : ((criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ).1.1).coeff
        (j : ℕ) = σ (criticalSourceRaw K m n j) := by
      change ((criticalSourceRawLow K m n).map σ.toRingHom).coeff (j : ℕ) = _
      rw [Polynomial.coeff_map, criticalSourceRawLow, lowPolynomial_coeff, dif_pos hj]
      congr 1
    rw [← hval]
    exact hcoeff
  · have hj' : (j : ℕ) - m < n := by have := j.isLt; omega
    have hx : criticalSourceRaw K m n j
        = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
          (MvPolynomial.X (Sum.inl (⟨(j : ℕ) - m, hj'⟩ : Fin n))) := by
      rw [algebraMap_criticalObservationRing_X_inl K]
      congr 1
      exact Fin.ext (by simp; omega)
    rw [hx, IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationField K m n) (criticalSourceField K m n)]
    refine sheet_mem_normalClosureSchur_of_observationRange K σ ?_
    rw [← IsScalarTower.algebraMap_apply, ← hx]
    exact criticalSourceCoordinateSet_subset_schur K (Or.inl ⟨j, rfl⟩)

/-- Every reciprocal source coordinate stays integral along every sheet. -/
theorem criticalSourceRecip_sheet_mem_normalClosureSchur
    (hm : 1 < m) (hn : 1 < n) (σ : criticalGeometricSheet K m n) (j : Fin (m + n)) :
    σ (criticalSourceRecip K m n j)
      ∈ criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) := by
  by_cases hj : (j : ℕ) < n
  · have hcoeff := (criticalGeometricSheetToSchurFieldFibre_coefficients_mem K hm hn
      (criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ)).2 ⟨(j : ℕ), hj⟩
    have hval : ((criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ).1.2).coeff
        (j : ℕ) = σ (criticalSourceRecip K m n j) := by
      change ((criticalSourceReciprocalLow K m n).map σ.toRingHom).coeff (j : ℕ) = _
      rw [Polynomial.coeff_map, criticalSourceReciprocalLow, lowPolynomial_coeff, dif_pos hj]
      congr 1
    rw [← hval]
    exact hcoeff
  · have hj' : (j : ℕ) - n < m := by have := j.isLt; omega
    have hx : criticalSourceRecip K m n j
        = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
          (MvPolynomial.X (Sum.inr (⟨(j : ℕ) - n, hj'⟩ : Fin m))) := by
      rw [algebraMap_criticalObservationRing_X_inr K]
      congr 1
      exact Fin.ext (by simp; omega)
    rw [hx, IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationField K m n) (criticalSourceField K m n)]
    refine sheet_mem_normalClosureSchur_of_observationRange K σ ?_
    rw [← IsScalarTower.algebraMap_apply, ← hx]
    exact criticalSourceCoordinateSet_subset_schur K (Or.inr ⟨j, rfl⟩)

/-- Every element of the chart ring is the image of an element of the observation field. -/
theorem algebraMap_chartRing_mem_observationRange (c : criticalObservationChartRing K m n) :
    ∃ y : criticalObservationField K m n,
      algebraMap (criticalObservationField K m n) (criticalSourceField K m n) y
        = algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) c := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj
    (M := Submonoid.powers (criticalObservationMarked K (m := m) (n := n)))
    (S := criticalObservationChartRing K m n) c
  obtain ⟨k, hk⟩ := s.2
  have himg := congrArg (algebraMap (criticalObservationChartRing K m n)
    (criticalSourceField K m n)) hs
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at himg
  have hsval : algebraMap (criticalObservationRing K m n) (criticalSourceField K m n) (s : _)
      = criticalSourceMarked K (m := m) (n := n) ^ k := by
    rw [← hk, map_pow]
  have hne : criticalSourceMarked K (m := m) (n := n) ≠ 0 := by
    rw [criticalSourceMarked_eq K]
    exact mul_ne_zero
      (criticalSourceRaw_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSourceRecip_atMarkedIndex_ne_zero K (Fact.out : 0 < m) (Fact.out : 0 < n))
  refine ⟨algebraMap (criticalObservationRing K m n) (criticalObservationField K m n) p /
    algebraMap (criticalObservationRing K m n) (criticalObservationField K m n) (s : _), ?_⟩
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hsval]
  rw [hsval] at himg
  rw [← himg, mul_div_assoc, div_self (pow_ne_zero k hne), mul_one]

/-- **Every element of the chart algebra stays integral along every sheet.** -/
theorem criticalSourceChartAlgebra_sheet_mem_normalClosureSchur
    (hm : 1 < m) (hn : 1 < n) (σ : criticalGeometricSheet K m n)
    {t : criticalSourceField K m n}
    (ht : t ∈ criticalSourceChartAlgebra K (m := m) (n := n)) :
    σ t ∈ criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n) := by
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact criticalSourceRaw_sheet_mem_normalClosureSchur K hm hn σ j
      · exact criticalSourceRecip_sheet_mem_normalClosureSchur K hm hn σ j
  | algebraMap c =>
      obtain ⟨y, hy⟩ := algebraMap_chartRing_mem_observationRange K c
      rw [← hy]
      refine sheet_mem_normalClosureSchur_of_observationRange K σ ?_
      rw [hy]
      exact chartRing_mem_schur K hm hn c
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subring.mul_mem _ hx hy

end

end GaloisForLFunctions.HTGeometry
