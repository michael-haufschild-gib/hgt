import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHomogeneousMetric

/-!
# A positive attained recovery gap at every homogeneous weight

Normalized residuals form a nonempty closed affine set in the finite-dimensional
physical norm. Properness gives a least-norm residual. Its fixed missing
coefficient excludes zero, so the minimum is strictly positive. The gap is the
actual infimum of all recovery errors and is attained. Uniqueness of the
optimizer is not asserted by this compactness argument.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicNormalizedResiduals (k : ℕ) : Set (cubicHomogeneousSpace (k+1)) :=
  {R | cubicHomogeneousCoordinates (k+1) R (cubicMissingIndex k)=1}

theorem cubicNormalizedResiduals_nonempty (k : ℕ) : (cubicNormalizedResiduals k).Nonempty := by
  refine ⟨cubicHomogeneousMissing k,?_⟩
  change cubicHomogeneousCoordinates (k+1) (cubicHomogeneousMissing k) (cubicMissingIndex k)=1
  rw [cubicHomogeneousMissing_coordinates]
  simp only [cubicMissingCoefficients,ite_true]

theorem cubicNormalizedResiduals_mem (k : ℕ) (R : cubicHomogeneousSpace (k+1)) :
    R ∈ cubicNormalizedResiduals k ↔ (cubicHomogeneousMissing k-R).val ∈ cubicCuspAlgebra :=
  (cubicHomogeneousResidual_constraint k R).symm

theorem cubicNormalizedResiduals_closed (k : ℕ) :
    letI := cubicHomogeneousNormedGroup (k+1)
    IsClosed (cubicNormalizedResiduals k) := by
  letI := cubicHomogeneousNormedGroup (k+1)
  exact isClosed_eq ((continuous_apply (cubicMissingIndex k)).comp
    (cubicHomogeneousCoordinates_continuous (k+1))) continuous_const

theorem cubicNormalizedResiduals_positiveMinimum (k : ℕ) :
    ∃ R ∈ cubicNormalizedResiduals k, 0<cubicHomogeneousCapacity (k+1) R ∧
      ∀ S ∈ cubicNormalizedResiduals k,
        cubicHomogeneousCapacity (k+1) R ≤ cubicHomogeneousCapacity (k+1) S := by
  letI := cubicHomogeneousNormedGroup (k+1)
  letI := cubicHomogeneousSpace_proper (k+1)
  obtain ⟨R,hR,hmin⟩ := (cubicNormalizedResiduals_closed k).exists_infDist_eq_dist
    (cubicNormalizedResiduals_nonempty k) (0 : cubicHomogeneousSpace (k+1))
  have hne : R ≠ 0 := by
    intro hz
    subst R
    change (((0 : Polynomial (Polynomial ℝ)).coeff (k+1-k)).coeff k)=1 at hR
    simp only [Polynomial.coeff_zero] at hR
    exact zero_ne_one hR
  refine ⟨R,hR,?_,?_⟩
  · exact lt_of_le_of_ne (cubicHomogeneousCapacity_nonneg (k+1) R)
      (fun h => hne ((cubicHomogeneousCapacity_definite (k+1) R).mp h.symm))
  · intro S hS
    have hb := Metric.infDist_le_dist_of_mem (x := (0 : cubicHomogeneousSpace (k+1))) hS
    rw [hmin,dist_zero_left,dist_zero_left] at hb
    exact hb

theorem cubicHomogeneousRecoveryErrors_positiveLeast (k : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ IsLeast (cubicHomogeneousRecoveryErrors k) δ := by
  obtain ⟨R,hR,hpos,hmin⟩ := cubicNormalizedResiduals_positiveMinimum k
  refine ⟨cubicHomogeneousCapacity (k+1) R,hpos,?_,?_⟩
  · exact ⟨R,(cubicNormalizedResiduals_mem k R).mp hR,rfl⟩
  · rintro y ⟨S,hS,rfl⟩
    exact hmin S ((cubicNormalizedResiduals_mem k S).mpr hS)

def cubicGradedRecoveryGap (k : ℕ) : ℝ := sInf (cubicHomogeneousRecoveryErrors k)

theorem cubicGradedRecoveryGap_isLeast (k : ℕ) :
    IsLeast (cubicHomogeneousRecoveryErrors k) (cubicGradedRecoveryGap k) := by
  obtain ⟨δ,hδ,hmin⟩ := cubicHomogeneousRecoveryErrors_positiveLeast k
  change IsLeast _ (sInf _)
  rw [hmin.csInf_eq]
  exact hmin

theorem cubicGradedRecoveryGap_positive (k : ℕ) : 0<cubicGradedRecoveryGap k := by
  obtain ⟨δ,hδ,hmin⟩ := cubicHomogeneousRecoveryErrors_positiveLeast k
  change 0<sInf _
  rw [hmin.csInf_eq]
  exact hδ

theorem cubicGradedRecoveryGap_attained (k : ℕ) :
    ∃ R ∈ cubicNormalizedResiduals k,
      cubicHomogeneousCapacity (k+1) R=cubicGradedRecoveryGap k := by
  obtain ⟨R,hR,he⟩ := (cubicGradedRecoveryGap_isLeast k).1
  exact ⟨R,(cubicNormalizedResiduals_mem k R).mpr hR,he⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
