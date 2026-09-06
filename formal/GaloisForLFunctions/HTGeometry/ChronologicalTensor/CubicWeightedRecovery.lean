import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicWeightedProfile

/-!
# Exact weighted minimax problem for every missing homogeneous mode

The actual missing observation at weight k+1 is u^k c. A homogeneous residual
comes from an available cusp observation exactly when its coefficient at
u^k c is one. The set of all physical recovery errors equals the set of
weighted suprema over all univariate polynomials of degree at most k+1
whose coefficient at degree k is one. No optimal higher-weight value is
asserted here.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
open scoped BigOperators


theorem cubicDehomogeneousPolynomial_range (k : ℕ) :
    Set.range (cubicDehomogeneousPolynomial k)=
      {R : Polynomial ℝ | R.natDegree ≤ k} := by
  ext R
  constructor
  · rintro ⟨α,rfl⟩
    exact cubicDehomogeneousPolynomial_degree k α
  · intro hR
    refine ⟨fun i => R.coeff i.val,?_⟩
    ext n
    by_cases hn : n<k+1
    · exact cubicDehomogeneousPolynomial_coefficient k (fun i => R.coeff i.val) ⟨n,hn⟩
    · have hnk : k<n := by omega
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero.mp
        (cubicDehomogeneousPolynomial_degree k _) n hnk,
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp hR n hnk]

def cubicMissingIndex (k : ℕ) : Fin (k+2) := ⟨k,by omega⟩

def cubicMissingCoefficients (k : ℕ) : Fin (k+2) → ℝ :=
  fun i => if i=cubicMissingIndex k then 1 else 0

def cubicHomogeneousMissing (k : ℕ) : cubicHomogeneousSpace (k+1) :=
  (cubicHomogeneousCoordinatesEquiv (k+1)).symm (cubicMissingCoefficients k)

theorem cubicHomogeneousMissing_polynomial (k : ℕ) :
    (cubicHomogeneousMissing k).val=Polynomial.monomial 1 (Polynomial.monomial k (1:ℝ)) := by
  change cubicHomogeneousPolynomial (k+1) (cubicMissingCoefficients k)=_
  unfold cubicHomogeneousPolynomial
  rw [Finset.sum_eq_single (cubicMissingIndex k)]
  · have hk : k+1-k=1 := by omega
    simp [cubicMissingCoefficients,cubicMissingIndex,hk]
  · intro i hi hne
    simp [cubicMissingCoefficients,hne]
  · simp

theorem cubicHomogeneousMissing_observation (k : ℕ) (g : cubicProbeSection) :
    cubicPolynomialObservation (cubicHomogeneousMissing k).val g=
      (cubicDecayMode 0 g.val)^k*g.val 2 := by
  rw [cubicHomogeneousMissing_polynomial]
  change Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 g.val)) (g.val 2)
    (Polynomial.monomial 1 (Polynomial.monomial k (1:ℝ)))=_
  simp only [Polynomial.eval₂_monomial,Polynomial.coe_evalRingHom,
    Polynomial.eval_monomial,one_mul,pow_one]

theorem cubicHomogeneousMissing_coordinates (k : ℕ) :
    cubicHomogeneousCoordinates (k+1) (cubicHomogeneousMissing k)=cubicMissingCoefficients k :=
  (cubicHomogeneousCoordinatesEquiv (k+1)).apply_symm_apply _

theorem cubicHomogeneousResidual_constraint (k : ℕ) (R : cubicHomogeneousSpace (k+1)) :
    (cubicHomogeneousMissing k-R).val ∈ cubicCuspAlgebra ↔
      cubicHomogeneousCoordinates (k+1) R (cubicMissingIndex k)=1 := by
  rw [cubicHomogeneousCoordinates_cusp]
  change (((cubicHomogeneousMissing k).val-R.val).coeff (k+1-k)).coeff k=0 ↔ _
  rw [Polynomial.coeff_sub,Polynomial.coeff_sub]
  change cubicHomogeneousCoordinates (k+1) (cubicHomogeneousMissing k) (cubicMissingIndex k)-
    cubicHomogeneousCoordinates (k+1) R (cubicMissingIndex k)=0 ↔ _
  rw [cubicHomogeneousMissing_coordinates]
  simp only [cubicMissingCoefficients,ite_true]
  constructor <;> intro h <;> linarith

def cubicHomogeneousRecoveryErrors (k : ℕ) : Set ℝ :=
  cubicHomogeneousCapacity (k+1) ''
    {R : cubicHomogeneousSpace (k+1) | (cubicHomogeneousMissing k-R).val ∈ cubicCuspAlgebra}

theorem cubicHomogeneousRecoveryErrors_weighted (k : ℕ) :
    cubicHomogeneousRecoveryErrors k=
      cubicWeightedPolynomialNorm (k+1) ''
        {α : Fin (k+2) → ℝ | α (cubicMissingIndex k)=1} := by
  ext y
  constructor
  · rintro ⟨R,hR,rfl⟩
    refine ⟨cubicHomogeneousCoordinates (k+1) R,
      (cubicHomogeneousResidual_constraint k R).mp hR,?_⟩
    rw [← cubicHomogeneousCapacity_weighted]
    change cubicHomogeneousCapacity (k+1)
      ((cubicHomogeneousCoordinatesEquiv (k+1)).symm ((cubicHomogeneousCoordinatesEquiv (k+1)) R))=_
    rw [LinearEquiv.symm_apply_apply]
  · rintro ⟨α,hα,rfl⟩
    refine ⟨(cubicHomogeneousCoordinatesEquiv (k+1)).symm α,?_,
      cubicHomogeneousCapacity_weighted (k+1) α⟩
    change (cubicHomogeneousMissing k-(cubicHomogeneousCoordinatesEquiv (k+1)).symm α).val ∈ cubicCuspAlgebra
    rw [cubicHomogeneousResidual_constraint]
    change ((cubicHomogeneousCoordinatesEquiv (k+1))
      ((cubicHomogeneousCoordinatesEquiv (k+1)).symm α)) (cubicMissingIndex k)=1
    rw [LinearEquiv.apply_symm_apply]
    exact hα


theorem cubicHomogeneousRecoveryErrors_polynomial (k : ℕ) :
    cubicHomogeneousRecoveryErrors k=
      (fun R : Polynomial ℝ =>
        sSup ((fun c : ℝ => c^(k+1)*|R.eval (cubicEdgeRatio c)|) '' Icc 0 1)) ''
          {R : Polynomial ℝ | R.natDegree ≤ k+1 ∧ R.coeff k=1} := by
  rw [cubicHomogeneousRecoveryErrors_weighted]
  ext y
  constructor
  · rintro ⟨α,hα,rfl⟩
    refine ⟨cubicDehomogeneousPolynomial (k+1) α,⟨cubicDehomogeneousPolynomial_degree (k+1) α,?_⟩,rfl⟩
    exact (cubicDehomogeneousPolynomial_coefficient (k+1) α (cubicMissingIndex k)).trans hα
  · rintro ⟨R,⟨hR,hc⟩,rfl⟩
    have hrange : R ∈ Set.range (cubicDehomogeneousPolynomial (k+1)) := by
      rw [cubicDehomogeneousPolynomial_range]
      exact hR
    obtain ⟨α,rfl⟩ := hrange
    refine ⟨α,?_,rfl⟩
    exact (cubicDehomogeneousPolynomial_coefficient (k+1) α (cubicMissingIndex k)).symm.trans hc

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
