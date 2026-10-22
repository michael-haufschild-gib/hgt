import GaloisForLFunctions.HTGeometry.Critical.Observation.JacobianRecip
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.IntegralJacobian

/-!
# The determinant of the observation Jacobian

In the chosen block order the observation Jacobian is `fromBlocks Dᵀ 0 C 1`, so its determinant is
the determinant of the rectangular Schur Toeplitz block — the lifted Jacobian determinant element,
which is a uniformizer of the source Schur valuation ring and therefore not a unit.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing KaehlerDifferential Polynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

omit [IsAlgClosed K] [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalObservationJacobian_eq_fromBlocks :
    criticalObservationJacobian K (m := m) (n := n)
      = Matrix.fromBlocks
          (criticalReciprocalJacobian (criticalSourceRecipPolynomialIntegral K
            (Fact.out : 0 < m) (Fact.out : 0 < n)) n m).transpose
          0
          (Matrix.of fun t s => criticalObservationJacobian K (Sum.inr t) (Sum.inl s))
          1 := by
  refine Matrix.ext fun t s => ?_
  cases t with
  | inl t' =>
      cases s with
      | inl s' =>
          show criticalObservationJacobian K (Sum.inl t') (Sum.inl s') = _
          rw [criticalObservationJacobian_apply_inl K]
          show _ = criticalReciprocalJacobian (criticalSourceRecipPolynomialIntegral K
            (Fact.out : 0 < m) (Fact.out : 0 < n)) n m s' t'
          rw [criticalReciprocalJacobian_apply]
          simp only [rectangularSchurToeplitz]
          have hidx : ((finSumFinEquiv (Sum.inl t') : Fin (m + n)) : ℕ) = (t' : ℕ) := rfl
          rw [hidx]
          by_cases h : (t' : ℕ) ≤ n + (s' : ℕ)
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, neg_zero]
      | inr s' =>
          show criticalObservationJacobian K (Sum.inl t') (Sum.inr s') = _
          show (if (Sum.inl t' : Fin m ⊕ Fin n) = Sum.inr s' then (1 : _) else 0) = _
          rw [if_neg (by simp)]
          rfl
  | inr t' =>
      cases s with
      | inl s' => rfl
      | inr s' =>
          show criticalObservationJacobian K (Sum.inr t') (Sum.inr s') = _
          show (if (Sum.inr t' : Fin m ⊕ Fin n) = Sum.inr s' then (1 : _) else 0) = _
          rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
          by_cases h : t' = s'
          · rw [if_pos (by rw [h]), if_pos h]
          · rw [if_neg (by simpa using h), if_neg h]

omit [IsAlgClosed K] [Fact (1 < m)] [Fact (1 < n)] in
theorem det_criticalObservationJacobian :
    (criticalObservationJacobian K (m := m) (n := n)).det
      = criticalSchurJacobianDetElement K (Fact.out : 0 < m) (Fact.out : 0 < n) := by
  rw [criticalObservationJacobian_eq_fromBlocks K, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one, Matrix.det_transpose,
    det_criticalReciprocalJacobianIntegral K Fact.out Fact.out]

/-- **The observation Jacobian determinant is not a unit at the Schur place.** -/
theorem not_isUnit_det_criticalObservationJacobian :
    ¬ IsUnit (criticalObservationJacobian K (m := m) (n := n)).det := by
  rw [det_criticalObservationJacobian K]
  exact (irreducible_criticalSchurJacobianDetElement K
    (Fact.out : 1 < m) (Fact.out : 1 < n)).not_isUnit

end

end GaloisForLFunctions.HTGeometry
