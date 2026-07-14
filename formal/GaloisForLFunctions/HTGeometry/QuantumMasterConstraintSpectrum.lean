import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage
import GaloisForLFunctions.HTGeometry.SingularValues
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Spectral sum rules for bounded quantum master constraints

The bounded master constraint `C†C` is exactly the energy operator already used to construct the
singular values of a compact operator.  This file joins those two previously separate APIs.  It
removes the repeated compactness/symmetry/positivity premises from greedy spectral exhaustion of a
master constraint and identifies its trace with both Hilbert--Schmidt constraint energy and the
sum of its greedy spectral values.
-/

open scoped InnerProductSpace ComplexConjugate

namespace HTGeometry

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The quantum master constraint is definitionally the singular-value energy operator. -/
theorem quantumMasterConstraint_eq_energyOp (C : H →L[ℂ] H) :
    quantumMasterConstraint C = ContinuousLinearMap.energyOp C := rfl

/-- Compactness of `C` automatically gives compactness of its master constraint. -/
theorem quantumMasterConstraint_isCompactOperator
    {C : H →L[ℂ] H} (hC : IsCompactOperator C) :
    IsCompactOperator (quantumMasterConstraint C) := by
  change IsCompactOperator (ContinuousLinearMap.energyOp C)
  exact ContinuousLinearMap.energyOp_compact hC

/-- The symmetry premise used by the compact greedy spectral machinery is automatic for a master
constraint. -/
theorem quantumMasterConstraint_isSymmetric (C : H →L[ℂ] H) :
    (quantumMasterConstraint C).IsSymmetric := by
  change (ContinuousLinearMap.energyOp C).IsSymmetric
  exact ContinuousLinearMap.energyOp_symmetric C

/-- Every greedy spectral value of `C†C` is exactly the square of the corresponding singular
value of `C`. -/
theorem svVal_quantumMasterConstraint_eq_singVal_sq
    (C : H →L[ℂ] H) (n : ℕ) :
    ContinuousLinearMap.svVal (quantumMasterConstraint C) n =
      ContinuousLinearMap.singVal C n ^ 2 := by
  change ContinuousLinearMap.svVal (ContinuousLinearMap.energyOp C) n =
    ContinuousLinearMap.singVal C n ^ 2
  exact (ContinuousLinearMap.singVal_sq C n).symm

/-- A live greedy master mode is a genuine unit eigenvector.  Compactness of `C` is the only
premise: compactness, symmetry, and positivity of `C†C` are discharged internally. -/
theorem isGreedyStep_svVec_quantumMasterConstraint
    {C : H →L[ℂ] H} (hC : IsCompactOperator C)
    (n : ℕ) (hne : ContinuousLinearMap.svVal (quantumMasterConstraint C) n ≠ 0) :
    ContinuousLinearMap.IsGreedyStep (quantumMasterConstraint C)
      (ContinuousLinearMap.svVec (quantumMasterConstraint C)) n
      (ContinuousLinearMap.svVec (quantumMasterConstraint C) n) := by
  exact ContinuousLinearMap.isGreedyStep_svVec
    (quantumMasterConstraint_isCompactOperator hC)
    (quantumMasterConstraint_isSymmetric C)
    (re_inner_quantumMasterConstraint_nonneg C) n hne

/-- The master spectral values of a compact constraint tend to zero, with no separately supplied
self-adjointness or positivity hypotheses. -/
theorem tendsto_svVal_quantumMasterConstraint_zero
    {C : H →L[ℂ] H} (hC : IsCompactOperator C) :
    Filter.Tendsto
      (ContinuousLinearMap.svVal (quantumMasterConstraint C))
      Filter.atTop (nhds 0) := by
  exact ContinuousLinearMap.svVal_tendsto_zero
    (quantumMasterConstraint_isCompactOperator hC)
    (quantumMasterConstraint_isSymmetric C)
    (re_inner_quantumMasterConstraint_nonneg C)

/-- Completeness of the greedy master modes at the level of the original constraint: a vector
orthogonal to every mode is annihilated by `C`, not merely by `C†C`. -/
theorem constraint_apply_eq_zero_of_forall_inner_masterSvVec
    {C : H →L[ℂ] H} (hC : IsCompactOperator C) {x : H}
    (hx : ∀ n, inner ℂ
      (ContinuousLinearMap.svVec (quantumMasterConstraint C) n) x = 0) :
    C x = 0 := by
  have hmaster : quantumMasterConstraint C x = 0 :=
    ContinuousLinearMap.apply_eq_zero_of_forall_inner_svVec
      (quantumMasterConstraint_isCompactOperator hC)
      (quantumMasterConstraint_isSymmetric C)
      (re_inner_quantumMasterConstraint_nonneg C) hx
  have hmasterState : GaloisForLFunctions.PhysicalState
      (quantumMasterConstraint C).toLinearMap x := by
    simpa only [GaloisForLFunctions.PhysicalState] using hmaster
  have hconstraintState :=
    (physicalState_quantumMasterConstraint_iff C x).mp hmasterState
  simpa only [GaloisForLFunctions.PhysicalState] using hconstraintState

/-- The trace of a Hilbert--Schmidt master constraint is the total squared constraint energy. -/
theorem re_opTrace_quantumMasterConstraint_eq_hsNormSq
    {C : H →L[ℂ] H} (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    RCLike.re (ContinuousLinearMap.opTrace (quantumMasterConstraint C)) =
      ContinuousLinearMap.hsNormSq C := by
  change RCLike.re
      (ContinuousLinearMap.opTrace (ContinuousLinearMap.adjoint C ∘L C)) =
    ContinuousLinearMap.hsNormSq C
  exact ContinuousLinearMap.re_opTrace_adjoint_comp_self hC

/-- **Supersymmetric partner trace equality.**  A Hilbert--Schmidt constraint has equal total
spectral energy in the partner Hamiltonians `C†C` and `CC†`. -/
theorem opTrace_quantumMasterConstraint_eq_partner
    {C : H →L[ℂ] H} (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    ContinuousLinearMap.opTrace (quantumMasterConstraint C) =
      ContinuousLinearMap.opTrace (quantumMasterConstraint C.adjoint) := by
  change ContinuousLinearMap.opTrace (C.adjoint ∘L C) =
    ContinuousLinearMap.opTrace (C.adjoint.adjoint ∘L C.adjoint)
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact ContinuousLinearMap.opTrace_comp_comm hC.adjoint hC

/-- Real-valued form of the supersymmetric partner trace equality. -/
theorem re_opTrace_quantumMasterConstraint_eq_partner
    {C : H →L[ℂ] H} (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    RCLike.re (ContinuousLinearMap.opTrace (quantumMasterConstraint C)) =
      RCLike.re (ContinuousLinearMap.opTrace (quantumMasterConstraint C.adjoint)) := by
  rw [opTrace_quantumMasterConstraint_eq_partner hC]

/-- The Hilbert--Schmidt energy is the sum of the greedy master spectral values. -/
theorem hsNormSq_eq_tsum_svVal_quantumMasterConstraint
    {C : H →L[ℂ] H} (hHS : ContinuousLinearMap.IsHilbertSchmidt C) :
    ContinuousLinearMap.hsNormSq C =
      ∑' n, ContinuousLinearMap.svVal (quantumMasterConstraint C) n := by
  change ContinuousLinearMap.hsNormSq C =
    ∑' n, ContinuousLinearMap.svVal (ContinuousLinearMap.energyOp C) n
  exact ContinuousLinearMap.hsNormSq_eq_tsum_svVal hHS.isCompactOperator hHS

/-- **Master-constraint spectral sum rule.**  The real trace of `C†C`, its Hilbert--Schmidt
constraint energy, and the sum of the squared singular values are one value. -/
theorem re_opTrace_quantumMasterConstraint_eq_tsum_svVal
    {C : H →L[ℂ] H} (hHS : ContinuousLinearMap.IsHilbertSchmidt C) :
    RCLike.re (ContinuousLinearMap.opTrace (quantumMasterConstraint C)) =
      ∑' n, ContinuousLinearMap.svVal (quantumMasterConstraint C) n := by
  rw [re_opTrace_quantumMasterConstraint_eq_hsNormSq hHS]
  exact hsNormSq_eq_tsum_svVal_quantumMasterConstraint hHS

end

end HTGeometry
