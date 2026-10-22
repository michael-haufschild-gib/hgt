import GaloisForLFunctions.HTGeometry.Critical.Sheet.Singularity
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Sheet.ConormalVector
import GaloisForLFunctions.HTGeometry.Critical.Sheet.JacobianCorankOne
import GaloisForLFunctions.HTGeometry.HorizonJacobianDeterminant
import GaloisForLFunctions.HTGeometry.HorizonConormalProportional
import GaloisForLFunctions.HTGeometry.Critical.Schur.CollisionSingular
import GaloisForLFunctions.HTGeometry.LowTangentJacobianKernel
import GaloisForLFunctions.HTGeometry.MatrixKernelDeletedColumn
import GaloisForLFunctions.HTGeometry.Critical.Schur.TangentConstantTerm
import GaloisForLFunctions.HTGeometry.CriticalFibreSharedTangentRigidity
import GaloisForLFunctions.HTGeometry.Critical.Schur.MarkedReduction

/-!
# One conormal line for every singular sheet

The branch conormal vector is fixed once and for all, and at every singular sheet the reduced
horizon Jacobian has it as a kernel vector and has corank one.  Consequently every low tangent at
a singular reduced state is a scalar multiple of that one vector.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- A chosen non-unit of the observation Schur place with a unit differential coordinate. -/
noncomputable def criticalSchurBranchNonUnit :
    criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
  Classical.choose (exists_criticalNormalSchurConormalVector_ne_zero K (m := m) (n := n))

theorem criticalSchurBranchNonUnit_mem :
    criticalSchurBranchNonUnit K (m := m) (n := n)
      ∈ maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)) :=
  (Classical.choose_spec
    (exists_criticalNormalSchurConormalVector_ne_zero K (m := m) (n := n))).1

/-- The fixed conormal vector of the branch. -/
noncomputable def criticalSchurFixedConormal :
    Fin m ⊕ Fin n → IsLocalRing.ResidueField
      (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  criticalNormalSchurConormalVector K (criticalSchurBranchNonUnit K (m := m) (n := n))

theorem criticalSchurFixedConormal_ne_zero :
    criticalSchurFixedConormal K (m := m) (n := n) ≠ 0 :=
  (Classical.choose_spec
    (exists_criticalNormalSchurConormalVector_ne_zero K (m := m) (n := n))).2

/-- The reduced raw jet of a sheet at the Schur place. -/
noncomputable def criticalSheetReducedRawPolynomial (σ : criticalGeometricSheet K m n) :
    (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X] :=
  ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.1
    + criticalNormalClosureSchurRawTailIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n)).map
    (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))

/-- The reduced observation Jacobian at a singular sheet is the horizon Jacobian of the reduced
reciprocal jet. -/
theorem criticalSheet_jacobian_eq_horizon_reduced (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    (criticalObservationJacobian K (m := m) (n := n)).map
        ((IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))).comp (criticalSheetSourceSchurLift K σ hsing))
      = horizonObservationJacobian (criticalSheetReducedRecipPolynomial K σ) n m :=
  criticalSheet_jacobian_eq_horizon K σ hsing

/-- **The fixed conormal vector is a kernel vector of the reduced horizon Jacobian at every
singular sheet.** -/
theorem criticalSheet_horizonJacobian_mulVec_fixedConormal (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    (horizonObservationJacobian (criticalSheetReducedRecipPolynomial K σ) n m).mulVec
      (criticalSchurFixedConormal K (m := m) (n := n)) = 0 :=
  criticalSheet_jacobian_eq_horizon_reduced K σ hsing ▸
    criticalSheet_jacobian_mulVec_conormal K σ hsing _ (criticalSchurBranchNonUnit_mem K)

/-- **Corank one for the reduced horizon Jacobian at a singular sheet.** -/
theorem criticalSheet_finrank_ker_horizonJacobian [DecidableEq K]
    (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    Module.finrank
        (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
          (Fact.out : 0 < m) (Fact.out : 0 < n)))
        (LinearMap.ker (horizonObservationJacobian
          (criticalSheetReducedRecipPolynomial K σ) n m).mulVecLin) = 1 :=
  criticalSheet_jacobian_eq_horizon_reduced K σ hsing ▸
    criticalSheet_finrank_ker_reduced_jacobian_eq_one K σ hsing

omit [IsAlgClosed K] in
theorem criticalSheetReducedRawPolynomial_eq (σ : criticalGeometricSheet K m n) :
    criticalSheetReducedRawPolynomial K σ
      = (criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.1
        + (criticalNormalClosureSchurRawTailIntegral K (Fact.out : 0 < m)
            (Fact.out : 0 < n)).map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
            (Fact.out : 0 < m) (Fact.out : 0 < n))) :=
  -- the reduced label is the componentwise reduction, so this is additivity of the reduction map
  Polynomial.map_add _

omit [IsAlgClosed K] in
theorem criticalSheetReducedRecipPolynomial_eq (σ : criticalGeometricSheet K m n) :
    criticalSheetReducedRecipPolynomial K σ
      = (criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
        + (criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
            (Fact.out : 0 < n)).map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
            (Fact.out : 0 < m) (Fact.out : 0 < n))) :=
  Polynomial.map_add _

omit [IsAlgClosed K] in
theorem criticalSheetReducedRawPolynomial_eq' (σ : criticalGeometricSheet K m n) :
    criticalSheetReducedRawPolynomial K σ
      = (criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.1.map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
            (Fact.out : 0 < m) (Fact.out : 0 < n)))
        + (criticalNormalClosureSchurRawTailIntegral K (Fact.out : 0 < m)
            (Fact.out : 0 < n)).map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
            (Fact.out : 0 < m) (Fact.out : 0 < n))) :=
  Polynomial.map_add _

omit [IsAlgClosed K] in
theorem criticalSheetReducedRecipPolynomial_eq' (σ : criticalGeometricSheet K m n) :
    criticalSheetReducedRecipPolynomial K σ
      = (criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2.map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
            (Fact.out : 0 < m) (Fact.out : 0 < n)))
        + (criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
            (Fact.out : 0 < n)).map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
            (Fact.out : 0 < m) (Fact.out : 0 < n))) :=
  Polynomial.map_add _

omit [IsAlgClosed K] in
/-- The reduced jets of a sheet are inverse to each other through the horizon. -/
theorem criticalSheet_reduced_inv (σ : criticalGeometricSheet K m n) :
    (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ criticalSheetReducedRawPolynomial K σ * criticalSheetReducedRecipPolynomial K σ - 1 := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  rw [criticalSheetReducedRawPolynomial_eq, criticalSheetReducedRecipPolynomial_eq]
  exact (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
    (X_pow_dvd_reduced_criticalNormalClosureSchurRawTailIntegral K hfm
      hfn)
    (X_pow_dvd_reduced_criticalNormalClosureSchurReciprocalTailIntegral K hfm
      hfn) _ _).mp
      (criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m)
        (Fact.out : 1 < n) σ).2.2.2

/-- **Every low tangent at a singular sheet is a scalar multiple of the fixed conormal.** -/
theorem criticalSheet_exists_smul_of_tangent [DecidableEq K] (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    {U V : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]}
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ))
    (htan : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ U * criticalSheetReducedRecipPolynomial K σ
        + criticalSheetReducedRawPolynomial K σ * V) :
    ∃ c : IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)),
      horizonConormalVector U V m n = c • criticalSchurFixedConormal K (m := m) (n := n) := by
  refine exists_smul_of_finrank_ker_eq_one _
    (criticalSheet_finrank_ker_horizonJacobian K σ hsing)
    (criticalSheet_horizonJacobian_mulVec_fixedConormal K σ hsing)
    (horizonObservationJacobian_mulVec_conormal (criticalSheet_reduced_inv K σ) hU hV htan)
    (criticalSchurFixedConormal_ne_zero K)
end

end GaloisForLFunctions.HTGeometry
