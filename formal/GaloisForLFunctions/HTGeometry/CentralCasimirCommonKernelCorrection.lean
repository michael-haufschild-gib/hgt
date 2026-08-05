import GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir
import GaloisForLFunctions.HTGeometry.CentralCasimirHallExpansion
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Adding one Hermitian defect projector that annihilates a central-Casimir
family yields an exact Hall law modulo the projector's target sector. -/
theorem centralHermitianMatrixFamily_subspace_finrank_mod_defect
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) (P : Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hPsymm : P.conjTranspose = P)
    (hcentral : ∀ j,
      (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (hAP : ∀ j, A j * P = 0)
    (hPA : ∀ j, P * A j = 0)
    (hker : ∀ x : EuclideanSpace 𝕜 X,
      (∀ j, (A j).toEuclideanLin x = 0) →
      P.toEuclideanLin x = 0 → x = 0)
    (U V S : Submodule 𝕜 (EuclideanSpace 𝕜 X))
    (hUV : ∀ j x, x ∈ U → (A j).toEuclideanLin x ∈ V)
    (hPS : ∀ x, x ∈ U → P.toEuclideanLin x ∈ S) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V + Module.finrank 𝕜 S := by
  classical
  let B : Option J → Matrix X X 𝕜
    | none => P
    | some j => A j
  have hBsymm : ∀ q, (B q).conjTranspose = B q := by
    intro q
    cases q with
    | none => exact hPsymm
    | some j => exact hsymm j
  have hBcentral : ∀ q,
      (∑ r, B r * B r) * B q = B q * (∑ r, B r * B r) := by
    intro q
    rw [Fintype.sum_option]
    cases q with
    | none =>
        change (P * P + ∑ j, A j * A j) * P =
          P * (P * P + ∑ j, A j * A j)
        rw [Matrix.add_mul, Matrix.mul_add]
        congr 1
        · noncomm_ring
        · rw [Finset.sum_mul, Matrix.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [show (A j * A j) * P = A j * (A j * P) by noncomm_ring,
            hAP, Matrix.mul_zero]
          rw [show P * (A j * A j) = (P * A j) * A j by noncomm_ring,
            hPA, Matrix.zero_mul]
    | some j =>
        change (P * P + ∑ k, A k * A k) * A j =
          A j * (P * P + ∑ k, A k * A k)
        rw [Matrix.add_mul, Matrix.mul_add]
        rw [show (P * P) * A j = P * (P * A j) by noncomm_ring,
          hPA, Matrix.mul_zero]
        rw [show A j * (P * P) = (A j * P) * P by noncomm_ring,
          hAP, Matrix.zero_mul]
        simpa using hcentral j
  have hBker : ∀ x : EuclideanSpace 𝕜 X,
      (∀ q, (B q).toEuclideanLin x = 0) → x = 0 := by
    intro x hx
    apply hker x
    · intro j
      simpa [B] using hx (some j)
    · simpa [B] using hx none
  let W : Submodule 𝕜 (EuclideanSpace 𝕜 X) := V ⊔ S
  have hBUW : ∀ q x, x ∈ U → (B q).toEuclideanLin x ∈ W := by
    intro q x hx
    cases q with
    | none =>
        exact Submodule.mem_sup_right (hPS x hx)
    | some j =>
        exact Submodule.mem_sup_left (hUV j x hx)
  have hHall : Module.finrank 𝕜 U ≤ Module.finrank 𝕜 W :=
    centralHermitianMatrixFamily_subspace_finrank_of_commonKernel
      B hBsymm hBcentral hBker U W hBUW
  exact le_trans hHall (Submodule.finrank_add_le_finrank_add_finrank V S)

/-- Simultaneous kernel of a finite matrix family acting on Euclidean space. -/
def hermitianMatrixFamilyCommonKernel
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) :
    Submodule 𝕜 (EuclideanSpace 𝕜 X) :=
  ⨅ j, LinearMap.ker (A j).toEuclideanLin

/-- Canonical orthogonal projector onto the simultaneous kernel. -/
def hermitianMatrixFamilyCommonKernelProjection
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) : Matrix X X 𝕜 :=
  (Matrix.toEuclideanCLM (n := X) (𝕜 := 𝕜)).symm
    (hermitianMatrixFamilyCommonKernel A).starProjection

theorem hermitianMatrixFamilyCommonKernelProjection_apply
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) (x : EuclideanSpace 𝕜 X) :
    (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x =
      (hermitianMatrixFamilyCommonKernel A).starProjection x := by
  change Matrix.toEuclideanCLM
      (n := X) (𝕜 := 𝕜)
      (hermitianMatrixFamilyCommonKernelProjection A) x = _
  rw [hermitianMatrixFamilyCommonKernelProjection,
    StarAlgEquiv.apply_symm_apply]

theorem hermitianMatrixFamilyCommonKernelProjection_conjTranspose
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) :
    (hermitianMatrixFamilyCommonKernelProjection A).conjTranspose =
      hermitianMatrixFamilyCommonKernelProjection A := by
  have hself := isSelfAdjoint_starProjection
    (hermitianMatrixFamilyCommonKernel A)
  have h := congrArg
    (Matrix.toEuclideanCLM (n := X) (𝕜 := 𝕜)).symm hself
  simpa [hermitianMatrixFamilyCommonKernelProjection,
    Matrix.star_eq_conjTranspose, map_star] using h

theorem hermitianMatrixFamily_mul_commonKernelProjection_eq_zero
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜) (j : J) :
    A j * hermitianMatrixFamilyCommonKernelProjection A = 0 := by
  apply (Matrix.toEuclideanCLM (n := X) (𝕜 := 𝕜)).injective
  rw [map_mul, map_zero]
  apply ContinuousLinearMap.ext
  intro x
  change (A j).toEuclideanLin
      ((hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x) = 0
  rw [hermitianMatrixFamilyCommonKernelProjection_apply]
  have hx : (hermitianMatrixFamilyCommonKernel A).starProjection x ∈
      hermitianMatrixFamilyCommonKernel A :=
    (hermitianMatrixFamilyCommonKernel A).starProjection_apply_mem x
  have hxj : (hermitianMatrixFamilyCommonKernel A).starProjection x ∈
      LinearMap.ker (A j).toEuclideanLin :=
    (Submodule.mem_iInf _).1 hx j
  exact hxj

theorem hermitianMatrixFamily_commonKernelProjection_mul_eq_zero
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (j : J) :
    hermitianMatrixFamilyCommonKernelProjection A * A j = 0 := by
  have h := congrArg Matrix.conjTranspose
    (hermitianMatrixFamily_mul_commonKernelProjection_eq_zero A j)
  simpa [Matrix.conjTranspose_mul,
    hermitianMatrixFamilyCommonKernelProjection_conjTranspose A,
    hsymm j] using h

/-- Central-Casimir Hall expansion on every mixed subspace, with the exact
simultaneous-kernel dimension as the only correction. -/
theorem centralHermitianMatrixFamily_subspace_finrank_mod_commonKernel
    {𝕜 X J : Type*} [RCLike 𝕜]
    [Fintype X] [DecidableEq X] [Fintype J]
    (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hcentral : ∀ j,
      (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (U V : Submodule 𝕜 (EuclideanSpace 𝕜 X))
    (hUV : ∀ j x, x ∈ U → (A j).toEuclideanLin x ∈ V) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V +
      Module.finrank 𝕜 (hermitianMatrixFamilyCommonKernel A) := by
  let S := hermitianMatrixFamilyCommonKernel A
  let P := hermitianMatrixFamilyCommonKernelProjection A
  refine centralHermitianMatrixFamily_subspace_finrank_mod_defect
    A P hsymm
      (hermitianMatrixFamilyCommonKernelProjection_conjTranspose A)
      hcentral
      (hermitianMatrixFamily_mul_commonKernelProjection_eq_zero A)
      (hermitianMatrixFamily_commonKernelProjection_mul_eq_zero A hsymm)
      ?_ U V S hUV ?_
  · intro x hAx hPx
    have hxS : x ∈ S := by
      change x ∈ ⨅ j, LinearMap.ker (A j).toEuclideanLin
      exact (Submodule.mem_iInf _).2 (fun j => hAx j)
    have hPxx : P.toEuclideanLin x = x := by
      change (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x = x
      rw [hermitianMatrixFamilyCommonKernelProjection_apply]
      exact Submodule.starProjection_eq_self_iff.mpr hxS
    rw [hPxx] at hPx
    exact hPx
  · intro x _
    change (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x ∈ S
    rw [hermitianMatrixFamilyCommonKernelProjection_apply]
    exact S.starProjection_apply_mem x

/-- Sitewise singlet sector for the complete all-replica collective-Pauli
family. -/
def finiteAllReplicaCollectiveSingletSubspace
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  hermitianMatrixFamilyCommonKernel
    (fun p : I × Fin 3 =>
      finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2)

/-- Exact arbitrary-site, arbitrary-replica Hall law on every mixed subspace,
modulo only the simultaneous collective-Pauli singlet sector. -/
theorem finiteAllReplicaCollectiveCommutator_subspace_finrank_mod_singlet
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (U V : Submodule ℂ
      (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))
    (hUV : ∀ p : I × Fin 3, ∀ x, x ∈ U →
      (finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2).toEuclideanLin x ∈ V) :
    Module.finrank ℂ U ≤ Module.finrank ℂ V +
      Module.finrank ℂ (finiteAllReplicaCollectiveSingletSubspace I R) := by
  exact centralHermitianMatrixFamily_subspace_finrank_mod_commonKernel
    (fun p : I × Fin 3 =>
      finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2)
    (fun p => finiteAllReplicaCollectiveCommutatorMatrix_conjTranspose
      I R p.1 p.2)
    (fun p => finiteAllReplicaCollectiveCommutator_quadraticCasimir_commutes
      I R p.1 p.2)
    U V hUV

end

end GaloisForLFunctions.HTGeometry
