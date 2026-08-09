import GaloisForLFunctions.HTGeometry.CentralCasimirCommonKernelCorrection

/-!
# Exact Hall expansion off the simultaneous kernel

A Hermitian matrix family with central quadratic Casimir expands every subspace of the orthogonal
complement of its simultaneous kernel: no dimension correction is needed there.  Adjoining the
canonical kernel projector to the family makes its simultaneous kernel trivial while leaving the
Casimir central, and the projector annihilates the complement, so the enlarged family has the same
image span on such subspaces.

Specialised to the arbitrary-site, arbitrary-replica collective Pauli commutators, this is the
exact all-replica Hall law on the complement of the sitewise singlet sector.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝕜 X J : Type*} [RCLike 𝕜] [Fintype X] [DecidableEq X] [Fintype J]

theorem hermitianMatrixFamilyCommonKernelProjection_mul_self
    (A : J → Matrix X X 𝕜) :
    hermitianMatrixFamilyCommonKernelProjection A *
        hermitianMatrixFamilyCommonKernelProjection A =
      hermitianMatrixFamilyCommonKernelProjection A := by
  apply (Matrix.toEuclideanCLM (n := X) (𝕜 := 𝕜)).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro x
  change (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin
      ((hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x) =
    (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x
  rw [hermitianMatrixFamilyCommonKernelProjection_apply,
    hermitianMatrixFamilyCommonKernelProjection_apply]
  exact Submodule.starProjection_eq_self_iff.mpr
    ((hermitianMatrixFamilyCommonKernel A).starProjection_apply_mem x)

/-- The family completed by the canonical projector onto its simultaneous kernel. -/
def completedHermitianFamily (A : J → Matrix X X 𝕜) : Option J → Matrix X X 𝕜 :=
  fun j => j.elim (hermitianMatrixFamilyCommonKernelProjection A) A

theorem completedHermitianFamily_conjTranspose (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j) (j : Option J) :
    (completedHermitianFamily A j).conjTranspose = completedHermitianFamily A j := by
  cases j with
  | none => exact hermitianMatrixFamilyCommonKernelProjection_conjTranspose A
  | some j => exact hsymm j

theorem completedHermitianFamily_casimir (A : J → Matrix X X 𝕜) :
    (∑ k : Option J, completedHermitianFamily A k * completedHermitianFamily A k) =
      hermitianMatrixFamilyCommonKernelProjection A + ∑ k : J, A k * A k := by
  rw [Fintype.sum_option]
  simp only [completedHermitianFamily, Option.elim]
  rw [hermitianMatrixFamilyCommonKernelProjection_mul_self]

theorem completedHermitianFamily_central (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k)) (j : Option J) :
    (∑ k : Option J, completedHermitianFamily A k * completedHermitianFamily A k) *
        completedHermitianFamily A j =
      completedHermitianFamily A j *
        ∑ k : Option J, completedHermitianFamily A k * completedHermitianFamily A k := by
  classical
  set P : Matrix X X 𝕜 := hermitianMatrixFamilyCommonKernelProjection A with hP
  have hPP : P * P = P := hermitianMatrixFamilyCommonKernelProjection_mul_self A
  have hAP : ∀ j, A j * P = 0 :=
    hermitianMatrixFamily_mul_commonKernelProjection_eq_zero A
  have hPA : ∀ j, P * A j = 0 :=
    hermitianMatrixFamily_commonKernelProjection_mul_eq_zero A hsymm
  have hKP : (∑ k : J, A k * A k) * P = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.mul_assoc, hAP k, Matrix.mul_zero]
  have hPK : P * (∑ k : J, A k * A k) = 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Matrix.mul_assoc, hPA k, Matrix.zero_mul]
  cases j with
  | none =>
      show (∑ k : Option J, completedHermitianFamily A k * completedHermitianFamily A k) * P =
        P * ∑ k : Option J, completedHermitianFamily A k * completedHermitianFamily A k
      rw [completedHermitianFamily_casimir, Matrix.add_mul, Matrix.mul_add, hPP, hKP, hPK,
        add_zero]
  | some j =>
      show (∑ k : Option J, completedHermitianFamily A k * completedHermitianFamily A k) * A j =
        A j * ∑ k : Option J, completedHermitianFamily A k * completedHermitianFamily A k
      rw [completedHermitianFamily_casimir, Matrix.add_mul, Matrix.mul_add, hPA j, hAP j,
        zero_add, zero_add]
      exact hcentral j

theorem completedHermitianFamily_commonKernel_eq_bot (A : J → Matrix X X 𝕜) :
    ∀ x : EuclideanSpace 𝕜 X,
      (∀ j, (completedHermitianFamily A j).toEuclideanLin x = 0) → x = 0 := by
  intro x hx
  have hxS : x ∈ hermitianMatrixFamilyCommonKernel A :=
    (Submodule.mem_iInf _).2 fun j => hx (some j)
  have hPx : (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x = 0 := hx none
  rw [hermitianMatrixFamilyCommonKernelProjection_apply,
    Submodule.starProjection_eq_self_iff.mpr hxS] at hPx
  exact hPx

/-- **Exact bi-tightness of the completed scaled family.**  Scaling the completed family by the
inverse square root of its central Casimir produces an exactly bi-tight self-adjoint family. -/
theorem completedHermitianFamily_scaled_biTight (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k)) :
    (∑ j : Option J,
        (centralCasimirInvSqrtScaleRCLike (completedHermitianFamily A) *
            completedHermitianFamily A j).conjTranspose *
          (centralCasimirInvSqrtScaleRCLike (completedHermitianFamily A) *
            completedHermitianFamily A j) = 1) ∧
    (∑ j : Option J,
        (centralCasimirInvSqrtScaleRCLike (completedHermitianFamily A) *
            completedHermitianFamily A j) *
          (centralCasimirInvSqrtScaleRCLike (completedHermitianFamily A) *
            completedHermitianFamily A j).conjTranspose = 1) := by
  classical
  set B := completedHermitianFamily A with hB
  have hBsymm := completedHermitianFamily_conjTranspose A hsymm
  have hBcentral := completedHermitianFamily_central A hsymm hcentral
  have hBker := completedHermitianFamily_commonKernel_eq_bot A
  obtain ⟨hnonneg, hunit⟩ :=
    hermitianQuadraticCasimir_nonneg_and_isUnit_of_commonKernel B hBsymm hBker
  have hfirst := centralCasimirRCLike_scaled_conjTranspose_mul_sum B hBsymm hnonneg hunit hBcentral
  refine ⟨hfirst, ?_⟩
  have hscaledsymm : ∀ j,
      (centralCasimirInvSqrtScaleRCLike B * B j).conjTranspose =
        centralCasimirInvSqrtScaleRCLike B * B j := by
    intro j
    rw [Matrix.conjTranspose_mul, hBsymm j,
      centralCasimirInvSqrtScaleRCLike_conjTranspose,
      centralCasimirInvSqrtScaleRCLike_commutes B hnonneg hunit hBcentral]
  calc (∑ j : Option J, (centralCasimirInvSqrtScaleRCLike B * B j) *
        (centralCasimirInvSqrtScaleRCLike B * B j).conjTranspose)
      = ∑ j : Option J, (centralCasimirInvSqrtScaleRCLike B * B j).conjTranspose *
          (centralCasimirInvSqrtScaleRCLike B * B j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hscaledsymm j]
    _ = 1 := hfirst

/-- **Exact Hall expansion off the simultaneous kernel.**  A Hermitian family with central
quadratic Casimir needs no dimension correction on subspaces orthogonal to its simultaneous
kernel. -/
theorem centralHermitianMatrixFamily_subspace_finrank_of_orthogonal_commonKernel
    (A : J → Matrix X X 𝕜)
    (hsymm : ∀ j, (A j).conjTranspose = A j)
    (hcentral : ∀ j, (∑ k, A k * A k) * A j = A j * (∑ k, A k * A k))
    (U V : Submodule 𝕜 (EuclideanSpace 𝕜 X))
    (hU : U ≤ (hermitianMatrixFamilyCommonKernel A)ᗮ)
    (hUV : ∀ j x, x ∈ U → (A j).toEuclideanLin x ∈ V) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V := by
  classical
  have hBUV : ∀ j x, x ∈ U → (completedHermitianFamily A j).toEuclideanLin x ∈ V := by
    rintro (_ | j) x hx
    · show (hermitianMatrixFamilyCommonKernelProjection A).toEuclideanLin x ∈ V
      rw [hermitianMatrixFamilyCommonKernelProjection_apply]
      have hzero : (hermitianMatrixFamilyCommonKernel A).starProjection x = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff
          (hermitianMatrixFamilyCommonKernel A)).mpr (hU hx)
      rw [hzero]
      exact V.zero_mem
    · exact hUV j x hx
  exact centralHermitianMatrixFamily_subspace_finrank_of_commonKernel
    (completedHermitianFamily A)
    (completedHermitianFamily_conjTranspose A hsymm)
    (completedHermitianFamily_central A hsymm hcentral)
    (completedHermitianFamily_commonKernel_eq_bot A) U V hBUV

/-- **All-replica collective-Pauli Hall law off the singlet sector.**  For every finite physical
site type, every finite replica type, and every subspace orthogonal to the sitewise singlet
sector, the collective one-site Pauli commutators expand dimension exactly. -/
theorem finiteAllReplicaCollectiveCommutator_subspace_finrank_of_orthogonal_singlet
    (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (U V : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))
    (hU : U ≤ (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ)
    (hUV : ∀ p : I × Fin 3, ∀ x, x ∈ U →
      (finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2).toEuclideanLin x ∈ V) :
    Module.finrank ℂ U ≤ Module.finrank ℂ V := by
  exact centralHermitianMatrixFamily_subspace_finrank_of_orthogonal_commonKernel
    (fun p : I × Fin 3 => finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2)
    (fun p => finiteAllReplicaCollectiveCommutatorMatrix_conjTranspose I R p.1 p.2)
    (fun p => finiteAllReplicaCollectiveCommutator_quadraticCasimir_commutes I R p.1 p.2)
    U V hU hUV

end

end GaloisForLFunctions.HTGeometry
