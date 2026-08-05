import GaloisForLFunctions.HTGeometry.TwoLocalPauliLieGeneration
import GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance matrixLieRing
    {X : Type*} [Fintype X] [DecidableEq X] :
    LieRing (Matrix X X ℂ) :=
  LieRing.ofAssociativeRing

local instance moduleEndLieRing'
    {E : Type*} [AddCommGroup E] [Module ℂ E] :
    LieRing (Module.End ℂ E) :=
  LieRing.ofAssociativeRing

/-- Tensor product of a finite family of equal-size local matrices. -/
def finiteTensorLocalMatrix
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (M : R → Matrix D D ℂ) : Matrix (R → D) (R → D) ℂ :=
  fun x y => ∏ r, M r (x r) (y r)

theorem finiteTensorLocalMatrix_mul
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (M N : R → Matrix D D ℂ) :
    finiteTensorLocalMatrix M * finiteTensorLocalMatrix N =
      finiteTensorLocalMatrix fun r => M r * N r := by
  ext x z
  rw [Matrix.mul_apply]
  change (∑ y : R → D,
      (∏ r, M r (x r) (y r)) * (∏ r, N r (y r) (z r))) =
    ∏ r, ∑ y : D, M r (x r) y * N r y (z r)
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun r (y : D) =>
    M r (x r) y * N r y (z r)).symm

theorem finiteTensorLocalMatrix_one
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D] :
    finiteTensorLocalMatrix
      (fun _ : R => (1 : Matrix D D ℂ)) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [finiteTensorLocalMatrix]
  · obtain ⟨r, hr⟩ : ∃ r, x r ≠ y r := by
      simpa only [Function.ne_iff] using hxy
    rw [finiteTensorLocalMatrix, Matrix.one_apply, if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])

/-- Lift one matrix to one distinguished tensor factor. -/
def finiteTensorSingleSiteMatrix
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (r : R) (A : Matrix D D ℂ) : Matrix (R → D) (R → D) ℂ :=
  finiteTensorLocalMatrix fun s => if s = r then A else 1

theorem finiteTensorSingleSiteMatrix_apply
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (r : R) (A : Matrix D D ℂ) (x y : R → D) :
    finiteTensorSingleSiteMatrix r A x y =
      A (x r) (y r) *
        ∏ s ∈ Finset.univ.erase r,
          (1 : Matrix D D ℂ) (x s) (y s) := by
  rw [finiteTensorSingleSiteMatrix, finiteTensorLocalMatrix,
    ← Finset.mul_prod_erase Finset.univ
      (fun s => (if s = r then A else 1) (x s) (y s))
      (Finset.mem_univ r)]
  congr 1
  · rw [if_pos rfl]
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [if_neg (Finset.ne_of_mem_erase hs)]

theorem finiteTensorSingleSiteMatrix_add
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (r : R) (A B : Matrix D D ℂ) :
    finiteTensorSingleSiteMatrix r (A + B) =
      finiteTensorSingleSiteMatrix r A + finiteTensorSingleSiteMatrix r B := by
  ext x y
  change finiteTensorSingleSiteMatrix r (A + B) x y =
    finiteTensorSingleSiteMatrix r A x y +
      finiteTensorSingleSiteMatrix r B x y
  rw [finiteTensorSingleSiteMatrix_apply,
    finiteTensorSingleSiteMatrix_apply,
    finiteTensorSingleSiteMatrix_apply]
  simp only [Matrix.add_apply]
  ring

theorem finiteTensorSingleSiteMatrix_smul
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (r : R) (c : ℂ) (A : Matrix D D ℂ) :
    finiteTensorSingleSiteMatrix r (c • A) =
      c • finiteTensorSingleSiteMatrix r A := by
  ext x y
  change finiteTensorSingleSiteMatrix r (c • A) x y =
    c * finiteTensorSingleSiteMatrix r A x y
  rw [finiteTensorSingleSiteMatrix_apply,
    finiteTensorSingleSiteMatrix_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem finiteTensorSingleSiteMatrix_sub
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (r : R) (A B : Matrix D D ℂ) :
    finiteTensorSingleSiteMatrix r (A - B) =
      finiteTensorSingleSiteMatrix r A - finiteTensorSingleSiteMatrix r B := by
  ext x y
  change finiteTensorSingleSiteMatrix r (A - B) x y =
    finiteTensorSingleSiteMatrix r A x y -
      finiteTensorSingleSiteMatrix r B x y
  rw [finiteTensorSingleSiteMatrix_apply,
    finiteTensorSingleSiteMatrix_apply,
    finiteTensorSingleSiteMatrix_apply]
  simp only [Matrix.sub_apply]
  ring

theorem finiteTensorSingleSiteMatrix_mul
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (r : R) (A B : Matrix D D ℂ) :
    finiteTensorSingleSiteMatrix r A * finiteTensorSingleSiteMatrix r B =
      finiteTensorSingleSiteMatrix r (A * B) := by
  rw [finiteTensorSingleSiteMatrix, finiteTensorSingleSiteMatrix,
    finiteTensorLocalMatrix_mul]
  congr 1
  funext s
  by_cases hsr : s = r <;> simp [hsr]

theorem finiteTensorSingleSiteMatrix_comm_of_ne
    {R D : Type*} [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    {r s : R} (hrs : r ≠ s) (A B : Matrix D D ℂ) :
    finiteTensorSingleSiteMatrix r A * finiteTensorSingleSiteMatrix s B =
      finiteTensorSingleSiteMatrix s B * finiteTensorSingleSiteMatrix r A := by
  rw [finiteTensorSingleSiteMatrix, finiteTensorSingleSiteMatrix,
    finiteTensorLocalMatrix_mul, finiteTensorLocalMatrix_mul]
  congr 1
  funext q
  by_cases hqr : q = r
  · have hqs : q ≠ s := by
      intro h
      exact hrs (hqr.symm.trans h)
    simp [hqr, hrs]
  · by_cases hqs : q = s <;> simp [hqr, hqs, Ne.symm hrs]

/-- Diagonal action of one matrix on every replica factor. -/
def finiteReplicaCollectiveMatrix
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) : Matrix (R → D) (R → D) ℂ :=
  ∑ r : R, finiteTensorSingleSiteMatrix r A

def finiteReplicaCollectiveMatrixLinear
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D] :
    Matrix D D ℂ →ₗ[ℂ] Matrix (R → D) (R → D) ℂ where
  toFun := finiteReplicaCollectiveMatrix R D
  map_add' A B := by
    simp only [finiteReplicaCollectiveMatrix,
      finiteTensorSingleSiteMatrix_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [finiteReplicaCollectiveMatrix,
      finiteTensorSingleSiteMatrix_smul, Finset.smul_sum,
      RingHom.id_apply]

private theorem ringCommutator_sum_eq_diagonal'
    {R A : Type*} [Fintype R] [DecidableEq R] [Ring A]
    (f g : R → A)
    (hcross : ∀ r s, r ≠ s → f r * g s = g s * f r) :
    ringCommutator (∑ r, f r) (∑ r, g r) =
      ∑ r, ringCommutator (f r) (g r) := by
  classical
  have hfg : (∑ r, f r) * (∑ s, g s) = ∑ r, ∑ s, f r * g s := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  have hgf : (∑ r, g r) * (∑ s, f s) = ∑ r, ∑ s, g r * f s := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  have hswap : (∑ r, ∑ s, g r * f s) = ∑ r, ∑ s, g s * f r := by
    rw [Finset.sum_comm]
  rw [ringCommutator, hfg, hgf, hswap]
  calc
    (∑ r, ∑ s, f r * g s) - ∑ r, ∑ s, g s * f r =
        ∑ r, ∑ s, (f r * g s - g s * f r) := by
          simp only [Finset.sum_sub_distrib]
    _ = ∑ r, (f r * g r - g r * f r) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_eq_single r]
          · intro s _ hsr
            rw [hcross r s (Ne.symm hsr), sub_self]
          · simp

theorem finiteReplicaCollectiveMatrix_bracket
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (A B : Matrix D D ℂ) :
    ringCommutator (finiteReplicaCollectiveMatrix R D A)
        (finiteReplicaCollectiveMatrix R D B) =
      finiteReplicaCollectiveMatrix R D (ringCommutator A B) := by
  rw [finiteReplicaCollectiveMatrix, finiteReplicaCollectiveMatrix,
    ringCommutator_sum_eq_diagonal']
  · rw [finiteReplicaCollectiveMatrix]
    apply Finset.sum_congr rfl
    intro r _
    simp only [ringCommutator]
    rw [finiteTensorSingleSiteMatrix_mul,
      finiteTensorSingleSiteMatrix_mul,
      finiteTensorSingleSiteMatrix_sub]
  · intro r s hrs
    exact finiteTensorSingleSiteMatrix_comm_of_ne hrs A B

/-- Diagonal replication is a Lie-algebra representation. -/
def finiteReplicaCollectiveMatrixLieHom
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D] :
    Matrix D D ℂ →ₗ⁅ℂ⁆ Matrix (R → D) (R → D) ℂ where
  toLinearMap := finiteReplicaCollectiveMatrixLinear R D
  map_lie' := by
    intro A B
    exact (finiteReplicaCollectiveMatrix_bracket R D A B).symm

/-- Operator commutation, represented by vectorized matrices, is a Lie
homomorphism. -/
def matrixCommutatorRepresentationLieHom
    (C : Type*) [Fintype C] [DecidableEq C] :
    Matrix C C ℂ →ₗ⁅ℂ⁆ Matrix (C × C) (C × C) ℂ where
  toLinearMap := matrixCommutatorRepresentation
  map_lie' := by
    intro A B
    exact (matrixCommutatorRepresentation_bracket A B).symm

/-- Diagonal replication followed by vectorized operator commutation. -/
def finiteReplicaCommutatorMatrixLieHom
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D] :
    Matrix D D ℂ →ₗ⁅ℂ⁆ Matrix ((R → D) × (R → D))
      ((R → D) × (R → D)) ℂ :=
  (matrixCommutatorRepresentationLieHom (R → D)).comp
    (finiteReplicaCollectiveMatrixLieHom R D)

@[simp] theorem finiteReplicaCommutatorMatrixLieHom_apply
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) :
    finiteReplicaCommutatorMatrixLieHom R D A =
      matrixCommutatorRepresentation
        (finiteReplicaCollectiveMatrix R D A) := rfl

/-- A square matrix acts on Euclidean coordinate space as a Lie
homomorphism into endomorphisms. -/
def matrixToEuclideanLinLieHom
    (X : Type*) [Fintype X] [DecidableEq X] :
    Matrix X X ℂ →ₗ⁅ℂ⁆ Module.End ℂ (EuclideanSpace ℂ X) where
  toLinearMap := Matrix.toEuclideanLin.toLinearMap
  map_lie' := by
    intro A B
    change Matrix.toEuclideanLin (A * B - B * A) =
      (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) -
        (Matrix.toEuclideanLin B).comp (Matrix.toEuclideanLin A)
    rw [map_sub, Matrix.toLpLin_mul_same,
      Matrix.toLpLin_mul_same]

/-- Full arbitrary-replica operator-commutator representation of physical
matrices. -/
def finiteReplicaCommutatorEndLieHom
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D] :
    Matrix D D ℂ →ₗ⁅ℂ⁆
      Module.End ℂ (EuclideanSpace ℂ ((R → D) × (R → D))) :=
  (matrixToEuclideanLinLieHom ((R → D) × (R → D))).comp
    (finiteReplicaCommutatorMatrixLieHom R D)

@[simp] theorem finiteReplicaCommutatorEndLieHom_apply
    (R D : Type*) [Fintype R] [DecidableEq R]
    [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) :
    finiteReplicaCommutatorEndLieHom R D A =
      (matrixCommutatorRepresentation
        (finiteReplicaCollectiveMatrix R D A)).toEuclideanLin := rfl

/-- Lie homomorphisms transport membership in a generated Lie span to the
span generated by the transported source family. -/
theorem LieHom.map_mem_lieSpan_range_subtype
    {𝕜 L M : Type*} [CommRing 𝕜]
    [LieRing L] [LieAlgebra 𝕜 L]
    [LieRing M] [LieAlgebra 𝕜 M]
    (f : L →ₗ⁅𝕜⁆ M) (S : Set L) {x : L}
    (hx : x ∈ LieSubalgebra.lieSpan 𝕜 L S) :
    f x ∈ LieSubalgebra.lieSpan 𝕜 M
      (Set.range fun s : S => f s.1) := by
  let K := LieSubalgebra.lieSpan 𝕜 M
    (Set.range fun s : S => f s.1)
  have hle : LieSubalgebra.lieSpan 𝕜 L S ≤ K.comap f := by
    apply LieSubalgebra.lieSpan_le.mpr
    intro y hy
    change f y ∈ K
    apply LieSubalgebra.subset_lieSpan
    exact ⟨⟨y, hy⟩, rfl⟩
  exact hle hx

/-- Every full Pauli commutator direction at every finite replica order is
Lie-generated by the replicated one- and two-local Pauli directions. -/
theorem finiteReplicaPauliCommutatorEnd_mem_lieSpan_twoLocal
    (R : Type*) [Fintype R] [DecidableEq R]
    {n : ℕ} (s : Fin n → Fin 4) (hs : s ≠ 0) :
    finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n)) (QuantumAlg.pauliMat s) ∈
      LieSubalgebra.lieSpan ℂ
        (Module.End ℂ
          (EuclideanSpace ℂ
            ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))))
        (Set.range fun A : QuantumAlg.twoLocalPauliMatrices n =>
          finiteReplicaCommutatorEndLieHom R (Fin (2 ^ n)) A.1) := by
  apply LieHom.map_mem_lieSpan_range_subtype
  exact QuantumAlg.pauliMat_mem_lieSpan_twoLocal s hs

end

end GaloisForLFunctions.HTGeometry
