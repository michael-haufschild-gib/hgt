import GaloisForLFunctions.HTGeometry.StaticShortcutReplicaProjectorFrameLaw

/-!
# Vectorized conjugation channels and replica tensor powers

Conjugation `X ↦ A X Aᴴ` of square matrices is itself a matrix acting on the vectorization
`X ↦ (fun p => X p.1 p.2)`; its entries are `A p.1 q.1 * conj (A p.2 q.2)`.  This module records
that vectorized channel, its multiplicativity, its adjoint, and its action on rank-one projectors.

The `r`-fold tensor power of a single-copy matrix is the matrix with entries `∏ a, A (x a) (y a)`
on the replica index `Fin r → α`.  It is multiplicative, unital, compatible with the adjoint, and
maps an `r`-fold pure tensor to the `r`-fold pure tensor of the image.  Combining the two
constructions gives the exact one-gate action on a replica projector: the vectorized conjugation
by the replica power of a gate sends the replica projector of a state to the replica projector of
the gated state.
-/

open Matrix

open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Vectorization

variable {β : Type*} [Fintype β]

/-- Coordinate vectorization of a square matrix. -/
def matrixVectorization (X : Matrix β β ℂ) : β × β → ℂ := fun p => X p.1 p.2

/-- Rank-one projector `|ψ⟩⟨ψ|` as a matrix. -/
def pureProjectorMatrix (ψ : β → ℂ) : Matrix β β ℂ := Matrix.of fun i j => ψ i * conj (ψ j)

omit [Fintype β] in
theorem matrixVectorization_pureProjectorMatrix (ψ : β → ℂ) :
    matrixVectorization (pureProjectorMatrix ψ) = finitePureProjectorCoordinate ψ := rfl

/-- Vectorized conjugation channel `X ↦ A X Aᴴ`. -/
def pureConjugationChannel (A : Matrix β β ℂ) : Matrix (β × β) (β × β) ℂ :=
  Matrix.of fun p q => A p.1 q.1 * conj (A p.2 q.2)

theorem pureConjugationChannel_mulVec (A X : Matrix β β ℂ) :
    (pureConjugationChannel A).mulVec (matrixVectorization X) =
      matrixVectorization (A * X * Aᴴ) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, pureConjugationChannel, Matrix.of_apply,
    matrixVectorization, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

omit [Fintype β] in
theorem pureConjugationChannel_conjTranspose (A : Matrix β β ℂ) :
    (pureConjugationChannel A)ᴴ = pureConjugationChannel Aᴴ := by
  funext p q
  simp only [Matrix.conjTranspose_apply, pureConjugationChannel, Matrix.of_apply, RCLike.star_def,
    map_mul, starRingEnd_self_apply]

theorem pureConjugationChannel_mul [DecidableEq β] (A B : Matrix β β ℂ) :
    pureConjugationChannel A * pureConjugationChannel B = pureConjugationChannel (A * B) := by
  funext p q
  simp only [Matrix.mul_apply, pureConjugationChannel, Matrix.of_apply, map_sum, map_mul]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

omit [Fintype β] in
theorem pureConjugationChannel_one [DecidableEq β] :
    pureConjugationChannel (1 : Matrix β β ℂ) = 1 := by
  funext p q
  simp only [pureConjugationChannel, Matrix.of_apply, Matrix.one_apply, apply_ite conj,
    map_one, map_zero]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [h1, h2, Prod.ext_iff]

/-- Conjugation by `A` sends the rank-one projector of `ψ` to that of `A *ᵥ ψ`. -/
theorem conj_pureProjectorMatrix (A : Matrix β β ℂ) (ψ : β → ℂ) :
    A * pureProjectorMatrix ψ * Aᴴ = pureProjectorMatrix (A.mulVec ψ) := by
  funext i j
  simp only [Matrix.mul_apply, pureProjectorMatrix, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, RCLike.star_def, map_sum, map_mul]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The vectorized one-gate action on a rank-one projector. -/
theorem pureConjugationChannel_mulVec_projector (A : Matrix β β ℂ) (ψ : β → ℂ) :
    (pureConjugationChannel A).mulVec (finitePureProjectorCoordinate ψ) =
      finitePureProjectorCoordinate (A.mulVec ψ) := by
  rw [← matrixVectorization_pureProjectorMatrix, pureConjugationChannel_mulVec,
    conj_pureProjectorMatrix, matrixVectorization_pureProjectorMatrix]

end Vectorization

section ReplicaPower

variable {α : Type*} [Fintype α]

/-- `r`-fold tensor power of a single-copy matrix on the replica index. -/
def replicaTensorPowerMatrix (r : ℕ) (A : Matrix α α ℂ) :
    Matrix (Fin r → α) (Fin r → α) ℂ := Matrix.of fun x y => ∏ a, A (x a) (y a)

omit [Fintype α] in
theorem replicaTensorPowerMatrix_conjTranspose (r : ℕ) (A : Matrix α α ℂ) :
    (replicaTensorPowerMatrix r A)ᴴ = replicaTensorPowerMatrix r Aᴴ := by
  funext x y
  simp only [Matrix.conjTranspose_apply, replicaTensorPowerMatrix, Matrix.of_apply,
    RCLike.star_def, map_prod]

omit [Fintype α] in
theorem replicaTensorPowerMatrix_one [DecidableEq α] (r : ℕ) :
    replicaTensorPowerMatrix r (1 : Matrix α α ℂ) = 1 := by
  funext x y
  simp only [replicaTensorPowerMatrix, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · have : ∃ a, x a ≠ y a := by
      by_contra hc
      exact h (funext fun a => not_not.mp (fun hh => hc ⟨a, hh⟩))
    obtain ⟨a, ha⟩ := this
    rw [if_neg h, Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])]

theorem replicaTensorPowerMatrix_mul [DecidableEq α] (r : ℕ) (A B : Matrix α α ℂ) :
    replicaTensorPowerMatrix r (A * B) =
      replicaTensorPowerMatrix r A * replicaTensorPowerMatrix r B := by
  funext x y
  simp only [replicaTensorPowerMatrix, Matrix.of_apply, Matrix.mul_apply]
  rw [← sum_pi_prod_complex (fun a (z : α) => A (x a) z * B z (y a))]
  exact Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib

/-- The replica power of a matrix acts on an `r`-fold pure tensor as the single-copy matrix acts
on the state. -/
theorem replicaTensorPowerMatrix_mulVec (r : ℕ) (A : Matrix α α ℂ) (ψ : α → ℂ) :
    (replicaTensorPowerMatrix r A).mulVec (finitePureTensorPower r ψ) =
      finitePureTensorPower r (A.mulVec ψ) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, replicaTensorPowerMatrix, Matrix.of_apply,
    finitePureTensorPower]
  rw [← sum_pi_prod_complex (fun a (z : α) => A (x a) z * ψ z)]
  · exact Finset.sum_congr rfl fun z _ => (Finset.prod_mul_distrib).symm

end ReplicaPower

end

end GaloisForLFunctions.HTGeometry
