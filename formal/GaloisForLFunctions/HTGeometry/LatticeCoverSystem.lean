import GaloisForLFunctions.HTGeometry.IntegerCoverSystem

/-!
# Towers of tori from a filtration by lattices

A monotone family of lattices in a fixed abelian group becomes a family of integer matrices once a
basis has been chosen in each lattice: the inclusion of one lattice in the next is an integer
matrix in those bases, the matrix of a reflexive relation is the identity, and the matrices
multiply along a composite because the inclusions compose.  Transposing turns this into the
covariant convention of a cover system, where the matrix acts on the coordinates of the covering
space of the larger torus and returns those of the smaller.

* `GaloisForLFunctions.HTGeometry.integerCoverSystemOfBases` : the integer matrices of a based
  filtration by lattices.
* `GaloisForLFunctions.HTGeometry.torusCoverSystemOfBases` : the tower of tori it defines.
-/

namespace GaloisForLFunctions.HTGeometry

section LatticeSystem

open Module

variable {M : Type*} [AddCommGroup M] {ι : Type*} [Preorder ι]

/-- The inclusion of one member of a monotone family of lattices in a later one. -/
noncomputable def latticeInclusion (L : ι → Submodule ℤ M) (hmono : ∀ i j, i ≤ j → L i ≤ L j)
    (i j : ι) (h : i ≤ j) : L i →ₗ[ℤ] L j :=
  Submodule.inclusion (hmono i j h)

theorem latticeInclusion_self (L : ι → Submodule ℤ M) (hmono : ∀ i j, i ≤ j → L i ≤ L j)
    (i : ι) (h : i ≤ i) : latticeInclusion L hmono i i h = LinearMap.id := by
  ext x
  rfl

theorem latticeInclusion_comp (L : ι → Submodule ℤ M) (hmono : ∀ i j, i ≤ j → L i ≤ L j)
    (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) :
    (latticeInclusion L hmono j k hjk) ∘ₗ (latticeInclusion L hmono i j hij)
      = latticeInclusion L hmono i k (hij.trans hjk) := by
  ext x
  rfl

/-- **The integer matrices of a filtration by based lattices.**  In the chosen bases the inclusion
of one lattice in a later one is an integer matrix; the transpose is taken so that the matrix acts
on the coordinates of the larger space. -/
noncomputable def integerCoverSystemOfBases (L : ι → Submodule ℤ M)
    (hmono : ∀ i j, i ≤ j → L i ≤ L j) (d : ι → ℕ)
    (B : ∀ i, Basis (Fin (d i)) ℤ (L i)) : IntegerCoverSystem ι where
  dim := d
  mat i j h := (LinearMap.toMatrix (B i) (B j) (latticeInclusion L hmono i j h)).transpose
  mat_self i h := by
    rw [latticeInclusion_self L hmono i h, LinearMap.toMatrix_id, Matrix.transpose_one]
  mat_trans i j k hij hjk := by
    rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp (B i) (B j) (B k),
      latticeInclusion_comp L hmono i j k hij hjk]

@[simp] theorem integerCoverSystemOfBases_dim (L : ι → Submodule ℤ M)
    (hmono : ∀ i j, i ≤ j → L i ≤ L j) (d : ι → ℕ) (B : ∀ i, Basis (Fin (d i)) ℤ (L i)) :
    (integerCoverSystemOfBases L hmono d B).dim = d := rfl

/-- **The tower of tori of a filtration by based lattices**, with period one: the torus of a
lattice is the quotient of its coordinate space by the integer points, and the inclusion of
lattices induces the covering map. -/
noncomputable def torusCoverSystemOfBases (𝕜 : Type*) [RCLike 𝕜] (L : ι → Submodule ℤ M)
    (hmono : ∀ i j, i ≤ j → L i ≤ L j) (d : ι → ℕ)
    (B : ∀ i, Basis (Fin (d i)) ℤ (L i)) : TorusCoverSystem 𝕜 (1 : 𝕜) ι :=
  torusCoverSystemOfMatrices (integerCoverSystemOfBases L hmono d B)

@[simp] theorem torusCoverSystemOfBases_dim (𝕜 : Type*) [RCLike 𝕜] (L : ι → Submodule ℤ M)
    (hmono : ∀ i j, i ≤ j → L i ≤ L j) (d : ι → ℕ) (B : ∀ i, Basis (Fin (d i)) ℤ (L i)) :
    (torusCoverSystemOfBases 𝕜 L hmono d B).dim = d := rfl

end LatticeSystem

end GaloisForLFunctions.HTGeometry
