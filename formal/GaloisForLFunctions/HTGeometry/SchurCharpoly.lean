/-
# The characteristic polynomial in Schur coordinates, and algebraic multiplicity

The characteristic polynomial of a matrix is `∏ᵢ (X − tᵢ)` over its Schur diagonal, so the
multiplicity of `μ` as a root — equivalently, by mathlib's
`LinearMap.finrank_maxGenEigenspace_eq`, the dimension of the generalized eigenspace, i.e. the
**algebraic multiplicity** — is the number of Schur diagonal entries equal to `μ`.

Main results:
* `charpoly_of_upperTriangular`, `charpoly_of_schur` — the characteristic polynomial factors.
* `rootMultiplicity_charpoly_eq_schurCount` — root multiplicity is the Schur diagonal count.
* `finrank_maxGenEigenspace_eq_schurCount` — **algebraic multiplicity is the Schur diagonal
  count**.
-/
import GaloisForLFunctions.HTGeometry.SchurTriangulation
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset Polynomial

variable {m : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] {M U T : Matrix m m ℂ}

/-- The characteristic polynomial of an upper-triangular matrix is the product of `X − tᵢ`. -/
theorem charpoly_of_upperTriangular (hT : T.BlockTriangular id) :
    T.charpoly = ∏ i, (X - C (T i i)) := by
  have htri : (Matrix.charmatrix T).BlockTriangular id := by
    intro i j hij
    have hne : i ≠ j := fun hh => absurd hij (by rw [hh]; simp)
    simp [Matrix.charmatrix, Matrix.diagonal_apply_ne _ hne, hT hij]
  rw [Matrix.charpoly, Matrix.det_of_upperTriangular htri]
  exact Finset.prod_congr rfl fun i _ => by simp [Matrix.charmatrix]

/-- **The characteristic polynomial in Schur coordinates.** -/
theorem charpoly_of_schur (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hT : T.BlockTriangular id)
    (hMT : Uᴴ * M * U = T) : M.charpoly = ∏ i, (X - C (T i i)) := by
  have hM : M = U * T * Uᴴ := by
    rw [← hMT]
    calc M = (U * Uᴴ) * M * (U * Uᴴ) := by rw [hU2]; noncomm_ring
      _ = U * (Uᴴ * M * U) * Uᴴ := by noncomm_ring
  have hUinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hU2
  have hconj : (U * T * Uᴴ).charpoly = T.charpoly := by
    have h := Matrix.charpoly_units_conj (⟨U, Uᴴ, hU2, hU1⟩ : (Matrix m m ℂ)ˣ) T
    rw [show ((⟨U, Uᴴ, hU2, hU1⟩ : (Matrix m m ℂ)ˣ) : Matrix m m ℂ) = U from rfl, hUinv] at h
    exact h
  rw [hM, hconj, charpoly_of_upperTriangular hT]

/-- **The root multiplicity of the characteristic polynomial is the Schur diagonal count.** -/
theorem rootMultiplicity_charpoly_eq_schurCount (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) (μ : ℂ) :
    M.charpoly.rootMultiplicity μ = (Finset.univ.filter fun i => T i i = μ).card := by
  classical
  have hprod : M.charpoly
      = ((Finset.univ.val.map fun i : m => T i i).map fun a : ℂ => X - C a).prod := by
    rw [charpoly_of_schur hU1 hU2 hT hMT, Finset.prod, Multiset.map_map]
    rfl
  have hroots : M.charpoly.roots = Finset.univ.val.map fun i : m => T i i := by
    rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]
  rw [← Polynomial.count_roots, hroots, Multiset.count_map]
  rw [Finset.card_filter]
  simp [Finset.filter, Finset.card, eq_comm]

/-- **The algebraic multiplicity of an eigenvalue is the number of Schur diagonal entries equal to
it.** -/
theorem finrank_maxGenEigenspace_eq_schurCount (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) (μ : ℂ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (Matrix.toLin' M) μ)
      = (Finset.univ.filter fun i => T i i = μ).card := by
  classical
  have hcp : LinearMap.charpoly (Matrix.toLin' M) = M.charpoly := by
    have hMat : LinearMap.toMatrix (Pi.basisFun ℂ m) (Pi.basisFun ℂ m) (Matrix.toLin' M) = M :=
      (LinearEquiv.eq_symm_apply (LinearMap.toMatrix (Pi.basisFun ℂ m) (Pi.basisFun ℂ m))).mp rfl
    have h := LinearMap.charpoly_toMatrix (Matrix.toLin' M) (Pi.basisFun ℂ m)
    rw [hMat] at h
    exact h.symm
  rw [LinearMap.finrank_maxGenEigenspace_eq, hcp,
    rootMultiplicity_charpoly_eq_schurCount hU1 hU2 hT hMT μ]

end GaloisForLFunctions.HTGeometry
