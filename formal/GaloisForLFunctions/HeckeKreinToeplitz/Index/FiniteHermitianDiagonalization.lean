import GaloisForLFunctions.HeckeKreinToeplitz.Index.HermitianFiniteSums
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Diagonal coordinates for finite Hermitian forms

A basis turns a finite Hermitian form into a Hermitian matrix. The matrix
spectral theorem supplies real diagonal weights, without imposing a norm
or a positivity assumption on the original vector space.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Module
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]

/-- Euclidean coordinates of an algebraic finite basis. -/
def basisEuclideanCoordinates (b : Basis ι ℂ V) : V ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
  b.equivFun.trans (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm

/-- The matrix convention matches conjugate-linearity of the first inner-product slot. -/
def hermitianBasisMatrix (B : V → V → ℂ) (b : Basis ι ℂ V) : Matrix ι ι ℂ :=
  fun i j => B (b j) (b i)

omit [Fintype ι] [DecidableEq ι] in
theorem isHermitian_hermitianBasisMatrix {B : V → V → ℂ}
    (hB : IsHermitianForm B) (b : Basis ι ℂ V) : (hermitianBasisMatrix B b).IsHermitian := by
  ext i j
  exact (hB.symm (b i) (b j)).symm

theorem hermitianForm_eq_inner_basisMatrix {B : V → V → ℂ}
    (hB : IsHermitianForm B) (b : Basis ι ℂ V) (v w : V) :
    B v w = inner ℂ (basisEuclideanCoordinates b w)
      ((hermitianBasisMatrix B b).toEuclideanLin (basisEuclideanCoordinates b v)) := by
  have hs := hermitianForm_fin_synthesis hB b b (b.repr v) (b.repr w)
  rw [b.sum_repr, b.sum_repr] at hs
  rw [hs, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
  change (∑ i, ∑ j, b.repr v i * star (b.repr w j) * B (b i) (b j)) =
    ∑ i, (∑ j, B (b j) (b i) * b.repr v j) * star (b.repr w i)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite Hermitian form has real diagonal coordinates. -/
theorem exists_hermitian_diagonal_coordinates [FiniteDimensional ℂ V]
    {B : V → V → ℂ} (hB : IsHermitianForm B) :
    ∃ (n : ℕ) (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (d : Fin n → ℝ),
      ∀ v w, B v w = ∑ i, (d i : ℂ) * conj (e w i) * e v i := by
  let n := Module.finrank ℂ V
  let b := Module.finBasis ℂ V
  let M := hermitianBasisMatrix B b
  have hM : M.IsHermitian := isHermitian_hermitianBasisMatrix hB b
  have hT : M.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by simp
  let o := hT.eigenvectorBasis hn
  let d := hT.eigenvalues hn
  let e := (basisEuclideanCoordinates b).trans o.repr.toLinearEquiv
  refine ⟨n, e, d, ?_⟩
  intro v w
  rw [hermitianForm_eq_inner_basisMatrix hB b]
  rw [← o.repr.inner_map_map]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hT.eigenvectorBasis_apply_self_apply hn (basisEuclideanCoordinates b v) i
  change o.repr (M.toEuclideanLin (basisEuclideanCoordinates b v)) i =
    (d i : ℂ) * o.repr (basisEuclideanCoordinates b v) i at hi
  change inner ℂ (e w i) (o.repr (M.toEuclideanLin (basisEuclideanCoordinates b v)) i) = _
  rw [hi, RCLike.inner_apply']
  change conj (e w i) * ((d i : ℂ) * e v i) = (d i : ℂ) * conj (e w i) * e v i
  ring

#print axioms exists_hermitian_diagonal_coordinates

end GaloisForLFunctions.HeckeKreinToeplitz
