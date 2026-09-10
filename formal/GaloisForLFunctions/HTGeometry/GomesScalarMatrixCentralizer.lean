import GaloisForLFunctions.HTGeometry.GomesCentralizerAlgebraTransport
import Mathlib.Algebra.Algebra.Subalgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Full centralizers of repeated diagonal operators

The centralizer of a scalar matrix over any algebra consists of arbitrary matrices
whose entries lie in the coefficient's centralizer. The coefficient need not be central.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable (R : Type*) [CommSemiring R]
variable {A : Type*} [Semiring A] [Algebra R A]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Matrices belonging to a subalgebra are exactly matrices of subalgebra elements. -/
def gomesSubalgebraMatrixEquiv (S : Subalgebra R A) :
    (S.matrix : Subalgebra R (Matrix ι ι A)) ≃ₐ[R] Matrix ι ι S where
  toFun M i j := ⟨M.val i j, M.property i j⟩
  invFun M := ⟨fun i j => (M i j).val, fun i j => (M i j).property⟩
  left_inv M := Subtype.ext rfl
  right_inv M := by ext i j; rfl
  map_mul' M N := by
    ext i j
    change (∑ k, M.val i k * N.val k j) =
      S.val (∑ k, (⟨M.val i k, M.property i k⟩ : S) * ⟨N.val k j, N.property k j⟩)
    rw [map_sum]
    rfl
  map_add' M N := by ext i j; rfl
  commutes' r := by
    ext i j
    change (algebraMap R (Matrix ι ι A) r) i j =
      S.val ((algebraMap R (Matrix ι ι S) r) i j)
    simp only [Matrix.algebraMap_matrix_apply]
    split_ifs <;> rfl

/-- Commutation with a repeated diagonal coefficient is entrywise commutation. -/
theorem gomesScalarMatrix_centralizer_eq (a : A) :
    Subalgebra.centralizer R {Matrix.scalar ι a} =
      ((Subalgebra.centralizer R {a}).matrix : Subalgebra R (Matrix ι ι A)) := by
  ext M
  rw [gomesCentralizerSingleton_mem_iff]
  change Matrix.scalar ι a * M = M * Matrix.scalar ι a ↔
    ∀ i j, M i j ∈ Subalgebra.centralizer R {a}
  simp only [gomesCentralizerSingleton_mem_iff]
  constructor
  · intro h i j
    have hij := congrArg (fun N : Matrix ι ι A => N i j) h
    simpa only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] using hij
  · intro h
    ext i j
    simpa only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] using h i j

/-- The full centralizer of a repeated diagonal element is a matrix algebra over its centralizer. -/
def gomesScalarMatrixCentralizerEquiv (a : A) :
    (Subalgebra.centralizer R {Matrix.scalar ι a}) ≃ₐ[R]
      Matrix ι ι (Subalgebra.centralizer R {a}) :=
  (Subalgebra.equivOfEq _ _ (gomesScalarMatrix_centralizer_eq R ι a)).trans
    (gomesSubalgebraMatrixEquiv R ι (Subalgebra.centralizer R {a}))

end GaloisForLFunctions.HTGeometry
