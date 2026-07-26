import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolLowerLaw
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDeterminantHorizon

/-!
# Realizations of the matrix principal-symbol interfaces

Flatness of a matrix principal symbol is a commutation identity between consecutive layers, so any
layer symbol that does not depend on the law direction is flat — in particular the zero symbol and
every scalar layer family.

A lower principal law is realized with vanishing remainder: the block-diagonal action of the symbol on
the source packet is an observable packet whose finite stages need no strictly-lower correction.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Flatness -/

section Flat

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A layer symbol not depending on the law direction is flat. -/
theorem matrixPrincipalSymbolFlat_of_const (f : ℕ → Matrix ι ι K) :
    MatrixPrincipalSymbolFlat (fun n (_ : g) => f n) := fun _ _ _ => rfl

omit [DecidableEq ι] in
theorem matrixPrincipalSymbolFlat_zero :
    MatrixPrincipalSymbolFlat (fun (_ : ℕ) (_ : g) => (0 : Matrix ι ι K)) :=
  matrixPrincipalSymbolFlat_of_const _

theorem matrixPrincipalSymbolFlat_scalar (c : ℕ → K) :
    MatrixPrincipalSymbolFlat (fun n (_ : g) => (c n) • (1 : Matrix ι ι K)) :=
  matrixPrincipalSymbolFlat_of_const _

end Flat

/-! ## The lower principal law -/

section LowerLaw

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

/-- The block-diagonal action of a symbol on a source packet. -/
def matrixSymbolBlockAction (u : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K) (n : ℕ) (i : ι) : L :=
  ∑ j, algebraMap K L (symbol n i j) * u n j

omit [DecidableEq ι] in
/-- **Zero-remainder lower principal law.**  The block-diagonal action of a symbol is an observable
packet realizing the lower principal law with vanishing remainder. -/
theorem matrixPrincipalLowerLaw_blockAction (u : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K) :
    MatrixPrincipalLowerLaw u (matrixSymbolBlockAction u symbol) symbol := by
  intro N
  refine ⟨0, fun p q _ => rfl, ?_⟩
  funext p
  rw [matrixLinearForms, zero_add, matrixSymbolBlockAction]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p.1]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [matrixPrincipalBlockDiagonal, if_pos rfl]
  · intro n _ hn
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [matrixPrincipalBlockDiagonal, if_neg (Ne.symm hn), map_zero, zero_mul]
  · intro hp
    exact absurd (Finset.mem_univ p.1) hp

end LowerLaw

end GaloisForLFunctions.HTGeometry
