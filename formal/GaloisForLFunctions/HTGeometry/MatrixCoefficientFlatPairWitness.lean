import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolWitnesses
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolCoefficientFlatness

/-!
# Coefficient flatness with a lower principal law

The corpus realizes `MatrixPrincipalSymbolFlat` — the commutation identity
`symbol (n+1) A · symbol n B = symbol (n+1) B · symbol n A` — by direction-independent layer symbols,
and realizes `MatrixPrincipalLowerLaw` with vanishing remainder.  The layer that consumes *both*
premises together uses the other order, `MatrixCoefficientPrincipalSymbolFlat`
(`symbol n B · symbol (n+1) A = symbol n A · symbol (n+1) B`), which nothing realizes.

The same witness serves: a symbol not depending on the law direction makes both sides of either
identity literally the same product.  Pairing it with the block-diagonal action realizes the two
premises simultaneously.

* **`matrixCoefficientPrincipalSymbolFlat_of_const`**, and the zero and scalar instances;
* **`exists_coefficientFlat_lowerLaw`** — the pair, jointly realized.
-/

namespace GaloisForLFunctions.HTGeometry

section Flat

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A layer symbol not depending on the law direction is coefficient flat. -/
theorem matrixCoefficientPrincipalSymbolFlat_of_const (f : ℕ → Matrix ι ι K) :
    MatrixCoefficientPrincipalSymbolFlat (fun n (_ : g) => f n) := fun _ _ _ => rfl

omit [DecidableEq ι] in
theorem matrixCoefficientPrincipalSymbolFlat_zero :
    MatrixCoefficientPrincipalSymbolFlat (fun (_ : ℕ) (_ : g) => (0 : Matrix ι ι K)) :=
  matrixCoefficientPrincipalSymbolFlat_of_const _

theorem matrixCoefficientPrincipalSymbolFlat_scalar (c : ℕ → K) :
    MatrixCoefficientPrincipalSymbolFlat (fun n (_ : g) => (c n) • (1 : Matrix ι ι K)) :=
  matrixCoefficientPrincipalSymbolFlat_of_const _

end Flat

section Joint

variable {K L g ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Joint realization.**  A direction-independent layer symbol is coefficient flat, and its
block-diagonal action realizes the lower principal law with vanishing remainder, so the two premises
hold together on one symbol. -/
theorem exists_coefficientFlat_lowerLaw (f : ℕ → Matrix ι ι K) (u : ℕ → ι → L) :
    MatrixCoefficientPrincipalSymbolFlat (fun n (_ : g) => f n) ∧
      MatrixPrincipalLowerLaw u (matrixSymbolBlockAction u f) f :=
  ⟨matrixCoefficientPrincipalSymbolFlat_of_const f, matrixPrincipalLowerLaw_blockAction u f⟩

end Joint

end GaloisForLFunctions.HTGeometry
