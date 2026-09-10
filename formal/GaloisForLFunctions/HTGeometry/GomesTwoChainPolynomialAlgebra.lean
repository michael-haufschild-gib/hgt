import GaloisForLFunctions.HTGeometry.GomesTwoChainConstantObservation
import GaloisForLFunctions.HTGeometry.GomesEvenFormalFunctionalCalculus
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Faithful formal matrix algebra inside actual polynomial endomorphisms

The full second-derivative matrix equivalence embeds its entire matrix algebra
into polynomial endomorphisms. This identifies the derivative, affine reflections,
and scalar matrices with the actual operators used by the corpus.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- Every two-chain formal matrix acts as an actual polynomial endomorphism. -/
def gomesTwoChainPolynomialAlgHom :
    Matrix (Fin 2) (Fin 2) (PowerSeries K) →ₐ[K] Module.End K K[X] :=
  (gomesPolynomialDerivativePowerCommutantAlgebra K 2).val.comp
    (gomesPolynomialDerivativePowerCommutantEquiv K 2).symm.toAlgHom

/-- Reconstructing the matrix of an actual symmetry returns that exact endomorphism. -/
theorem gomesTwoChainPolynomialAlgHom_matrix (E : GomesPolynomialDerivativePowerCommutant K 2) :
    gomesTwoChainPolynomialAlgHom K (gomesPolynomialDerivativePowerCommutantEquiv K 2 E) = E.val :=
  congrArg Subtype.val ((gomesPolynomialDerivativePowerCommutantEquiv K 2).symm_apply_apply E)

/-- The full formal matrix action is faithful on actual polynomial inputs. -/
theorem gomesTwoChainPolynomialAlgHom_injective : Function.Injective (gomesTwoChainPolynomialAlgHom K) := by
  intro M N h
  apply (gomesPolynomialDerivativePowerCommutantEquiv K 2).symm.injective
  exact Subtype.ext h

/-- The formal companion matrix acts as the actual first derivative. -/
theorem gomesTwoChainPolynomialAlgHom_derivative :
    gomesTwoChainPolynomialAlgHom K (gomesEvenOddDerivativeMatrix K) = Polynomial.derivative := by
  rw [← gomesFormalSeriesDerivativePowerMatrixHom_two_X]
  change gomesTwoChainPolynomialAlgHom K (gomesPolynomialDerivativePowerCommutantEquiv K 2
    (gomesFormalSeriesDerivativePowerHom K 2 PowerSeries.X)) = _
  rw [gomesTwoChainPolynomialAlgHom_matrix]
  exact gomesFormalSeriesPolynomialOperator_X K

/-- Every formal reflection matrix acts as its literal affine polynomial reflection. -/
theorem gomesTwoChainPolynomialAlgHom_reflection (c : K) :
    gomesTwoChainPolynomialAlgHom K (gomesPolynomialReflectionMatrix K c) =
      gomesPolynomialReflectionEnd K c :=
  gomesTwoChainPolynomialAlgHom_matrix K (gomesPolynomialReflectionSymmetry K c)

omit [CharZero K] in
/-- The scalar-center algebra map is the literal scalar formal matrix. -/
theorem gomesTwoChainMatrix_algebraMap (F : PowerSeries K) :
    algebraMap (PowerSeries K) (Matrix (Fin 2) (Fin 2) (PowerSeries K)) F = Matrix.scalar (Fin 2) F := by
  apply Matrix.ext
  intro i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- Scalar formal matrices are exactly the actual formal functions of D². -/
theorem gomesTwoChainPolynomialAlgHom_scalar (F : PowerSeries K) :
    gomesTwoChainPolynomialAlgHom K (Matrix.scalar (Fin 2) F) = gomesEvenFormalPolynomialOperator K F := rfl

/-- Formal-center scalars act as the actual even formal functional calculus. -/
theorem gomesTwoChainPolynomialAlgHom_algebraMap (F : PowerSeries K) :
    gomesTwoChainPolynomialAlgHom K
      (algebraMap (PowerSeries K) (Matrix (Fin 2) (Fin 2) (PowerSeries K)) F) =
        gomesEvenFormalPolynomialOperator K F := by
  rw [gomesTwoChainMatrix_algebraMap, gomesTwoChainPolynomialAlgHom_scalar]

/-- The formal scalar action also has the explicit expanded-series interpretation. -/
theorem gomesTwoChainPolynomialAlgHom_scalar_expanded (F : PowerSeries K) :
    gomesTwoChainPolynomialAlgHom K (Matrix.scalar (Fin 2) F) =
      gomesFormalSeriesPolynomialOperator K (PowerSeries.expand 2 (Nat.succ_ne_zero 1) F) := by
  rw [gomesTwoChainPolynomialAlgHom_scalar, gomesEvenFormalPolynomialOperator_eq_expanded]

end GaloisForLFunctions.HTGeometry
