import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.FieldTheory.Finiteness

/-!
# Finite quotients of polynomial orders

A finite free domain over `K[X]` has finite-dimensional quotients by every
nonzero ideal. Smith decomposition reduces this to quotients of `K[X]` by
nonzero polynomials. Over finite constants, these quotient rings are finite.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (K B : Type*) [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra K[X] B] [IsScalarTower K K[X] B]
    [Module.Free K[X] B] [Module.Finite K[X] B]

/-- Every nonzero ideal of a finite free polynomial order has finite codimension over the constants. -/
theorem polynomialOrder_quotient_finiteDimensional (I : Ideal B) (hI : I ≠ ⊥) :
    Module.Finite K (B ⧸ I) := by
  let b := Module.Free.chooseBasis K[X] B
  letI (i : Module.Free.ChooseBasisIndex K[X] B) :
      Module.Finite K (K[X] ⧸ Ideal.span {I.smithCoeffs b hI i}) :=
    PowerBasis.finite (AdjoinRoot.powerBasis (I.smithCoeffs_ne_zero b hI i))
  exact Module.Finite.equiv (Ideal.quotientEquivDirectSum K b hI).symm

/-- Nonzero ideal quotients are finite when the constant field is finite. -/
theorem polynomialOrder_quotient_finite [Finite K] (I : Ideal B) (hI : I ≠ ⊥) :
    Finite (B ⧸ I) := by
  letI := polynomialOrder_quotient_finiteDimensional K B I hI
  exact Module.finite_of_finite K

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
