import GaloisForLFunctions.HTGeometry.DifferentialFGBaseChange
import GaloisForLFunctions.HTGeometry.KolchinNullstellensatzDiffFG
import GaloisForLFunctions.HTGeometry.TensorReducedGeneral

/-!
# Differential points after scalar extension

A reduced, differentially finitely generated algebra remains reduced and differentially finitely
generated after extending a characteristic-zero differential base field.  If the new field is
differentially closed, Kolchin's Nullstellensatz therefore supplies differential points separating
every nonzero element of the scalar extension.
-/

open scoped TensorProduct Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

universe u

variable {K L E : Type u} [Field K] [CharZero K] [Field L] [CommRing E]
  [Algebra ℚ L] [Algebra K L] [Algebra K E]
  [Differential K] [Differential L] [Differential E]
  [DifferentialAlgebra K L] [DifferentialAlgebra K E]
  [IsDifferentiallyClosed L] [IsReduced E]

/-- Differential points over a differentially closed scalar extension separate every nonzero
element of a differentially finitely generated reduced algebra. -/
theorem exists_differentialAlgHom_ne_zero_of_diffFG_tensorBaseChange
    {k : ℕ} (y : Fin k → E)
    (hy : Function.Surjective (differentialPolynomialEvalOver (K := K) y))
    {e : L ⊗[K] E} (he : e ≠ 0) :
    letI : Differential (L ⊗[K] E) := tensorProductDifferential
    ∃ χ : (L ⊗[K] E) →ₐ[L] L,
      (∀ x, χ (Differential.deriv x) = Differential.deriv (χ x)) ∧ χ e ≠ 0 := by
  letI : Differential (L ⊗[K] E) := tensorProductDifferential
  letI : DifferentialAlgebra L (L ⊗[K] E) := tensorProductDifferentialAlgebra_left
  letI : IsReduced (L ⊗[K] E) :=
    isReduced_tensor_field_algebra_of_charZero (k := K) (L := L) (B := E)
  exact exists_differentialAlgHom_ne_zero_of_diffFG
    (C := L) (E := L ⊗[K] E) (fun i => (1 : L) ⊗ₜ[K] y i)
    (differentialPolynomialEvalOver_tensorBaseChange_surjective y hy) he

end

end GaloisForLFunctions.HTGeometry
