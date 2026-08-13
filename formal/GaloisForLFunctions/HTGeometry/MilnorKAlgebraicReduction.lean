import GaloisForLFunctions.HTGeometry.MilnorKFunctoriality
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Length-two symbols of an algebraic extension come from a finite subextension

Two elements of an algebraic extension of the rationals generate a finite subextension, and torsion
of a length-two Milnor symbol descends along the inclusion.  So the torsion of every length-two
symbol of an arbitrary algebraic extension of the rationals follows from the torsion of every
length-two symbol of every finite subextension.

* `milnorSymbol_mul_torsion_of_finiteSubextension` : **reduction to finite subextensions.**
-/

namespace GaloisForLFunctions.HTGeometry

open IntermediateField

/-- **Reduction to finite subextensions.**  If every length-two symbol of every finite
subextension is torsion, then so is every length-two symbol. -/
theorem milnorSymbol_mul_torsion_of_finiteSubextension {F : Type*} [Field F] [Algebra ℚ F]
    [Algebra.IsAlgebraic ℚ F]
    (hNF : ∀ K : IntermediateField ℚ F, FiniteDimensional ℚ K →
      ∀ x y : Kˣ, (milnorSymbol x * milnorSymbol y : MilnorK K) ∈ torsionAddSubgroup (MilnorK K))
    (a b : Fˣ) :
    (milnorSymbol a * milnorSymbol b : MilnorK F) ∈ torsionAddSubgroup (MilnorK F) := by
  classical
  have hint : ∀ x ∈ ({(a : F), (b : F)} : Set F), IsIntegral ℚ x := by
    intro x _
    exact (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set K : IntermediateField ℚ F := IntermediateField.adjoin ℚ ({(a : F), (b : F)} : Set F) with hK
  haveI hfd : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hint
  have haK : (a : F) ∈ K := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hbK : (b : F) ∈ K := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hane : (⟨(a : F), haK⟩ : K) ≠ 0 := by
    intro hzero
    exact a.ne_zero (congrArg Subtype.val hzero)
  have hbne : (⟨(b : F), hbK⟩ : K) ≠ 0 := by
    intro hzero
    exact b.ne_zero (congrArg Subtype.val hzero)
  refine milnorSymbol_mul_torsion_of_ringHom (K.val : K →+* F) (a := a) (b := b)
    (x := Units.mk0 _ hane) (y := Units.mk0 _ hbne) rfl rfl (hNF K hfd _ _)

end GaloisForLFunctions.HTGeometry
