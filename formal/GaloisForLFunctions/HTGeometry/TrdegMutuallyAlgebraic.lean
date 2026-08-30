import GaloisForLFunctions.HTGeometry.StateFieldTrdeg
import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed

/-!
# Mutually algebraic fields have the same transcendence degree

Two intermediate fields each of whose elements is algebraic over the other have the same relative
algebraic closure, and the relative algebraic closure does not change the transcendence degree.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

universe u

/-- Algebraicity over a smaller field passes to a larger one. -/
theorem isAlgebraic_of_le {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A B : IntermediateField K L} (hAB : A ≤ B) {y : L} (h : IsAlgebraic ↥A y) :
    IsAlgebraic ↥B y := by
  letI : Algebra ↥A ↥B := (IntermediateField.inclusion hAB).toRingHom.toAlgebra
  haveI : IsScalarTower ↥A ↥B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h.tower_top ↥B

/-- **Mutually algebraic fields have the same relative algebraic closure.** -/
theorem algebraicClosure_eq_of_mutually_algebraic {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A B : IntermediateField K L}
    (hAB : ∀ y : L, y ∈ A → IsAlgebraic ↥B y) (hBA : ∀ y : L, y ∈ B → IsAlgebraic ↥A y) :
    (algebraicClosure ↥A L).restrictScalars K = (algebraicClosure ↥B L).restrictScalars K := by
  have key : ∀ (P Q : IntermediateField K L), (∀ y : L, y ∈ P → IsAlgebraic ↥Q y) →
      (algebraicClosure ↥P L).restrictScalars K ≤ (algebraicClosure ↥Q L).restrictScalars K := by
    intro P Q hPQ y hy
    have hyP : IsAlgebraic ↥P y := mem_algebraicClosure_iff.mp hy
    have hle : P ≤ (algebraicClosure ↥Q L).restrictScalars K := by
      intro w hw
      exact mem_algebraicClosure_iff.mpr (hPQ w hw)
    have := isAlgebraic_of_le hle hyP
    exact mem_algebraicClosure_of_isAlgebraic this
  exact le_antisymm (key A B hAB) (key B A hBA)

/-- **Mutually algebraic fields have the same transcendence degree.** -/
theorem trdeg_eq_of_mutually_algebraic {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A B : IntermediateField K L}
    (hAB : ∀ y : L, y ∈ A → IsAlgebraic ↥B y) (hBA : ∀ y : L, y ∈ B → IsAlgebraic ↥A y) :
    Algebra.trdeg K ↥A = Algebra.trdeg K ↥B := by
  have hA := trdeg_algebraicClosure_restrictScalars_eq (K := K) (L := L) A
  have hB := trdeg_algebraicClosure_restrictScalars_eq (K := K) (L := L) B
  rw [← hA, ← hB, algebraicClosure_eq_of_mutually_algebraic hAB hBA]

end

end GaloisForLFunctions.HTGeometry
