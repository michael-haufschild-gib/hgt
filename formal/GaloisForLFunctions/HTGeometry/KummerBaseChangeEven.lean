import GaloisForLFunctions.HTGeometry.KummerBaseChange
import GaloisForLFunctions.HTGeometry.EvenCaseDischarge

/-!
# Base change with the exclusion condition discharged

Combining the base change step with the even-case exclusion gives a statement whose only remaining
inputs are the square-class computation on a fixed square root and the abelian quotient, both of
which are supplied by the situation rather than assumed about every element.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **Base change preserves the symmetric Galois group, exclusion discharged.**  The only inputs are
the abelian quotient on the intersection and one square-class computation. -/
noncomputable def kummerBaseChangeEvenEquiv {E M : IntermediateField F L}
    [Normal F E] [FiniteDimensional F E] [IsGalois F E]
    [FiniteDimensional F M] [IsGalois F M]
    [FiniteDimensional M L] [IsGalois M L]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm γ)
    (hEM : E ⊔ M = ⊤)
    (hnorm : (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup.Normal)
    (habel : ∀ x y : (E ≃ₐ[F] E) ⧸
      (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup, x * y = y * x)
    (hcyc : IsCyclic (M ≃ₐ[F] M))
    {β : L} {d : F} (hβE : β ∈ E) (hβsq : β * β = algebraMap F L d)
    (hβbot : β ∉ (⊥ : IntermediateField F L))
    {α₀ : L} {c : F} (hα₀sq : α₀ * α₀ = algebraMap F L c) (hα₀M : α₀ ∈ M)
    (hα₀bot : α₀ ∉ (⊥ : IntermediateField F L))
    (hclass : ¬ ∃ t : F, d * c = t * t) :
    (L ≃ₐ[M] L) ≃* Equiv.Perm γ :=
  kummerBaseChangePermOfAbelian φ hEM hnorm habel
    (notMem_of_permGal_of_isCyclic φ hcyc hβE hβsq hβbot hα₀sq hα₀M hα₀bot hclass)

end GaloisForLFunctions.HTGeometry
