import GaloisForLFunctions.HTGeometry.PolynomialBaseChange
import GaloisForLFunctions.HTGeometry.KummerBaseChangeEvenGenerator

/-!
# Base change along a radical polynomial of even degree

The odd case needs no square-root hypothesis because a field of odd degree contains no square root
of a base element.  When the second factor generates an extension of even degree that argument is
unavailable, and its place is taken by a square-class computation.

The square root the computation compares against is not extra data: it is the half power of the
generator of the second factor's root field.  So the even case of the base change needs only that
generator, its degree, and the square class of the product of the two radicands.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **The even case of base change along a radical polynomial.**  The Galois group of the first
factor survives when the base is enlarged by the roots of the second, provided the discriminant
square root and the radicand lie in different square classes. -/
noncomputable def polyBaseChangeEvenEquiv {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0)
    [Polynomial.IsSplittingField F L (p * q)]
    [Normal F (rootField F (L := L) p)] [FiniteDimensional F (rootField F (L := L) p)]
    [IsGalois F (rootField F (L := L) p)]
    [FiniteDimensional F (rootField F (L := L) q)] [IsGalois F (rootField F (L := L) q)]
    [FiniteDimensional (rootField F (L := L) q) L] [IsGalois (rootField F (L := L) q) L]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    (φ : (rootField F (L := L) p ≃ₐ[F] rootField F (L := L) p) ≃* Equiv.Perm γ)
    (hnorm : (IntermediateField.comap (rootField F (L := L) p).val
      (rootField F (L := L) p ⊓ rootField F (L := L) q)).fixingSubgroup.Normal)
    (habel : ∀ x y : (rootField F (L := L) p ≃ₐ[F] rootField F (L := L) p) ⧸
      (IntermediateField.comap (rootField F (L := L) p).val
        (rootField F (L := L) p ⊓ rootField F (L := L) q)).fixingSubgroup, x * y = y * x)
    (hcyc : IsCyclic (rootField F (L := L) q ≃ₐ[F] rootField F (L := L) q))
    {β : L} {e : F} (hβE : β ∈ rootField F (L := L) p)
    (hβsq : β * β = algebraMap F L e) (hβbot : β ∉ (⊥ : IntermediateField F L))
    {α : L} {c : F} {m : ℕ} (hm : 0 < m) (hαM : α ∈ rootField F (L := L) q)
    (hαpow : α ^ (2 * m) = algebraMap F L c)
    (hdeg : 2 * m ≤ Module.finrank F F⟮α⟯)
    (hclass : ¬ ∃ t : F, e * c = t * t) :
    (L ≃ₐ[rootField F (L := L) q] L) ≃* Equiv.Perm γ :=
  polyBaseChangeEquiv hp hq φ hnorm habel
    (notMem_of_permGal_of_isCyclic φ hcyc hβE hβsq hβbot (sq_pow_half hαpow) (pow_mem hαM m)
      (pow_notMem_bot_of_finrank_le hm (by omega) hdeg) hclass)

end GaloisForLFunctions.HTGeometry
