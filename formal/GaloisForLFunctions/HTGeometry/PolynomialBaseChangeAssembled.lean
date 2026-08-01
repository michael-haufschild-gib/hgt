import GaloisForLFunctions.HTGeometry.PolynomialBaseChangeEven
import GaloisForLFunctions.HTGeometry.IntersectionAbelian

/-!
# Base change along a radical polynomial, with the group hypotheses discharged

The subgroup fixing the intersection of the two root fields is normal because both are normal, and
the quotient by it is abelian because the second root field has cyclic automorphism group.  So
neither has to be assumed.

What is left is the second factor being a cyclic extension, its generator with its degree, and one
square-class computation — all of which the Kummer situation supplies directly.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **Base change along a radical polynomial of even degree, fully assembled.**  The Galois group of
the first factor survives enlarging the base by the roots of the second. -/
noncomputable def polyBaseChangeEvenAssembledEquiv {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0)
    [Polynomial.IsSplittingField F L (p * q)]
    [Normal F (rootField F (L := L) p)] [FiniteDimensional F (rootField F (L := L) p)]
    [IsGalois F (rootField F (L := L) p)]
    [Normal F (rootField F (L := L) q)] [FiniteDimensional F (rootField F (L := L) q)]
    [IsGalois F (rootField F (L := L) q)]
    [FiniteDimensional (rootField F (L := L) q) L] [IsGalois (rootField F (L := L) q) L]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    (φ : (rootField F (L := L) p ≃ₐ[F] rootField F (L := L) p) ≃* Equiv.Perm γ)
    (hcyc : IsCyclic (rootField F (L := L) q ≃ₐ[F] rootField F (L := L) q))
    {β : L} {e : F} (hβE : β ∈ rootField F (L := L) p)
    (hβsq : β * β = algebraMap F L e) (hβbot : β ∉ (⊥ : IntermediateField F L))
    {α : L} {c : F} {m : ℕ} (hm : 0 < m) (hαM : α ∈ rootField F (L := L) q)
    (hαpow : α ^ (2 * m) = algebraMap F L c)
    (hdeg : 2 * m ≤ Module.finrank F F⟮α⟯)
    (hclass : ¬ ∃ t : F, e * c = t * t) :
    (L ≃ₐ[rootField F (L := L) q] L) ≃* Equiv.Perm γ := by
  haveI : Normal F L := Normal.of_isSplittingField (p * q)
  letI := hcyc.commGroup
  have habelM : ∀ x y : (rootField F (L := L) q ≃ₐ[F] rootField F (L := L) q),
      x * y = y * x := fun x y => mul_comm x y
  have hnorm := fixingSubgroup_comap_inf_normal (F := F) (L := L)
    (rootField F (L := L) p) (rootField F (L := L) q)
  exact polyBaseChangeEvenEquiv hp hq φ hnorm
    (commute_quotient_comap_inf (rootField F (L := L) p) (rootField F (L := L) q) hnorm habelM)
    hcyc hβE hβsq hβbot hm hαM hαpow hdeg hclass

/-- **Base change along a radical polynomial of odd degree, fully assembled.**  No square-class
computation is needed: a field of odd degree over the base contains no square root of a base
element. -/
noncomputable def polyBaseChangeOddAssembledEquiv {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0)
    [Polynomial.IsSplittingField F L (p * q)]
    [Normal F (rootField F (L := L) p)] [FiniteDimensional F (rootField F (L := L) p)]
    [IsGalois F (rootField F (L := L) p)]
    [Normal F (rootField F (L := L) q)] [FiniteDimensional F (rootField F (L := L) q)]
    [IsGalois F (rootField F (L := L) q)]
    [FiniteDimensional (rootField F (L := L) q) L] [IsGalois (rootField F (L := L) q) L]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    (φ : (rootField F (L := L) p ≃ₐ[F] rootField F (L := L) p) ≃* Equiv.Perm γ)
    (hcyc : IsCyclic (rootField F (L := L) q ≃ₐ[F] rootField F (L := L) q))
    (hodd : ¬ 2 ∣ Module.finrank F (rootField F (L := L) q)) :
    (L ≃ₐ[rootField F (L := L) q] L) ≃* Equiv.Perm γ := by
  haveI : Normal F L := Normal.of_isSplittingField (p * q)
  letI := hcyc.commGroup
  have habelM : ∀ x y : (rootField F (L := L) q ≃ₐ[F] rootField F (L := L) q),
      x * y = y * x := fun x y => mul_comm x y
  have hnorm := fixingSubgroup_comap_inf_normal (F := F) (L := L)
    (rootField F (L := L) p) (rootField F (L := L) q)
  exact polyBaseChangeOddEquiv hp hq φ hnorm
    (commute_quotient_comap_inf (rootField F (L := L) p) (rootField F (L := L) q) hnorm habelM)
    hodd

end GaloisForLFunctions.HTGeometry
