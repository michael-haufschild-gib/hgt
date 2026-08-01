import GaloisForLFunctions.HTGeometry.RadicalBaseChangeCapstone

/-!
# Base change along an even radical extension, from mathematical data alone

Everything the base change step needs beyond the two polynomials is derived here: the typeclass
hypotheses from the ambient being a splitting field of the product, the permutation identification
from any model splitting field of the first factor, and the cyclicity of the second factor from the
degree of its generator together with a primitive root of unity in the base.

What is left to supply is the mathematics: a symmetric-group identification for the first factor, a
generator of the radical extension with its degree, a square root of a base element inside the first
factor's root field, and the fact that the two radicands lie in different square classes.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **The card's base change step, from mathematical data alone.** -/
noncomputable def radicalBaseChangeEven {p : Polynomial F} {c : F} {m : ℕ} (hp : p ≠ 0)
    (hm : 0 < m)
    [Polynomial.IsSplittingField F L
      (p * (Polynomial.X ^ (2 * m) - Polynomial.C c))]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    {L₀ : Type*} [Field L₀] [Algebra F L₀] [Polynomial.IsSplittingField F L₀ p]
    (ψ : (L₀ ≃ₐ[F] L₀) ≃* Equiv.Perm γ)
    (hζ : (primitiveRoots (2 * m) F).Nonempty)
    {α : L}
    (hαM : α ∈ rootField F (L := L) (Polynomial.X ^ (2 * m) - Polynomial.C c))
    (hαpow : α ^ (2 * m) = algebraMap F L c)
    (hdeg : 2 * m ≤ Module.finrank F F⟮α⟯)
    {β : L} {e : F} (hβE : β ∈ rootField F (L := L) p)
    (hβsq : β * β = algebraMap F L e) (hβbot : β ∉ (⊥ : IntermediateField F L))
    (hclass : ¬ ∃ t : F, e * c = t * t) :
    (L ≃ₐ[rootField F (L := L) (Polynomial.X ^ (2 * m) - Polynomial.C c)] L) ≃* Equiv.Perm γ := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hq : (Polynomial.X ^ (2 * m) - Polynomial.C c : Polynomial F) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero
  have hsplitAll := Polynomial.IsSplittingField.splits' (K := F) (L := L)
    (f := p * (Polynomial.X ^ (2 * m) - Polynomial.C c))
  have hsplitp := splits_of_splits_mul_left (L := L) hp hq hsplitAll
  have hsplitq := splits_of_splits_mul_right (L := L) hp hq hsplitAll
  haveI := isGalois_rootField_left (L := L) (p := p)
    (q := (Polynomial.X ^ (2 * m) - Polynomial.C c)) hp hq
  haveI := isGalois_rootField_right (L := L) (p := p)
    (q := (Polynomial.X ^ (2 * m) - Polynomial.C c)) hp hq
  haveI := finiteDimensional_rootField_left (L := L) (p := p)
    (q := (Polynomial.X ^ (2 * m) - Polynomial.C c)) hp hq
  haveI := finiteDimensional_rootField_right (L := L) (p := p)
    (q := (Polynomial.X ^ (2 * m) - Polynomial.C c)) hp hq
  haveI : Normal F (rootField F (L := L) p) := IsGalois.to_normal
  haveI : Normal F (rootField F (L := L) (Polynomial.X ^ (2 * m) - Polynomial.C c)) :=
    IsGalois.to_normal
  haveI := isGalois_top_over_rootField (L := L) (p := p)
    (q := (Polynomial.X ^ (2 * m) - Polynomial.C c))
  haveI : FiniteDimensional F L :=
    Polynomial.IsSplittingField.finiteDimensional L
      (p * (Polynomial.X ^ (2 * m) - Polynomial.C c))
  haveI : FiniteDimensional
      (rootField F (L := L) (Polynomial.X ^ (2 * m) - Polynomial.C c)) L :=
    FiniteDimensional.right F _ L
  have hirr := irreducible_X_pow_sub_C_of_finrank (L := L) (by omega) hαpow hdeg
  have hcyc := isCyclic_rootField_X_pow_sub_C (F := F) (L := L) hζ hirr hsplitq
  exact polyBaseChangeEvenAssembledEquiv hp hq
    (rootFieldPermEquiv (L := L₀) (L' := L) hsplitp ψ) hcyc hβE hβsq hβbot hm hαM hαpow hdeg hclass

/-- **The odd case of the same statement.**  No square-class computation is needed: the radical
extension has odd degree, so it contains no square root of a base element. -/
noncomputable def radicalBaseChangeOdd {p : Polynomial F} {c : F} {n : ℕ} (hp : p ≠ 0)
    (hn : 0 < n)
    [Polynomial.IsSplittingField F L (p * (Polynomial.X ^ n - Polynomial.C c))]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    {L₀ : Type*} [Field L₀] [Algebra F L₀] [Polynomial.IsSplittingField F L₀ p]
    (ψ : (L₀ ≃ₐ[F] L₀) ≃* Equiv.Perm γ)
    (hζ : (primitiveRoots n F).Nonempty)
    {α : L} (hαpow : α ^ n = algebraMap F L c)
    (hdeg : n ≤ Module.finrank F F⟮α⟯)
    (hodd : ¬ 2 ∣ Module.finrank F
      (rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c))) :
    (L ≃ₐ[rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c)] L) ≃* Equiv.Perm γ := by
  haveI : NeZero n := ⟨by omega⟩
  have hq : (Polynomial.X ^ n - Polynomial.C c : Polynomial F) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero
  have hsplitAll := Polynomial.IsSplittingField.splits' (K := F) (L := L)
    (f := p * (Polynomial.X ^ n - Polynomial.C c))
  have hsplitp := splits_of_splits_mul_left (L := L) hp hq hsplitAll
  have hsplitq := splits_of_splits_mul_right (L := L) hp hq hsplitAll
  haveI := isGalois_rootField_left (L := L) (p := p)
    (q := (Polynomial.X ^ n - Polynomial.C c)) hp hq
  haveI := isGalois_rootField_right (L := L) (p := p)
    (q := (Polynomial.X ^ n - Polynomial.C c)) hp hq
  haveI := finiteDimensional_rootField_left (L := L) (p := p)
    (q := (Polynomial.X ^ n - Polynomial.C c)) hp hq
  haveI := finiteDimensional_rootField_right (L := L) (p := p)
    (q := (Polynomial.X ^ n - Polynomial.C c)) hp hq
  haveI : Normal F (rootField F (L := L) p) := IsGalois.to_normal
  haveI : Normal F (rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c)) :=
    IsGalois.to_normal
  haveI := isGalois_top_over_rootField (L := L) (p := p)
    (q := (Polynomial.X ^ n - Polynomial.C c))
  haveI : FiniteDimensional F L :=
    Polynomial.IsSplittingField.finiteDimensional L
      (p * (Polynomial.X ^ n - Polynomial.C c))
  haveI : FiniteDimensional
      (rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c)) L :=
    FiniteDimensional.right F _ L
  have hirr := irreducible_X_pow_sub_C_of_finrank (L := L) hn hαpow hdeg
  have hcyc := isCyclic_rootField_X_pow_sub_C (F := F) (L := L) hζ hirr hsplitq
  exact polyBaseChangeOddAssembledEquiv hp hq
    (rootFieldPermEquiv (L := L₀) (L' := L) hsplitp ψ) hcyc hodd

end GaloisForLFunctions.HTGeometry
