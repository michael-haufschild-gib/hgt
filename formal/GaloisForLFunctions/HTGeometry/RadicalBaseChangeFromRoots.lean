import GaloisForLFunctions.HTGeometry.RadicalBaseChangeEvenCapstone
import GaloisForLFunctions.HTGeometry.RadicalRootExists
import GaloisForLFunctions.HTGeometry.VandermondeFixed

/-!
# Base change from the roots of the first factor

The discriminant square root need not be supplied: it is the Vandermonde product of the roots of the
first factor.  It lies in that factor's root field, its square is a base-field element because every
automorphism permutes the roots, and it is not itself in the base field as soon as some automorphism
acts by an odd permutation.

Likewise the generator of the radical extension is produced by the polynomial splitting.  So the
statement reduces to the two polynomials, the symmetric-group identification, the degree of the
radical generator, and the square class.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **Base change along an even radical extension, with the discriminant square root taken from the
roots.** -/
noncomputable def radicalBaseChangeEvenFromRoots {p : Polynomial F} {c : F} {m : ℕ}
    (hp : p ≠ 0) (hm : 0 < m)
    [Polynomial.IsSplittingField F L (p * (Polynomial.X ^ (2 * m) - Polynomial.C c))]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    {L₀ : Type*} [Field L₀] [Algebra F L₀] [Polynomial.IsSplittingField F L₀ p]
    (ψ : (L₀ ≃ₐ[F] L₀) ≃* Equiv.Perm γ)
    (hζ : (primitiveRoots (2 * m) F).Nonempty)
    {dd : ℕ} (v : Fin dd → rootField F (L := L) p)
    (hvinj : Function.Injective v)
    (hvperm : ∀ σ : rootField F (L := L) p ≃ₐ[F] rootField F (L := L) p,
      ∃ e : Equiv.Perm (Fin dd), ∀ i, σ (v i) = v (e i))
    (σ₀ : rootField F (L := L) p ≃ₐ[F] rootField F (L := L) p) (e₀ : Equiv.Perm (Fin dd))
    (hσ₀ : ∀ i, σ₀ (v i) = v (e₀ i)) (hsign : Equiv.Perm.sign e₀ = -1)
    (hdeg : ∀ α : L, α ^ (2 * m) = algebraMap F L c → 2 * m ≤ Module.finrank F F⟮α⟯)
    (hclass : ∀ e : F,
      algebraMap F (rootField F (L := L) p) e = vandermondeProd v * vandermondeProd v →
      ¬ ∃ t : F, e * c = t * t) :
    (L ≃ₐ[rootField F (L := L) (Polynomial.X ^ (2 * m) - Polynomial.C c)] L) ≃* Equiv.Perm γ := by
  have hq : (Polynomial.X ^ (2 * m) - Polynomial.C c : Polynomial F) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero
  have hsplitAll := Polynomial.IsSplittingField.splits' (K := F) (L := L)
    (f := p * (Polynomial.X ^ (2 * m) - Polynomial.C c))
  have hsplitq := splits_of_splits_mul_right (L := L) hp hq hsplitAll
  haveI := isGalois_rootField_left (L := L) (p := p)
    (q := (Polynomial.X ^ (2 * m) - Polynomial.C c)) hp hq
  haveI := finiteDimensional_rootField_left (L := L) (p := p)
    (q := (Polynomial.X ^ (2 * m) - Polynomial.C c)) hp hq
  haveI : CharZero (rootField F (L := L) p) :=
    charZero_of_injective_algebraMap
      (algebraMap F (rootField F (L := L) p)).injective
  have hex := exists_pow_eq_mem_rootField (L := L) (c := c) (n := 2 * m) (by omega) hsplitq
  have hexe := exists_algebraMap_vandermondeSq (F := F)
    (E := rootField F (L := L) p) v hvperm
  set α := Classical.choose hex with hαdef
  have hαM := (Classical.choose_spec hex).1
  have hαpow := (Classical.choose_spec hex).2
  set e := Classical.choose hexe with hedef
  have he := Classical.choose_spec hexe
  refine radicalBaseChangeEven hp hm ψ hζ hαM hαpow (hdeg α hαpow)
    (β := ((vandermondeProd v : rootField F (L := L) p) : L)) (e := e)
    (vandermondeProd v).2 ?_ ?_ (hclass e he)
  · rw [IsScalarTower.algebraMap_apply F (rootField F (L := L) p) L, he, map_mul]
    rfl
  · exact notMem_bot_of_notMem_bot_coe
      (vandermondeProd_notMem_bot v hvinj σ₀ e₀ hσ₀ hsign)

end GaloisForLFunctions.HTGeometry
