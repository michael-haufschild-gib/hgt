import GaloisForLFunctions.HTGeometry.SolvableGaloisRadicals
import GaloisForLFunctions.HTGeometry.GroupCharacter.BurnsideUniverse

/-!
# Radical solvability of an extension with full symmetric sheet action

Let `S/O` be a finite extension of characteristic-zero fields whose normal-closure Galois group acts
on the `D = [S:O]` sheets as the full symmetric group.  Then every element of `S` is solvable by
radicals over `O` exactly when `D ≤ 4`.

* If `D ≤ 4` the Galois group has order `D!`, dividing `2³·3`, so it is solvable by Burnside's
  `pᵃqᵇ` theorem; the Galois group of the minimal polynomial of any element of `S` is a quotient of
  it, and the converse of Abel–Ruffini applies.
* If every element is solvable by radicals, so is a primitive element; its minimal polynomial has
  the normal closure as splitting field, so the Galois group of the normal closure is solvable, and
  `S_D` is not solvable for `D ≥ 5`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

variable (O S : Type*) [Field O] [Field S] [Algebra O S] [FiniteDimensional O S] [CharZero O]

/-- **Radical threshold for a full symmetric extension.**  Every element of `S` is solvable by
radicals over `O` exactly when `[S:O] ≤ 4`. -/
theorem forall_isSolvableByRad_iff_finrank_le_four
    (hbij : Function.Bijective (sheetAction O S)) :
    (∀ x : S, algebraMap S (AlgebraicClosure S) x ∈ solvableByRad O (AlgebraicClosure S)) ↔
      Module.finrank O S ≤ 4 := by
  classical
  let N := sheetNormalClosure O S
  let e : Gal(N/O) ≃* Equiv.Perm (sheetEmbedding O S) := MulEquiv.ofBijective _ hbij
  have hsheets : Nat.card (sheetEmbedding O S) = Module.finrank O S := natCard_sheetEmbedding O S
  constructor
  · intro hrad
    by_contra hD
    obtain ⟨θ, hθ⟩ := Field.exists_primitive_element O S
    have hθint : IsIntegral O θ := Algebra.IsIntegral.isIntegral θ
    have hrθ : algebraMap S (AlgebraicClosure S) θ ∈ solvableByRad O (AlgebraicClosure S) :=
      hrad θ
    have hsolvθ := isSolvable_gal_minpoly hrθ
    rw [minpoly.algebraMap_eq (algebraMap S (AlgebraicClosure S)).injective] at hsolvθ
    haveI : IsSolvable Gal((minpoly O θ).SplittingField/O) := hsolvθ
    haveI : IsSplittingField O N (minpoly O θ) :=
      isSplittingField_minpoly_of_isNormalClosure_of_adjoin_singleton_eq_top θ hθint hθ
    have hsolvN : IsSolvable Gal(N/O) :=
      solvable_of_surjective
        (f := (autMulEquivOfAlgEquiv (IsSplittingField.algEquiv N (minpoly O θ))).symm.toMonoidHom)
        (autMulEquivOfAlgEquiv (IsSplittingField.algEquiv N (minpoly O θ))).symm.surjective
    have hsolvP : IsSolvable (Equiv.Perm (sheetEmbedding O S)) :=
      solvable_of_surjective (f := e.toMonoidHom) e.surjective
    apply Equiv.Perm.not_solvable (sheetEmbedding O S) _ hsolvP
    rw [← Nat.cast_card, hsheets]
    exact_mod_cast (show 5 ≤ Module.finrank O S by omega)
  · intro hD x
    have hcard : Nat.card Gal(N/O) ∣ 2 ^ 3 * 3 ^ 1 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, hsheets]
      interval_cases h : Module.finrank O S <;> decide
    have hsolvN : IsSolvable Gal(N/O) :=
      GroupCharacter.isSolvable_of_card_dvd_two_prime_powers Nat.prime_two Nat.prime_three hcard
    let y : N := sheetCanonicalEmbedding O S x
    have hminy : minpoly O y = minpoly O x :=
      minpoly.algHom_eq (sheetCanonicalEmbedding O S) (sheetCanonicalEmbedding O S).injective x
    haveI : Fact ((minpoly O x).map (algebraMap O N)).Splits := ⟨by
      rw [← hminy]
      exact Normal.splits inferInstance y⟩
    have hsolvx : IsSolvable (minpoly O x).Gal :=
      solvable_of_surjective (Gal.restrict_surjective (minpoly O x) N)
    have hα : IsIntegral O (algebraMap S (AlgebraicClosure S) x) :=
      (Algebra.IsIntegral.isIntegral x).algebraMap
    have hmin : minpoly O (algebraMap S (AlgebraicClosure S) x) = minpoly O x :=
      minpoly.algebraMap_eq (algebraMap S (AlgebraicClosure S)).injective x
    exact mem_solvableByRad_of_isSolvable_gal_minpoly hα (by rw [hmin]; exact hsolvx)

end

end GaloisForLFunctions.HTGeometry
