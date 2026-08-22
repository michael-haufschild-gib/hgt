import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.Tactic

/-!
# Realizing root permutations inside a Galois group

`Polynomial.Gal.galActionHom` is always injective on the Galois group of a polynomial, so the
Galois group is the full symmetric group on the roots exactly when every permutation of the roots
is realized by a field automorphism.  Because the realized permutations form a subgroup, it is
enough to realize a *generating* set.

This is the interface between an explicitly constructed field automorphism — for instance the
conjugation of a quadratic step in `QuadraticTowerSquareClasses` — and the statement
`Nat.card p.Gal = D !` that Hilbert irreducibility consumes.

## Main results

* `mem_range_galActionHom_of_algEquiv` — an `F`-automorphism of a splitting field realizes its
  permutation of the roots inside the Galois action.
* `galActionHom_surjective_of_closure` — realizing a generating set suffices.
* `card_gal_eq_factorial_of_closure` — hence `Nat.card p.Gal` is `D !`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] (p : F[X]) (E : Type*) [Field E] [Algebra F E]
  [Fact (p.map (algebraMap F E)).Splits]

/-- An `F`-automorphism of a field in which `p` splits realizes its permutation of the roots
inside the image of the Galois action. -/
theorem mem_range_galActionHom_of_algEquiv (ϕ : E ≃ₐ[F] E)
    (σ : Equiv.Perm (p.rootSet E))
    (hσ : ∀ x : p.rootSet E, ((σ x : E)) = ϕ (x : E)) :
    σ ∈ (Gal.galActionHom p E).range := by
  refine ⟨Gal.restrict p E ϕ, ?_⟩
  ext x
  rw [Gal.galActionHom_restrict]
  exact (hσ x).symm

/-- If the realized permutations generate the whole symmetric group on the roots, the Galois
action is surjective. -/
theorem galActionHom_surjective_of_closure
    {S : Set (Equiv.Perm (p.rootSet E))}
    (hS : Subgroup.closure S = ⊤)
    (hmem : ∀ σ ∈ S, σ ∈ (Gal.galActionHom p E).range) :
    Function.Surjective (Gal.galActionHom p E) := by
  intro σ
  have hle : Subgroup.closure S ≤ (Gal.galActionHom p E).range :=
    (Subgroup.closure_le _).mpr hmem
  rw [hS] at hle
  exact hle (Subgroup.mem_top σ)

/-- **The Galois group is the full symmetric group on the roots** as soon as a generating set of
permutations is realized by field automorphisms. -/
theorem card_gal_eq_factorial_of_closure
    [Fintype (p.rootSet E)] [DecidableEq (p.rootSet E)]
    {S : Set (Equiv.Perm (p.rootSet E))}
    (hS : Subgroup.closure S = ⊤)
    (hmem : ∀ σ ∈ S, σ ∈ (Gal.galActionHom p E).range) :
    Nat.card p.Gal = (Fintype.card (p.rootSet E)).factorial := by
  have hbij : Function.Bijective (Gal.galActionHom p E) :=
    ⟨Gal.galActionHom_injective p E, galActionHom_surjective_of_closure p E hS hmem⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The special case in which every transposition of roots is realized. -/
theorem card_gal_eq_factorial_of_swaps
    [Fintype (p.rootSet E)] [DecidableEq (p.rootSet E)]
    (hmem : ∀ σ : Equiv.Perm (p.rootSet E), σ.IsSwap →
      σ ∈ (Gal.galActionHom p E).range) :
    Nat.card p.Gal = (Fintype.card (p.rootSet E)).factorial :=
  card_gal_eq_factorial_of_closure p E Equiv.Perm.closure_isSwap (fun σ hσ => hmem σ hσ)

end GaloisForLFunctions.HTGeometry
