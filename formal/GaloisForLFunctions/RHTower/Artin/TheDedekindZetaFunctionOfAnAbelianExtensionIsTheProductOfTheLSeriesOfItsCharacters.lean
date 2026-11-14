import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfALinearCharacter
import GaloisForLFunctions.RHTower.Artin.ArtinIdempotentsOfAnAbelianNormalSubgroup
import GaloisForLFunctions.RHTower.Artin.ArtinCharacterInduction

/-!
# The Dedekind zeta function of an abelian extension is the product of the `L`-series of its characters

Let `L/K` be an abelian extension of number fields with group `G`. For `Re s > 1`

  `ζ_L(s) = Π_χ L(s, χ, L/K)`,

the product over the characters `χ` of `G` (`dedekindZeta_eq_prod_artinEulerProduct`). The top
field enters as a field `M` between `K` and `L` whose group over `L` is the trivial subgroup.

Proof. The regular character `r_G` (`|G|` at `1`, `0` elsewhere) is induced from the trivial
character of the trivial subgroup (`inducedFunction_bot_one`), so the Artin Euler product of
the regular representation is the Dedekind zeta function of the top field. By the second
orthogonality relation `r_G = Σ_χ χ`, and the Artin Euler product is multiplicative on
relations between characters.
-/

open scoped Classical BigOperators NumberField

noncomputable section

universe u

namespace GaloisForLFunctions

attribute [local instance] finiteLinearCharacter fintypeLinearCharacter

/-- **The regular character is induced from the trivial subgroup**: the function induced from
the constant `1` on the trivial subgroup is `|G|` at `1` and `0` elsewhere. -/
theorem inducedFunction_bot_one {G : Type u} [Group G] [Fintype G] (g : G) :
    inducedFunction (⊥ : Subgroup G) (fun _ => (1 : ℂ)) g =
      if g = 1 then (Nat.card G : ℂ) else 0 := by
  have hext : ∀ x : G, extendByZero (⊥ : Subgroup G) (fun _ => (1 : ℂ)) (x * g * x⁻¹) =
      if g = 1 then 1 else 0 := fun x => by
    by_cases hg : g = 1
    · rw [if_pos hg, extendByZero_of_mem _ _ (show x * g * x⁻¹ ∈ (⊥ : Subgroup G) by
        rw [hg, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _)]
    · rw [if_neg hg, extendByZero_of_notMem _ _ fun h =>
        hg (conj_eq_one_iff.mp (Subgroup.mem_bot.mp h))]
  rw [inducedFunction, Finset.sum_congr rfl fun x _ => hext x, Subgroup.card_bot, Nat.cast_one,
    inv_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The Dedekind zeta function of an abelian extension is the product of the Artin
`L`-series of the characters of its group**, for `Re s > 1`. Here `M` is the top field: a field
between `K` and `L` over which `L` has the trivial subgroup as its group. -/
theorem dedekindZeta_eq_prod_artinEulerProduct (M : Type u) [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L] [IsGaloisGroup (⊥ : Subgroup G) M L]
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta M s = ∏ χ : LinearCharacter G,
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
        (linearCharacterLine χ) s := by
  -- the regular representation: induced from the trivial character of the trivial subgroup
  have hreg : (inducedRepresentation G (⊥ : Subgroup G)
      (linearCharacterLine (1 : LinearCharacter (⊥ : Subgroup G)))).character =
      inducedFunction (⊥ : Subgroup G) fun _ => 1 := by
    rw [inducedRepresentation, induced_character_eq_inducedFunction,
      linearCharacterLine_character]
    rfl
  -- the regular character is the sum of the characters
  have hsum : (inducedRepresentation G (⊥ : Subgroup G)
      (linearCharacterLine (1 : LinearCharacter (⊥ : Subgroup G)))).character =
      ∑ χ ∈ (Finset.univ : Finset (LinearCharacter G)),
        (1 : ℤ) • (linearCharacterLine χ).character := by
    rw [hreg]
    funext g
    rw [inducedFunction_bot_one, Finset.sum_apply, ← sum_linearCharacter_apply g]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [one_smul, linearCharacterLine_character]
  rw [← artinEulerProduct_induced_one_eq_dedekindZeta K L (M := M) (⊥ : Subgroup G) _ hreg hs]
  refine (numberFieldFinitePlaceArtinEulerReciprocalProduct_eq_prod_zpow (K := K) (L := L)
    Finset.univ (fun _ => (1 : ℤ)) _ (fun χ : LinearCharacter G => linearCharacterLine χ)
    hsum hs).trans ?_
  exact Finset.prod_congr rfl fun χ _ => zpow_one _

end GaloisForLFunctions
