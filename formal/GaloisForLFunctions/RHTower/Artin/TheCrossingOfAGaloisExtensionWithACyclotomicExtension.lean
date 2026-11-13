import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfACyclotomicCharacterIsAHeckeLSeries
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# The crossing of a Galois extension with a cyclotomic extension

Let `K ⊂ L ⊂ M` be fields with `L/K` and `M/K` Galois with groups `G` and `Γ`, and `M`
generated over `L` by a primitive `m`-th root of unity `ζ`. Let `r : Γ → G` be the restriction
and `κ : Γ → (ℤ/m)ˣ` the cyclotomic character of `ζ`.

* `γ ↦ (r γ, κ(γ))` is injective (`injective_restrictHom_prod_cyclotomicCharacter`): an
  automorphism that fixes `L` and `ζ` fixes `L(ζ) = M`.
* If `[M : L] = φ(m)` it is bijective (`bijective_restrictHom_prod_cyclotomicCharacter`):
  `|Γ| = [L : K] [M : L] = |G| φ(m)`.

**Existence** (`exists_cyclotomic_crossing`). Let `L/K` be an abelian extension of number
fields and `Φ_m` irreducible over `L`. Then there are a number field `M ⊃ L`, abelian over `K`
with group `Γ`, and a primitive `m`-th root of unity in `M`, such that `γ ↦ (r γ, κ(γ))` is
bijective. Take `M = L(ζ_m)`, the splitting field over `K` of `p · Φ_m` for a polynomial `p`
over `K` with splitting field `L`; its Galois group embeds into `G × (ℤ/m)ˣ`.
-/

open scoped Classical NumberField
open NumberField Polynomial

noncomputable section

universe u

namespace GaloisForLFunctions

section Tower

variable (K L M : Type u) {G Γ : Type u} [Field K] [Field L] [Field M] [Algebra K L]
  [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [Group Γ] [Finite Γ] [MulSemiringAction Γ M] [IsGaloisGroup Γ K M]
  {m : ℕ} [NeZero m] {ζ : 𝓞 M} (hζ : IsPrimitiveRoot ζ m)
  (hadj : Algebra.adjoin L {(ζ : M)} = ⊤)

include hadj

/-- An automorphism of `M = L(ζ)` that restricts to the identity of `L` and fixes `ζ` is the
identity. -/
theorem eq_one_of_restrictHom_eq_one_of_cyclotomicCharacter_eq_one {γ : Γ}
    (hr : IsGaloisGroup.restrictHom Γ G K L M γ = 1) (hκ : cyclotomicCharacter hζ γ = 1) :
    γ = 1 := by
  haveI : FaithfulSMul Γ M := IsGaloisGroup.faithful K
  have hfix : γ • (ζ : M) = ζ :=
    congrArg (fun x : 𝓞 M => (x : M)) (smul_eq_of_cyclotomicCharacter_eq_one hζ hκ)
  refine eq_of_smul_eq_smul fun x : M => ?_
  rw [one_smul]
  have hx : x ∈ Algebra.adjoin L {(ζ : M)} := hadj ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hfix
  | algebraMap y => rw [← IsGaloisGroup.algebraMap_restrictHom_smul Γ G K L M, hr, one_smul]
  | add y z _ _ hy hz => rw [smul_add, hy, hz]
  | mul y z _ _ hy hz => rw [smul_mul', hy, hz]

/-- **The restriction to `L` and the cyclotomic character determine an automorphism of
`L(ζ)`.** -/
theorem injective_restrictHom_prod_cyclotomicCharacter :
    Function.Injective fun γ : Γ =>
      (IsGaloisGroup.restrictHom Γ G K L M γ, cyclotomicCharacter hζ γ) := by
  intro γ γ' h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  refine mul_inv_eq_one.mp (eq_one_of_restrictHom_eq_one_of_cyclotomicCharacter_eq_one K L M
    (G := G) hζ hadj ?_ ?_)
  · rw [map_mul, map_inv, h1, mul_inv_cancel]
  · rw [map_mul, map_inv, h2, mul_inv_cancel]

/-- **If `[L(ζ) : L] = φ(m)`, the automorphisms of `L(ζ)` over `K` are the pairs of an
automorphism of `L` and a residue class prime to `m`.** -/
theorem bijective_restrictHom_prod_cyclotomicCharacter
    (hdeg : Module.finrank L M = m.totient) :
    Function.Bijective fun γ : Γ =>
      (IsGaloisGroup.restrictHom Γ G K L M γ, cyclotomicCharacter hζ γ) := by
  refine (injective_restrictHom_prod_cyclotomicCharacter K L M hζ hadj).bijective_of_nat_card_le
    (le_of_eq ?_)
  rw [Nat.card_prod, IsGaloisGroup.card_eq_finrank G K L,
    Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient, ← hdeg,
    Module.finrank_mul_finrank, IsGaloisGroup.card_eq_finrank Γ K M]

end Tower

/-- The crossing inside a given cyclotomic extension `M` of `L`: the Galois group of `M/K` is
abelian, and its elements are the pairs of an automorphism of `L` and a residue class prime to
`m`. -/
theorem exists_crossing_of_isCyclotomicExtension (K L M : Type u) {G : Type u} [Field K]
    [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M] [CommGroup G] [Fintype G]
    [MulSemiringAction G L] [IsGaloisGroup G K L] {m : ℕ} [NeZero m]
    [IsCyclotomicExtension {m} L M] (hirr : Irreducible (cyclotomic m L)) :
    ∃ (Γ : Type u) (_ : CommGroup Γ) (_ : Fintype Γ) (_ : MulSemiringAction Γ M)
      (_ : IsGaloisGroup Γ K M) (ζ : 𝓞 M) (hζ : IsPrimitiveRoot ζ m),
      Function.Bijective fun γ : Γ =>
        (IsGaloisGroup.restrictHom Γ G K L M γ, cyclotomicCharacter hζ γ) := by
  haveI : IsGalois K L := IsGaloisGroup.isGalois G K L
  haveI : FiniteDimensional K L := IsGaloisGroup.finiteDimensional G K L
  haveI : FiniteDimensional L M := IsCyclotomicExtension.finiteDimensional {m} L M
  haveI : FiniteDimensional K M := Module.Finite.trans L M
  -- `M` is the splitting field over `K` of `p Φ_m`
  haveI : IsGalois K M := by
    obtain ⟨p, hpsep, hp⟩ := IsGalois.is_separable_splitting_field K L
    haveI := hp
    haveI : IsSplittingField L M ((cyclotomic m K).map (algebraMap K L)) := by
      rw [map_cyclotomic]
      exact IsCyclotomicExtension.splitting_field_cyclotomic m L M
    haveI := IsSplittingField.mul (K := L) (L := M) p (cyclotomic m K) hpsep.ne_zero
      (cyclotomic_ne_zero m K)
    exact isGalois_iff.mpr ⟨inferInstance, Normal.of_isSplittingField (p * cyclotomic m K)⟩
  have hζ' := IsCyclotomicExtension.zeta_spec m L M
  have hadj : Algebra.adjoin L {((hζ'.toInteger : 𝓞 M) : M)} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ'
  have hbij := bijective_restrictHom_prod_cyclotomicCharacter K L M (G := G) (Γ := M ≃ₐ[K] M)
    hζ'.toInteger_isPrimitiveRoot hadj (IsCyclotomicExtension.finrank M hirr)
  -- the Galois group embeds into the abelian group `G × (ℤ/m)ˣ`
  letI : CommGroup (M ≃ₐ[K] M) :=
    { (inferInstance : Group (M ≃ₐ[K] M)) with
      mul_comm := fun a b => hbij.1 (Prod.ext
        (show IsGaloisGroup.restrictHom (M ≃ₐ[K] M) G K L M (a * b) =
            IsGaloisGroup.restrictHom (M ≃ₐ[K] M) G K L M (b * a) by
          rw [map_mul, map_mul, mul_comm])
        (show cyclotomicCharacter hζ'.toInteger_isPrimitiveRoot (a * b) =
            cyclotomicCharacter hζ'.toInteger_isPrimitiveRoot (b * a) by
          rw [map_mul, map_mul, mul_comm])) }
  exact ⟨M ≃ₐ[K] M, this, Fintype.ofFinite _, AlgEquiv.applyMulSemiringAction,
    IsGaloisGroup.of_isGalois K M, hζ'.toInteger, hζ'.toInteger_isPrimitiveRoot, hbij⟩

/-- **The crossing of an abelian extension with a cyclotomic extension.** If `Φ_m` is
irreducible over `L`, there are a number field `M ⊃ L`, abelian over `K` with group `Γ`, and a
primitive `m`-th root of unity `ζ ∈ M`, such that the restriction to `L` together with the
cyclotomic character of `ζ` is a bijection `Γ → G × (ℤ/m)ˣ`. -/
theorem exists_cyclotomic_crossing (K L : Type u) {G : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L]
    [IsGaloisGroup G K L] {m : ℕ} [NeZero m] (hirr : Irreducible (cyclotomic m L)) :
    ∃ (M : Type u) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower K L M) (Γ : Type u) (_ : CommGroup Γ) (_ : Fintype Γ)
      (_ : MulSemiringAction Γ M) (_ : IsGaloisGroup Γ K M) (ζ : 𝓞 M)
      (hζ : IsPrimitiveRoot ζ m),
      Function.Bijective fun γ : Γ =>
        (IsGaloisGroup.restrictHom Γ G K L M γ, cyclotomicCharacter hζ γ) := by
  obtain ⟨Γ, i1, i2, i3, i4, ζ, hζ, h⟩ :=
    exists_crossing_of_isCyclotomicExtension K L (CyclotomicField m L) (G := G) hirr
  exact ⟨CyclotomicField m L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, Γ, i1, i2, i3, i4, ζ, hζ, h⟩

end GaloisForLFunctions
