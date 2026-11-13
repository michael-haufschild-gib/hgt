import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInflatedRepresentation
import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfACyclotomicCharacterIsAHeckeLSeries

/-!
# Artin Euler products are invariant under inflation

Let `K ⊂ M ⊂ L` be number fields with `L/K` and `M/K` Galois with groups `G` and `G'`, and
`π : G → G'` the restriction of automorphisms. For a representation `ρ'` of `G'`:

* the local Euler polynomial of `ρ' ∘ π` over `L/K` at a prime `v` of `K` is that of `ρ'` over
  `M/K` (`numberFieldFinitePlaceLocalEulerPolynomial_inflation`): for a prime `Q` of `L` above
  `v`, `π` maps the inertia group of `Q` onto that of `Q ∩ M` and a Frobenius element to a
  Frobenius element;
* **`L(s, ρ' ∘ π, L/K) = L(s, ρ', M/K)`**
  (`numberFieldFinitePlaceArtinEulerReciprocalProduct_inflation`);
* the Artin symbol of a linear character `χ'` of `G'` is that of `χ' ∘ π`
  (`artinSymbol_inflation`).

With additivity and induction this is the Artin formalism of the Euler products.

**Abelian extensions inside cyclotomic extensions**
(`exists_artinEulerProduct_eq_heckeL_mul_of_adjoin_eq_top_of_tower`): if `L = K(ζ)` for a
primitive `m`-th root of unity `ζ`, every linear character `χ'` of `Gal(M/K)` has a ray class
character `ψ` modulo `(m) ∞` with
`L(s, χ', M/K) = L(s, ψ) · Π_{v | m} (1 − (χ', v) N(v)^{-s})^{-1}` for `Re s > 1`.
-/

open scoped Classical BigOperators NumberField
open Polynomial IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

attribute [local instance] Ideal.Quotient.field

open HeckeLFunctions

/-- The line of a character composed with a homomorphism is the composition of the line. -/
theorem linearCharacterLine_comp {Γ Γ' : Type u} [Group Γ] [Group Γ'] (χ' : LinearCharacter Γ')
    (π : Γ →* Γ') :
    linearCharacterLine (χ'.comp π) = (linearCharacterLine χ').comp π :=
  MonoidHom.ext fun _ => rfl

variable (K M L : Type u) {G G' V : Type u} [Field K] [NumberField K] [Field M] [NumberField M]
  [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [Group G'] [Fintype G'] [MulSemiringAction G' M] [IsGaloisGroup G' K M]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-! ### The restriction of automorphisms -/

/-- The restriction acts on the integers of `M` as the automorphism of `L`. -/
theorem algebraMap_restrictHom_smul_ringOfIntegers (g : G) (b : 𝓞 M) :
    algebraMap (𝓞 M) (𝓞 L) (IsGaloisGroup.restrictHom G G' K M L g • b) =
      g • algebraMap (𝓞 M) (𝓞 L) b :=
  NumberField.RingOfIntegers.ext (IsGaloisGroup.algebraMap_restrictHom_smul G G' K M L g (b : M))

/-- An automorphism of `L` that fixes `M` restricts to the identity. -/
theorem restrictHom_eq_one_of_mem_fixingSubgroup {h : G}
    (hh : h ∈ fixingSubgroup G (Set.range (algebraMap M L))) :
    IsGaloisGroup.restrictHom G G' K M L h = 1 := by
  haveI : FaithfulSMul G' M := IsGaloisGroup.faithful K
  refine eq_of_smul_eq_smul fun x : M => ?_
  rw [one_smul]
  apply (algebraMap M L).injective
  rw [IsGaloisGroup.algebraMap_restrictHom_smul]
  exact (mem_fixingSubgroup_iff G).mp hh _ ⟨x, rfl⟩

/-! ### Euler factors and Euler products -/

/-- **The local Euler polynomial of an inflated representation** is the local Euler polynomial
of the representation over the intermediate field. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_inflation (v : HeightOneSpectrum (𝓞 K))
    (ρ' : Representation ℂ G' V) :
    numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v
        (ρ'.comp (IsGaloisGroup.restrictHom G G' K M L)) =
      numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := M) v ρ' := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  haveI := hQmax.isPrime
  haveI : (Q.under (𝓞 M)).LiesOver v.asIdeal :=
    Ideal.under_liesOver_of_liesOver (𝓞 M) Q v.asIdeal
  haveI : (Q.under (𝓞 M)).IsMaximal := inferInstance
  -- the automorphisms of `L` over `M`
  haveI : IsGaloisGroup (fixingSubgroup G (Set.range (algebraMap M L))) M L :=
    IsGaloisGroup.of_isScalarTower G K L M
  haveI := isGaloisGroup_subgroup_ringOfIntegers (M := M) (L := L)
    (fixingSubgroup G (Set.range (algebraMap M L)))
  rw [← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
      (K := K) (L := L) (G := G) v Q,
    ← frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
      (K := K) (L := M) (G := G') v (Q.under (𝓞 M))]
  exact frobeniusInertiaEulerPolynomial_comp_eq (A := 𝓞 K)
    (IsGaloisGroup.restrictHom G G' K M L) (algebraMap_restrictHom_smul_ringOfIntegers K M L)
    (fixingSubgroup G (Set.range (algebraMap M L)))
    (IsGaloisGroup.restrictHom_surjective G G' K M L)
    (fun _ hh => restrictHom_eq_one_of_mem_fixingSubgroup K M L hh) Q ρ'

/-- **Inflation invariance**: `L(s, ρ' ∘ π, L/K) = L(s, ρ', M/K)`. -/
theorem numberFieldFinitePlaceArtinEulerReciprocalProduct_inflation
    (ρ' : Representation ℂ G' V) (s : ℂ) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
        (ρ'.comp (IsGaloisGroup.restrictHom G G' K M L)) s =
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := M) ρ' s := by
  unfold numberFieldFinitePlaceArtinEulerReciprocalProduct
  refine tprod_congr fun v => ?_
  unfold numberFieldFinitePlaceArtinEulerReciprocal
  rw [numberFieldFinitePlaceLocalEulerPolynomial_inflation K M L]

/-! ### Linear characters -/

/-- **The Artin symbol is invariant under inflation.** -/
theorem artinSymbol_inflation (χ' : LinearCharacter G') (v : HeightOneSpectrum (𝓞 K)) :
    artinSymbol K L (χ'.comp (IsGaloisGroup.restrictHom G G' K M L)) v =
      artinSymbol K M χ' v := by
  unfold artinSymbol
  rw [linearCharacterLine_comp, numberFieldFinitePlaceLocalEulerPolynomial_inflation K M L]

section Cyclotomic

variable (G)

include G in
/-- **Abelian Artin Euler products inside a cyclotomic extension are Hecke `L`-series.** If
`L = K(ζ)` for a primitive `m`-th root of unity `ζ` and `M` is an intermediate field of `L/K`,
then for every linear character `χ'` of `Gal(M/K)` there is a ray class character `ψ` modulo
`(m) ∞` with `L(s, χ', M/K) = L(s, ψ) · Π_{v | m} (1 − (χ', v) N(v)^{-s})^{-1}` for
`Re s > 1`. -/
theorem exists_artinEulerProduct_eq_heckeL_mul_of_adjoin_eq_top_of_tower {m : ℕ} [NeZero m]
    {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ m) (hL : IntermediateField.adjoin K {(ζ : L)} = ⊤)
    (χ' : LinearCharacter G') :
    ∃ ψ : HeckeCharacter (normModulus K m), ∀ s : ℂ, 1 < s.re →
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := M)
        (linearCharacterLine χ') s = heckeL (normModulus K m) ψ s *
          ∏ v ∈ (finite_primes_dvd (normModulus K m)).toFinset,
            (1 - artinSymbol K M χ' v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨ψ, hψ⟩ := exists_artinEulerProduct_eq_heckeL_mul_of_adjoin_eq_top (G := G) hζ hL
    (χ'.comp (IsGaloisGroup.restrictHom G G' K M L))
  refine ⟨ψ, fun s hs => ?_⟩
  have h := hψ s hs
  rw [linearCharacterLine_comp,
    numberFieldFinitePlaceArtinEulerReciprocalProduct_inflation K M L] at h
  rw [h]
  congr 1
  exact Finset.prod_congr rfl fun v _ => by rw [artinSymbol_inflation K M L]

end Cyclotomic

end GaloisForLFunctions
