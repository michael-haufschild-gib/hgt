import GaloisForLFunctions.RHTower.Artin.TheArtinSymbolsOfALinearCharacterAreTheValuesOfAPrimitiveRayClassCharacter
import GaloisForLFunctions.RHTower.Artin.InvariantDivisorsDescendOutsideALargeSetOfPrimes

/-!
# A linear character with trivial Artin symbols at almost all primes is trivial

Let `L/K` be a Galois extension of number fields with group `G` and `χ` a linear character of
`G`.

* **The Artin symbols determine the character** (`eq_one_of_forall_artinSymbol_eq_one`). If
  `(χ, v) = 1` for all primes `v` of norm `> B`, then `χ = 1`. For abelian `G`: almost all
  primes are unramified, with `(χ, v) = χ(Frob_v)`, so `ker χ` contains almost all Frobenius
  elements, and these generate `G`. In general `χ` is inflated from the abelian group
  `G / ker χ`, the group of the fixed field of `ker χ`, with the same Artin symbols.
* **A nontrivial character has a nontrivial ray class character**
  (`heckeCharacter_ne_one_of_artinSymbol`): a ray class character `ψ` modulo `𝔪` with
  `(χ, v) = ψ(v)` for `v ∤ 𝔪` is nontrivial if `χ` is.
* **Reciprocity with a primitive nontrivial character**
  (`exists_primitive_heckeCharacter_ne_one_artinSymbol`): for `χ ≠ 1` the primitive ray class
  character with the Artin symbols of `χ` as values outside `c` is nontrivial.
-/

open scoped Classical BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-- The norms of the primes of a finite set are bounded. -/
theorem exists_forall_absNorm_le_of_finite {K : Type*} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    ∃ B : ℕ, ∀ v ∈ S, Ideal.absNorm v.asIdeal ≤ B := by
  obtain ⟨B, hB⟩ := (hS.image fun v => Ideal.absNorm v.asIdeal).bddAbove
  exact ⟨B, fun v hv => hB (Set.mem_image_of_mem _ hv)⟩

section Abelian

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **A character of an abelian Galois group with trivial Artin symbols at almost all primes
is trivial**: its kernel contains the Frobenius elements of almost all primes. -/
theorem eq_one_of_forall_artinSymbol_eq_one_of_comm (χ : LinearCharacter G) {B : ℕ}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), B < Ideal.absNorm v.asIdeal →
      artinSymbol K L χ v = 1) : χ = 1 := by
  obtain ⟨B₀, hB₀⟩ := exists_forall_absNorm_le_of_finite
    (finite_not_isUnramifiedPrime (K := K) (L := L) (G := G))
  have htop : χ.ker = ⊤ := eq_top_of_forall_frobeniusElement_mem (K := K) (L := L) χ.ker
    (B := max B B₀) fun v hv => by
      have hunr : IsUnramifiedPrime K L G v := by
        by_contra hram
        exact absurd (hB₀ v hram) (not_le.mpr ((le_max_right B B₀).trans_lt hv))
      refine ⟨hunr, MonoidHom.mem_ker.mpr (Units.ext ?_)⟩
      rw [← artinSymbol_eq_apply_frobeniusElement χ hunr, h v ((le_max_left B B₀).trans_lt hv),
        Units.val_one]
  exact MonoidHom.ext fun g => MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top g)

end Abelian

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- An Artin symbol is `0` or a root of unity: `|(χ, v)| ≤ 1`. -/
theorem norm_artinSymbol_le_one (χ : LinearCharacter G) (v : HeightOneSpectrum (𝓞 K)) :
    ‖artinSymbol K L χ v‖ ≤ 1 := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  rw [artinSymbol_eq_frobeniusValue K L χ v Q, frobeniusValue]
  split_ifs
  · exact (norm_char_eq_one χ _).le
  · rw [norm_zero]
    exact zero_le_one

/-- **A linear character with trivial Artin symbols at almost all primes is trivial.** -/
theorem eq_one_of_forall_artinSymbol_eq_one (χ : LinearCharacter G) {B : ℕ}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), B < Ideal.absNorm v.asIdeal →
      artinSymbol K L χ v = 1) : χ = 1 := by
  -- `χ` is inflated from the cyclic group `G / ker χ` of the fixed field of `ker χ`
  haveI : IsCyclic (G ⧸ χ.ker) := isCyclic_quotient_ker χ
  letI : CommGroup (G ⧸ χ.ker) := IsCyclic.commGroup
  letI : Fintype (G ⧸ χ.ker) := Fintype.ofFinite _
  have hχ : (QuotientGroup.kerLift χ).comp (IsGaloisGroup.restrictHom G (G ⧸ χ.ker) K
      (FixedPoints.intermediateField χ.ker : IntermediateField K L) L) = χ :=
    MonoidHom.ext fun g =>
      congrArg (QuotientGroup.kerLift χ) (restrictHom_fixedPoints_eq_mk K L χ.ker g)
  have h1 : QuotientGroup.kerLift χ = 1 :=
    eq_one_of_forall_artinSymbol_eq_one_of_comm K
      (FixedPoints.intermediateField χ.ker : IntermediateField K L) (G := G ⧸ χ.ker)
      (QuotientGroup.kerLift χ) (B := B) fun v hv =>
        ((artinSymbol_inflation K (FixedPoints.intermediateField χ.ker : IntermediateField K L)
          L (G := G) (QuotientGroup.kerLift χ) v).symm.trans
          (congrArg (fun χ₀ : LinearCharacter G => artinSymbol K L χ₀ v) hχ)).trans (h v hv)
  rw [← hχ, h1, MonoidHom.one_comp]

/-- **A nontrivial linear character has a nontrivial ray class character**: a ray class
character modulo `𝔪` with the Artin symbols of `χ ≠ 1` as values outside `𝔪` is not trivial. -/
theorem heckeCharacter_ne_one_of_artinSymbol {χ : LinearCharacter G} (hχ : χ ≠ 1)
    (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (hval : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin →
      artinSymbol K L χ v = heckeValue 𝔪 ψ v.asIdeal) : ψ ≠ 1 := by
  rintro rfl
  obtain ⟨B, hB⟩ := exists_forall_absNorm_le_of_finite (finite_primes_dvd 𝔪)
  refine hχ (eq_one_of_forall_artinSymbol_eq_one K L χ (B := B) fun v hv => ?_)
  have hdvd : ¬ v.asIdeal ∣ 𝔪.fin := fun hd => absurd (hB v hd) (not_le.mpr hv)
  rw [hval v hdvd, heckeValue_one_prime, if_neg hdvd]

/-- **Reciprocity with a primitive nontrivial character.** For a linear character `χ ≠ 1` of
the group of a Galois extension `L/K` there are `c ≥ 1` and a primitive ray class character
`ψ ≠ 1` with `(χ, v) = ψ(v)` for `v ∤ c` and, for `Re s > 1`,
`L(s, χ, L/K) = L(s, ψ) · Π_{v | c} (1 − ψ(v) N(v)^{-s}) (1 − (χ, v) N(v)^{-s})^{-1}`. -/
theorem exists_primitive_heckeCharacter_ne_one_artinSymbol {χ : LinearCharacter G}
    (hχ : χ ≠ 1) :
    ∃ (c : ℕ) (_ : NeZero c) (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫),
      heckeFiniteConductor 𝔫 ψ = 𝔫.fin ∧ ψ ≠ 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (normModulus K c).fin →
        artinSymbol K L χ v = heckeValue 𝔫 ψ v.asIdeal) ∧
      ∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
          (linearCharacterLine χ) s = heckeL 𝔫 ψ s *
            ∏ v ∈ (finite_primes_dvd (normModulus K c)).toFinset,
              ((1 - heckeValue 𝔫 ψ v.asIdeal * (v.asIdeal.absNorm : ℂ) ^ (-s)) *
                (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) := by
  obtain ⟨c, hc, ψ, hval, hL⟩ := exists_artinEulerProduct_linearCharacter_eq_heckeL_mul K L χ
  have hψ : ψ ≠ 1 := heckeCharacter_ne_one_of_artinSymbol K L hχ (normModulus K c) ψ hval
  refine ⟨c, hc, conductorModulus (normModulus K c) ψ, primitiveHecke (normModulus K c) ψ,
    heckeFiniteConductor_primitiveHecke (normModulus K c) ψ,
    fun h => hψ ((primitiveHecke_eq_one_iff (normModulus K c) ψ).mp h), fun v hv => ?_,
    fun s hs => ?_⟩
  · rw [hval v hv, heckeValue_primitiveHecke_prime (normModulus K c) ψ v hv]
  · rw [hL s hs, heckeL_eq_heckeL_primitiveHecke_mul (normModulus K c) ψ hs, mul_assoc,
      ← Finset.prod_mul_distrib]

end GaloisForLFunctions
