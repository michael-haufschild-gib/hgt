import GaloisForLFunctions.RHTower.Artin.TheArtinMapOfACyclicExtensionIsTrivialOnARay
import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductIsInvariantUnderInflation
import Mathlib.RingTheory.IntegralDomain

/-!
# The reciprocity law for linear characters

**Artin's reciprocity law** (`exists_artinEulerProduct_linearCharacter_eq_heckeL_mul`). Let
`L/K` be a Galois extension of number fields with group `G` and `χ` a linear character of `G`.
There are `c ≥ 1` and a ray class character `ψ` modulo `(c) ∞` with `(χ, v) = ψ(v)` for every
prime `v ∤ c`, and

  `L(s, χ, L/K) = L(s, ψ) · Π_{v | c} (1 − (χ, v) N(v)^{-s})^{-1}`  for `Re s > 1`.

Proof. `G / ker χ` embeds into `ℂ^×`, so it is cyclic (`isCyclic_quotient_ker`); it is the
Galois group of the fixed field `F` of `ker χ` over `K`, and the restriction `G → Gal(F/K)` is
the quotient map (`restrictHom_fixedPoints_eq_mk`). For the cyclic extension `F/K` the Artin
map is trivial on a ray modulo `(c) ∞`, so `χ' ∘ (·, F/K)` is a ray class character for the
character `χ'` of `G / ker χ` induced by `χ`
(`exists_heckeCharacter_artinSymbol_of_forall_mem_zpowers`). The Artin symbols of `χ` over
`L/K` are those of `χ'` over `F/K` (inflation).
-/

open scoped Classical BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-! ### The fixed field of a normal subgroup -/

section FixedField

variable (K L : Type u) {G : Type u} [Field K] [Field L] [Algebra K L] [Group G] [Finite G]
  [MulSemiringAction G L] [IsGaloisGroup G K L] (N : Subgroup G) [N.Normal]

omit [Finite G] in
/-- The class of `g` in `G / N` acts on the fixed field of `N` as `g`. -/
theorem algebraMap_quotient_smul_fixedPoints (g : G)
    (x : (FixedPoints.intermediateField N : IntermediateField K L)) :
    algebraMap (FixedPoints.intermediateField N : IntermediateField K L) L ((g : G ⧸ N) • x) =
      g • algebraMap (FixedPoints.intermediateField N : IntermediateField K L) L x :=
  IsGaloisGroup.algebraMap_smulOfNormal G _ L N g x

/-- **The restriction to the fixed field of `N` is the quotient map `G → G / N`.** -/
theorem restrictHom_fixedPoints_eq_mk (g : G) :
    IsGaloisGroup.restrictHom G (G ⧸ N) K
      (FixedPoints.intermediateField N : IntermediateField K L) L g = (g : G ⧸ N) := by
  haveI : FaithfulSMul (G ⧸ N) (FixedPoints.intermediateField N : IntermediateField K L) :=
    IsGaloisGroup.faithful K
  refine eq_of_smul_eq_smul
    fun x : (FixedPoints.intermediateField N : IntermediateField K L) => ?_
  apply FaithfulSMul.algebraMap_injective
    (FixedPoints.intermediateField N : IntermediateField K L) L
  rw [IsGaloisGroup.algebraMap_restrictHom_smul, algebraMap_quotient_smul_fixedPoints]

end FixedField

/-- **A linear character of a finite group factors through a cyclic quotient.** -/
theorem isCyclic_quotient_ker {G : Type*} [Group G] [Finite G] (χ : G →* ℂˣ) :
    IsCyclic (G ⧸ χ.ker) :=
  isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (QuotientGroup.kerLift χ))
    (Units.val_injective.comp (QuotientGroup.kerLift_injective χ))

/-! ### The reciprocity law -/

section Cyclic

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The reciprocity law for a cyclic extension.** There are `c ≥ 1` and, for every character
`χ` of `G`, a ray class character modulo `(c) ∞` with the values `(χ, v)` at the primes
`v ∤ c`: the character `χ ∘ (·, L/K)`. -/
theorem exists_heckeCharacter_artinSymbol_of_forall_mem_zpowers {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (χ : LinearCharacter G) :
    ∃ (c : ℕ) (_ : NeZero c) (ψ : HeckeCharacter (normModulus K c)),
      ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (normModulus K c).fin →
        artinSymbol K L χ v = heckeValue (normModulus K c) ψ v.asIdeal := by
  obtain ⟨c, hc, hram, hrec⟩ :=
    exists_rayPrincipal_le_ker_artinMap_of_forall_mem_zpowers K L G hσ
  have hram' : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (normModulus K c).fin →
      IsUnramifiedPrime K L G v := fun v hv =>
    hram v fun h => hv ((dvd_normModulus_fin_iff K c v).mpr h)
  exact ⟨c, hc, artinHeckeCharacter K L G (normModulus K c) hrec χ, fun v hv =>
    (heckeValue_artinHeckeCharacter K L G (normModulus K c) hrec hram' χ v hv).symm⟩

end Cyclic

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The Artin symbols of a linear character are the values of a ray class character.** For a
Galois extension `L/K` of number fields with group `G` and a linear character `χ` of `G` there
are `c ≥ 1` and a ray class character `ψ` modulo `(c) ∞` with `(χ, v) = ψ(v)` for `v ∤ c`. -/
theorem exists_heckeCharacter_artinSymbol (χ : LinearCharacter G) :
    ∃ (c : ℕ) (_ : NeZero c) (ψ : HeckeCharacter (normModulus K c)),
      ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (normModulus K c).fin →
        artinSymbol K L χ v = heckeValue (normModulus K c) ψ v.asIdeal := by
  -- `G / ker χ` is cyclic, the Galois group of the fixed field of `ker χ`
  haveI : IsCyclic (G ⧸ χ.ker) := isCyclic_quotient_ker χ
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := G ⧸ χ.ker)
  letI : CommGroup (G ⧸ χ.ker) := IsCyclic.commGroup
  letI : Fintype (G ⧸ χ.ker) := Fintype.ofFinite _
  obtain ⟨c, hc, ψ, hψ⟩ := exists_heckeCharacter_artinSymbol_of_forall_mem_zpowers K
    (FixedPoints.intermediateField χ.ker : IntermediateField K L) (G := G ⧸ χ.ker) hσ
    (QuotientGroup.kerLift χ)
  -- `χ` is the inflation of the induced character of `G / ker χ`
  have hχ : (QuotientGroup.kerLift χ).comp (IsGaloisGroup.restrictHom G (G ⧸ χ.ker) K
      (FixedPoints.intermediateField χ.ker : IntermediateField K L) L) = χ :=
    MonoidHom.ext fun g =>
      congrArg (QuotientGroup.kerLift χ) (restrictHom_fixedPoints_eq_mk K L χ.ker g)
  refine ⟨c, hc, ψ, fun v hv => ?_⟩
  have hinf := artinSymbol_inflation K
    (FixedPoints.intermediateField χ.ker : IntermediateField K L) L (G := G)
    (QuotientGroup.kerLift χ) v
  exact (congrArg (fun χ₀ : LinearCharacter G => artinSymbol K L χ₀ v) hχ).symm.trans
    (hinf.trans (hψ v hv))

/-- **Artin's reciprocity law for linear characters.** For a Galois extension `L/K` of number
fields with group `G` and a linear character `χ` of `G` there are `c ≥ 1` and a ray class
character `ψ` modulo `(c) ∞` with `(χ, v) = ψ(v)` for every prime `v ∤ c` and
`L(s, χ, L/K) = L(s, ψ) · Π_{v | c} (1 − (χ, v) N(v)^{-s})^{-1}` for `Re s > 1`. -/
theorem exists_artinEulerProduct_linearCharacter_eq_heckeL_mul (χ : LinearCharacter G) :
    ∃ (c : ℕ) (_ : NeZero c) (ψ : HeckeCharacter (normModulus K c)),
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (normModulus K c).fin →
        artinSymbol K L χ v = heckeValue (normModulus K c) ψ v.asIdeal) ∧
      ∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
          (linearCharacterLine χ) s = heckeL (normModulus K c) ψ s *
            ∏ v ∈ (finite_primes_dvd (normModulus K c)).toFinset,
              (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨c, hc, ψ, hψ⟩ := exists_heckeCharacter_artinSymbol K L χ
  exact ⟨c, hc, ψ, hψ, fun s hs =>
    artinEulerProduct_linearCharacter_eq_heckeL_mul K L χ (normModulus K c) ψ hψ hs⟩

end GaloisForLFunctions
