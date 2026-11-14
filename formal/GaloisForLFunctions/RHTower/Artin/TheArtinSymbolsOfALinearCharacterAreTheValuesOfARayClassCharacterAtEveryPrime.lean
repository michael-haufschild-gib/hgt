import GaloisForLFunctions.RHTower.Artin.TheArtinMapIsTrivialOnARayWithOnlyRamifiedPrimesInTheModulus
import GaloisForLFunctions.RHTower.Artin.TheReciprocityLawForLinearCharacters

/-!
# The Artin symbols of a linear character are the values of a ray class character at every prime

Let `L/K` be a Galois extension of number fields with group `G` and `χ` a linear character of
`G`. The Artin symbol `(χ, v)` is `χ(Frob_v)` if `χ` is trivial on the inertia groups above
`v`, and `0` otherwise.

**Theorem** (`exists_heckeCharacter_forall_artinSymbol`). There are a modulus `𝔪` of `K` and a
ray class character `ψ` modulo `𝔪` with `(χ, v) = ψ(v)` at every prime `v` of `K`; the primes
dividing `𝔪` are the primes with `(χ, v) = 0`. Hence `L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`,
with no correcting Euler factor (`exists_artinEulerProduct_linearCharacter_eq_heckeL`).

Proof. `χ` is inflated from a faithful character `χ'` of `G / ker χ`, the group of the fixed
field `F` of `ker χ`, with the same Artin symbols. The Artin map of `F/K` is trivial on the ray
modulo `I ∞` for an ideal `I` whose prime divisors are the primes ramified in `F`; let
`ψ = χ' ∘ (·, F/K)`. A prime `v ∤ I` is unramified and `ψ(v) = χ'(Frob_v) = (χ', v) ≠ 0`. At
`v | I` an inertia group is not trivial and `χ'` is faithful, so `(χ', v) = 0 = ψ(v)`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-! ### Faithful characters of an abelian extension -/

section Abelian

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- The Artin symbol at an unramified prime is a root of unity. -/
theorem artinSymbol_ne_zero_of_isUnramifiedPrime (χ : LinearCharacter G)
    {v : HeightOneSpectrum (𝓞 K)} (hv : IsUnramifiedPrime K L G v) :
    artinSymbol K L χ v ≠ 0 := by
  rw [artinSymbol_eq_apply_frobeniusElement χ hv]
  exact Units.ne_zero _

/-- **A faithful character has Artin symbol `0` at a ramified prime**: it is not trivial on a
non-trivial inertia group. -/
theorem artinSymbol_eq_zero_of_injective {χ : LinearCharacter G} (hχ : Function.Injective χ)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ IsUnramifiedPrime K L G v) :
    artinSymbol K L χ v = 0 := by
  have hv' : ¬ ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.LiesOver v.asIdeal → Q.inertia G = ⊥ := hv
  obtain ⟨Q, hQ⟩ := not_forall.mp hv'
  obtain ⟨hQmax, hQ⟩ := Classical.not_imp.mp hQ
  obtain ⟨hQover, hne⟩ := Classical.not_imp.mp hQ
  haveI := hQmax
  haveI := hQover
  rw [artinSymbol_eq_frobeniusValue K L χ v Q, frobeniusValue, if_neg]
  exact fun h => hne ((Subgroup.eq_bot_iff_forall _).mpr fun τ hτ =>
    hχ ((h τ hτ).trans (map_one χ).symm))

/-- **Reciprocity at every prime for a faithful character of an abelian extension.** There are
a modulus `𝔪`, whose prime divisors are the primes ramified in `L`, and a ray class character
`ψ` modulo `𝔪` with `(χ, v) = ψ(v)` at every prime `v`. -/
theorem exists_heckeCharacter_forall_artinSymbol_of_injective {χ : LinearCharacter G}
    (hχ : Function.Injective χ) :
    ∃ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin ↔ ¬ IsUnramifiedPrime K L G v) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v = heckeValue 𝔪 ψ v.asIdeal := by
  obtain ⟨I, hI, hdvd, hrec⟩ := exists_ideal_rayPrincipal_le_ker_artinMap K L G
  have hram : ∀ v : HeightOneSpectrum (𝓞 K),
      ¬ v.asIdeal ∣ (⟨I, hI, Set.univ⟩ : Modulus K).fin → IsUnramifiedPrime K L G v :=
    fun v hv => not_not.mp fun h => hv ((hdvd v).mpr h)
  refine ⟨⟨I, hI, Set.univ⟩, artinHeckeCharacter K L G _ hrec χ, hdvd, fun v => ?_⟩
  by_cases hv : v.asIdeal ∣ I
  · -- a ramified prime: both sides vanish
    rw [artinSymbol_eq_zero_of_injective K L G hχ ((hdvd v).mp hv)]
    refine (heckeValue_of_not_mem _ _ ?_).symm
    rintro ⟨hI', hm⟩
    have h := hm v hv
    rw [coe_idealUnit, count_self] at h
    exact one_ne_zero h
  · exact (heckeValue_artinHeckeCharacter K L G _ hrec hram χ v hv).symm

end Abelian

/-! ### Linear characters of a Galois extension -/

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The Artin symbols of a linear character are the values of a ray class character at every
prime.** For a Galois extension `L/K` of number fields with group `G` and a linear character
`χ` of `G` there are a modulus `𝔪` and a ray class character `ψ` modulo `𝔪` with
`(χ, v) = ψ(v)` for every prime `v` of `K`; the primes dividing `𝔪` are those with
`(χ, v) = 0`. -/
theorem exists_heckeCharacter_forall_artinSymbol (χ : LinearCharacter G) :
    ∃ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin ↔ artinSymbol K L χ v = 0) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v = heckeValue 𝔪 ψ v.asIdeal := by
  -- `G / ker χ` is cyclic, the Galois group of the fixed field of `ker χ`
  haveI : IsCyclic (G ⧸ χ.ker) := isCyclic_quotient_ker χ
  letI : CommGroup (G ⧸ χ.ker) := IsCyclic.commGroup
  letI : Fintype (G ⧸ χ.ker) := Fintype.ofFinite _
  obtain ⟨𝔪, ψ, hdvd, hψ⟩ := exists_heckeCharacter_forall_artinSymbol_of_injective K
    (FixedPoints.intermediateField χ.ker : IntermediateField K L) (G ⧸ χ.ker)
    (QuotientGroup.kerLift_injective χ)
  -- `χ` is the inflation of the faithful character of `G / ker χ`
  have hχ : (QuotientGroup.kerLift χ).comp (IsGaloisGroup.restrictHom G (G ⧸ χ.ker) K
      (FixedPoints.intermediateField χ.ker : IntermediateField K L) L) = χ :=
    MonoidHom.ext fun g =>
      congrArg (QuotientGroup.kerLift χ) (restrictHom_fixedPoints_eq_mk K L χ.ker g)
  have hsym : ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v =
      artinSymbol K (FixedPoints.intermediateField χ.ker : IntermediateField K L)
        (QuotientGroup.kerLift χ) v := fun v =>
    (congrArg (fun χ₀ : LinearCharacter G => artinSymbol K L χ₀ v) hχ).symm.trans
      (artinSymbol_inflation K (FixedPoints.intermediateField χ.ker : IntermediateField K L) L
        (G := G) (QuotientGroup.kerLift χ) v)
  refine ⟨𝔪, ψ, fun v => ?_, fun v => (hsym v).trans (hψ v)⟩
  rw [hsym v, hdvd v]
  exact ⟨fun h => artinSymbol_eq_zero_of_injective K _ (G ⧸ χ.ker)
      (QuotientGroup.kerLift_injective χ) h,
    fun h hunr => artinSymbol_ne_zero_of_isUnramifiedPrime K _ (G ⧸ χ.ker)
      (QuotientGroup.kerLift χ) hunr h⟩

/-- **The Artin Euler product of a linear character is a Hecke `L`-series.** For a Galois
extension `L/K` of number fields with group `G` and a linear character `χ` of `G` there is a
ray class character `ψ` of `K` with `(χ, v) = ψ(v)` at every prime and
`L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`. -/
theorem exists_artinEulerProduct_linearCharacter_eq_heckeL (χ : LinearCharacter G) :
    ∃ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin ↔ artinSymbol K L χ v = 0) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v = heckeValue 𝔪 ψ v.asIdeal) ∧
      ∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
          (linearCharacterLine χ) s = heckeL 𝔪 ψ s := by
  obtain ⟨𝔪, ψ, hdvd, hψ⟩ := exists_heckeCharacter_forall_artinSymbol K L χ
  exact ⟨𝔪, ψ, hdvd, hψ, fun s hs =>
    artinEulerProduct_linearCharacter_eq_heckeL K L χ 𝔪 ψ hψ hs⟩

end GaloisForLFunctions
