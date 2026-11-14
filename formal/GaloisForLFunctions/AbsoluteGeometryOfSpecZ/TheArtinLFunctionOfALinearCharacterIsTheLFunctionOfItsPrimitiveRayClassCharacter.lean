import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.InAFactorizationOfADedekindZetaFunctionEveryPrimeOfAModulusDividesTheConductor
import GaloisForLFunctions.RHTower.Artin.TheArtinSymbolsOfALinearCharacterAreTheValuesOfARayClassCharacterAtEveryPrime
import GaloisForLFunctions.RHTower.Artin.TheDedekindZetaFunctionOfAnAbelianExtensionIsTheProductOfTheLSeriesOfItsCharacters

/-!
# The Artin `L`-function of a linear character is the `L`-function of its primitive ray class character

Let `L/K` be a Galois extension of number fields with group `G` and `χ` a linear character of
`G`, with Artin symbols `(χ, v)`: `χ(Frob_v)` if `χ` is trivial on the inertia groups above
`v`, and `0` otherwise.

**Theorem** (`exists_primitive_heckeCharacter_forall_artinSymbol`). There is a primitive ray
class character `ψ` of `K`, modulo `𝔫`, with `(χ, v) = ψ(v)` at every prime `v` of `K`. So

* a prime divides the conductor `𝔫` iff `(χ, v) = 0`, i.e. iff `χ` is ramified at `v`
  (the conductor and the ramification of `χ` have the same primes);
* `L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`, with no correcting Euler factor.

Proof. There is a ray class character `ψ₀` modulo `𝔪` with `(χ, v) = ψ₀(v)` at every prime,
`𝔪` divisible exactly by the primes with `(χ, v) = 0`. It remains to see that every prime of
`𝔪` divides the conductor of `ψ₀` (`dvd_heckeFiniteConductor_of_forall_artinSymbol_eq`): then
the primitive character of `ψ₀` vanishes at the primes of `𝔪` and agrees with `ψ₀` elsewhere.
Pass to the fixed field `F` of `ker χ`, abelian over `K`. Every character `η` of its group has
a ray class character with the Artin symbols of `η` at every prime, and

  `ζ_F(s) = Π_η L(s, η, F/K) = Π_η L(s, ψ_η)`,

a factorization of a Dedekind zeta function into ray class `L`-series: every prime of a
modulus divides the conductor.
-/

noncomputable section

open NumberField
open scoped Classical

universe u

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions IsDedekindDomain

attribute [local instance] finiteLinearCharacter fintypeLinearCharacter

/-! ### Abelian extensions -/

section Abelian

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- For a character of an abelian Galois group: a ray class character with its Artin symbols
at every prime has a conductor divisible by every prime of its modulus. -/
theorem dvd_heckeFiniteConductor_of_forall_artinSymbol_eq_of_comm (χ : LinearCharacter G)
    {𝔪 : Modulus K} {ψ : HeckeCharacter 𝔪}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v = heckeValue 𝔪 ψ v.asIdeal)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.fin) :
    v.asIdeal ∣ heckeFiniteConductor 𝔪 ψ := by
  -- a ray class character for every character of `G`, the given one for `χ`
  obtain ⟨P, hPχ, hP⟩ : ∃ P : LinearCharacter G → Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
      P χ = ⟨𝔪, ψ⟩ ∧ ∀ (η : LinearCharacter G) (w : HeightOneSpectrum (𝓞 K)),
        artinSymbol K L η w = heckeValue (P η).1 (P η).2 w.asIdeal := by
    choose 𝔪' ψ' _ hψ' using fun η : LinearCharacter G =>
      exists_heckeCharacter_forall_artinSymbol K L η
    refine ⟨Function.update (fun η => ⟨𝔪' η, ψ' η⟩) χ ⟨𝔪, ψ⟩, Function.update_self _ _ _,
      fun η w => ?_⟩
    by_cases hη : η = χ
    · subst hη
      rw [Function.update_self]
      exact h w
    · rw [Function.update_of_ne hη]
      exact hψ' η w
  -- the Dedekind zeta function of the top field is the product of their `L`-series
  have hζ : ∀ s : ℂ, 1 < s.re →
      dedekindZeta (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L) s =
        ∏ η : LinearCharacter G, heckeL (P η).1 (P η).2 s := fun s hs => by
    rw [dedekindZeta_eq_prod_artinEulerProduct K L (G := G)
      (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L) hs]
    exact Finset.prod_congr rfl fun η _ =>
      artinEulerProduct_linearCharacter_eq_heckeL K L η (P η).1 (P η).2 (hP η) hs
  have hmain : v.asIdeal ∣ (P χ).1.fin → v.asIdeal ∣ heckeFiniteConductor (P χ).1 (P χ).2 :=
    dvd_heckeFiniteConductor_of_dedekindZeta_eq_prod
      (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L)
      (fun η => (P η).1) (fun η => (P η).2) hζ χ
  rw [hPχ] at hmain
  exact hmain hv

end Abelian

/-! ### Linear characters of a Galois extension -/

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **Every prime of the modulus divides the conductor.** Let `χ` be a linear character of the
group of a Galois extension `L/K` of number fields and `ψ` a ray class character modulo `𝔪`
with `(χ, v) = ψ(v)` at every prime `v`. Then every prime dividing `𝔪` divides the conductor of
`ψ`. -/
theorem dvd_heckeFiniteConductor_of_forall_artinSymbol_eq (χ : LinearCharacter G)
    {𝔪 : Modulus K} {ψ : HeckeCharacter 𝔪}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v = heckeValue 𝔪 ψ v.asIdeal)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.fin) :
    v.asIdeal ∣ heckeFiniteConductor 𝔪 ψ := by
  -- `χ` is inflated from a character of the cyclic group `G / ker χ`
  haveI : IsCyclic (G ⧸ χ.ker) := isCyclic_quotient_ker χ
  letI : CommGroup (G ⧸ χ.ker) := IsCyclic.commGroup
  letI : Fintype (G ⧸ χ.ker) := Fintype.ofFinite _
  have hχ : (QuotientGroup.kerLift χ).comp (IsGaloisGroup.restrictHom G (G ⧸ χ.ker) K
      (FixedPoints.intermediateField χ.ker : IntermediateField K L) L) = χ :=
    MonoidHom.ext fun g =>
      congrArg (QuotientGroup.kerLift χ) (restrictHom_fixedPoints_eq_mk K L χ.ker g)
  refine dvd_heckeFiniteConductor_of_forall_artinSymbol_eq_of_comm K
    (FixedPoints.intermediateField χ.ker : IntermediateField K L) (G ⧸ χ.ker)
    (QuotientGroup.kerLift χ) (fun w => ?_) hv
  rw [← h w, ← artinSymbol_inflation K
    (FixedPoints.intermediateField χ.ker : IntermediateField K L) L (G := G)
    (QuotientGroup.kerLift χ) w, hχ]

/-- **The Artin `L`-function of a linear character is the `L`-function of its primitive ray
class character.** For a Galois extension `L/K` of number fields with group `G` and a linear
character `χ` of `G` there is a primitive ray class character `ψ` modulo `𝔫` with
`(χ, v) = ψ(v)` at every prime `v` of `K`. The primes of the conductor `𝔫` are the primes with
`(χ, v) = 0`, and `L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`. -/
theorem exists_primitive_heckeCharacter_forall_artinSymbol (χ : LinearCharacter G) :
    ∃ (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫), heckeFiniteConductor 𝔫 ψ = 𝔫.fin ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔫.fin ↔ artinSymbol K L χ v = 0) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v = heckeValue 𝔫 ψ v.asIdeal) ∧
      ∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
          (linearCharacterLine χ) s = heckeL 𝔫 ψ s := by
  obtain ⟨𝔪, ψ, hdvd, hψ⟩ := exists_heckeCharacter_forall_artinSymbol K L χ
  -- the conductor has the primes of the modulus
  have hcond : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal ∣ (conductorModulus 𝔪 ψ).fin ↔ v.asIdeal ∣ 𝔪.fin := fun v =>
    ⟨fun h => dvd_fin_of_dvd_divisorModulus 𝔪 (modulus_le_heckeFiniteConductor 𝔪 ψ) h,
      fun h => dvd_heckeFiniteConductor_of_forall_artinSymbol_eq K L χ hψ h⟩
  -- the primitive character has the Artin symbols of `χ` at every prime
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), artinSymbol K L χ v =
      heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal := fun v => by
    by_cases hv : v.asIdeal ∣ 𝔪.fin
    · rw [(hdvd v).mp hv]
      refine (heckeValue_of_not_mem _ _ ?_).symm
      rintro ⟨hI', hm⟩
      have h := hm v ((hcond v).mpr hv)
      rw [coe_idealUnit, FractionalIdeal.count_self] at h
      exact one_ne_zero h
    · rw [hψ v, heckeValue_primitiveHecke_prime 𝔪 ψ v hv]
  exact ⟨conductorModulus 𝔪 ψ, primitiveHecke 𝔪 ψ, heckeFiniteConductor_primitiveHecke 𝔪 ψ,
    fun v => (hcond v).trans (hdvd v), hval, fun s hs =>
      artinEulerProduct_linearCharacter_eq_heckeL K L χ _ _ hval hs⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
