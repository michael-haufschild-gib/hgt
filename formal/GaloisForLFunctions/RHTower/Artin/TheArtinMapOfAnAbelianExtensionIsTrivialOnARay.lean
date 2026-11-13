import GaloisForLFunctions.RHTower.Artin.TheReciprocityLawForLinearCharacters
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Artin map of an abelian extension is trivial on a ray

**The reciprocity law for abelian extensions** (`exists_rayPrincipal_le_ker_artinMap`). Let
`L/K` be an abelian extension of number fields with group `G`. There is `c ≥ 1`, divisible by
the ramified primes, such that the Artin symbol `((α), L/K)` is trivial for every
`α ≡ 1 mod^× c` positive at the real places.

Proof. For a tower `K ⊂ F ⊂ L` the restriction `G → Gal(F/K)` maps the Artin symbol of an ideal
whose primes are unramified in `L` to its Artin symbol in `F/K` (`restrictHom_artinMap`). A
character `χ` of `G` factors through the cyclic group `G / ker χ`, the Galois group of the fixed
field `F_χ` of `ker χ`; the reciprocity law for the cyclic extension `F_χ/K` gives `c_χ` with
`χ((α), L/K) = 1` on the ray modulo `(N) ∞` for every multiple `N` of `c_χ` divisible by the
ramified primes (`exists_forall_apply_artinMap_eq_one`). Choose for every `g ≠ 1` in `G` a
character `χ_g` with `χ_g(g) ≠ 1` and take for `c` the product of the `c_{χ_g}` and of an
integer divisible by the ramified primes: an Artin symbol `g ≠ 1` on the ray modulo `(c) ∞`
would have `χ_g(g) = 1`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

section Tower

variable (K L M : Type u) {G Γ : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [CommGroup Γ] [Fintype Γ] [MulSemiringAction Γ M] [IsGaloisGroup Γ K M]

/-- **The Artin symbol restricts to the Artin symbol**: for an ideal `I` of `K` whose primes
are unramified in `L` and in `M`, the restriction of `(I, M/K)` to `L` is `(I, L/K)`. -/
theorem restrictHom_artinMap {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 →
      IsUnramifiedPrime K L G v ∧ IsUnramifiedPrime K M Γ v) :
    IsGaloisGroup.restrictHom Γ G K L M (artinMap K M Γ I) = artinMap K L G I := by
  show (IsGaloisGroup.restrictHom Γ G K L M).comp (primeValuesHom (frobeniusOrOne K M Γ)) I =
    primeValuesHom (frobeniusOrOne K L G) I
  rw [comp_primeValuesHom]
  refine primeValuesHom_congr I fun v hv => ?_
  show IsGaloisGroup.restrictHom Γ G K L M
      (if IsUnramifiedPrime K M Γ v then frobeniusElement K M Γ v else 1) =
    if IsUnramifiedPrime K L G v then frobeniusElement K L G v else 1
  rw [if_pos (h v hv).2, if_pos (h v hv).1]
  exact restrictHom_frobeniusElement K L M (h v hv).1

end Tower

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **A character of the Artin symbol is trivial on a ray.** For a character `χ` of the group
of an abelian extension `L/K` there is `c ≥ 1` such that `χ((α), L/K) = 1` on the ray modulo
`(N) ∞`, for every multiple `N` of `c` divisible by the primes ramified in `L`. -/
theorem exists_forall_apply_artinMap_eq_one (χ : LinearCharacter G) :
    ∃ c : ℕ, c ≠ 0 ∧ ∀ (N : ℕ) [NeZero N], c ∣ N →
      (∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∉ v.asIdeal → IsUnramifiedPrime K L G v) →
      ∀ I ∈ rayPrincipal (normModulus K N), χ (artinMap K L G I) = 1 := by
  -- the cyclic extension `F/K`, `F` the fixed field of `ker χ`
  haveI : IsCyclic (G ⧸ χ.ker) := isCyclic_quotient_ker χ
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := G ⧸ χ.ker)
  obtain ⟨c, hc, hram, hrec⟩ := exists_rayPrincipal_le_ker_artinMap_of_forall_mem_zpowers K
    (FixedPoints.intermediateField χ.ker : IntermediateField K L) (G ⧸ χ.ker) hσ
  refine ⟨c, NeZero.ne c, fun N _ hcN hN I hI => ?_⟩
  -- the primes of `I` are unramified in `F` and in `L`
  have hI' := rayPrincipal_le (normModulus K N) hI
  have hur : ∀ v : HeightOneSpectrum (𝓞 K),
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 →
      IsUnramifiedPrime K (FixedPoints.intermediateField χ.ker : IntermediateField K L)
        (G ⧸ χ.ker) v ∧ IsUnramifiedPrime K L G v := fun v hv => by
    have hNv : (N : 𝓞 K) ∉ v.asIdeal := fun h =>
      hv (hI' v ((dvd_normModulus_fin_iff K N v).mpr h))
    exact ⟨hram v fun h => hNv (Ideal.mem_of_dvd _ (Nat.cast_dvd_cast hcN) h), hN v hNv⟩
  have h1 := restrictHom_artinMap K
    (FixedPoints.intermediateField χ.ker : IntermediateField K L) L (G := G ⧸ χ.ker) (Γ := G) hur
  -- the class of `(I, L/K)` in `G / ker χ` is `(I, F/K) = 1`
  have h2 : (QuotientGroup.mk (artinMap K L G I) : G ⧸ χ.ker) = 1 :=
    (restrictHom_fixedPoints_eq_mk K L χ.ker (artinMap K L G I)).symm.trans
      (h1.trans (MonoidHom.mem_ker.mp (hrec (rayPrincipal_normModulus_le_of_dvd K hcN hI))))
  exact MonoidHom.mem_ker.mp ((QuotientGroup.eq_one_iff _).mp h2)

variable (G) in
/-- **The reciprocity law for abelian extensions.** For an abelian extension `L/K` of number
fields there is `c ≥ 1`, divisible by the ramified primes, such that the Artin map is trivial on
the principal ideals of the ray modulo `(c) ∞`. -/
theorem exists_rayPrincipal_le_ker_artinMap :
    ∃ (c : ℕ) (_ : NeZero c),
      (∀ v : HeightOneSpectrum (𝓞 K), (c : 𝓞 K) ∉ v.asIdeal → IsUnramifiedPrime K L G v) ∧
      rayPrincipal (normModulus K c) ≤ (artinMap K L G).ker := by
  obtain ⟨q, S, hq, hSq, hram, -, -⟩ := exists_nat_unramified_principalOutside K L G
  choose cχ hcχ0 hcχ using fun χ : LinearCharacter G =>
    exists_forall_apply_artinMap_eq_one K L χ
  -- a character that separates `g` from `1`
  have hsep : ∀ g : G, ∃ χ : LinearCharacter G, g ≠ 1 → χ g ≠ 1 := fun g => by
    by_cases hg : g = 1
    · exact ⟨1, fun h => (h hg).elim⟩
    · obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
      exact ⟨χ, fun _ => hχ⟩
  choose φ hφ using hsep
  have hN : NeZero (q * ∏ g : G, cχ (φ g)) :=
    ⟨mul_ne_zero hq (Finset.prod_ne_zero_iff.mpr fun g _ => hcχ0 (φ g))⟩
  haveI := hN
  have hur : ∀ v : HeightOneSpectrum (𝓞 K),
      ((q * ∏ g : G, cχ (φ g) : ℕ) : 𝓞 K) ∉ v.asIdeal → IsUnramifiedPrime K L G v :=
    fun v hv => hram v fun hS => hv (by
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ ((hSq v).mp hS))
  refine ⟨q * ∏ g : G, cχ (φ g), hN, hur, fun I hI => ?_⟩
  by_contra hne
  exact hφ _ (fun h => hne (MonoidHom.mem_ker.mpr h))
    (hcχ (φ (artinMap K L G I)) (q * ∏ g : G, cχ (φ g))
      (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun g => cχ (φ g)) (Finset.mem_univ _)) q)
      hur I hI)

end GaloisForLFunctions
