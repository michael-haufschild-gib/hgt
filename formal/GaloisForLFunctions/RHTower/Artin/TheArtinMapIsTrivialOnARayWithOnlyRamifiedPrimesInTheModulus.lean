import GaloisForLFunctions.RHTower.Artin.NormsFromTheDecompositionFieldOfAnUnramifiedPrime
import GaloisForLFunctions.RHTower.Artin.EveryRayClassCharacterIsInducedFromAPrimitiveCharacterOfItsConductor

/-!
# The Artin map is trivial on a ray with only ramified primes in the modulus

Let `L/K` be an abelian extension of number fields with group `G`. A modulus is `I ∞`, `I ≠ 0`
an ideal of `𝓞_K` and `∞` all real places; `P_I` is the group of the principal ideals of its
ray.

**Removing an unramified prime** (`rayPrincipal_le_ker_artinMap_of_mul_pow`). Let the primes
`v ∤ I` be unramified in `L`, `u ∤ I` a prime and `e ≥ 1`. If the Artin map is trivial on
`P_{I u^e}`, it is trivial on `P_I`.

Proof. A ray element is a quotient of integers of the ray, so let `a ≡ 1 mod I` be a totally
positive integer, `a ∉ u^{j+1}`. Take `μ ∈ I ∖ u` and `m` prime to `N(u)` such that the order
of `N(u)` modulo `m` is divisible by `[L:K]` and `M = L(ζ_m)` has group `G × (ℤ/m)ˣ` over `K`.
The prime `u` is unramified in `M`; let `E` be its decomposition field. The cyclotomic
character is injective on `Gal(M/E) = ⟨Frob_u⟩`, so the Artin map of `M/E` is trivial on the
ray modulo `(m) ∞` of `E`. Take `β ∈ 𝓞_E` totally positive, `β ≡ 1 mod μ m` and
`b = N_{E/K} β ≡ a mod u^{e+j}`. Then `b ≡ 1 mod I` is totally positive, `a/b` lies in the ray
modulo `I u^e ∞`, and

  `((b), L/K) = ((b), M/K)|_L = ((β), M/E)|_L = 1`,

the primes of `(β)` and of `(b)` being prime to `μ m`, hence unramified in `L` and `M`.

**The modulus** (`exists_ideal_rayPrincipal_le_ker_artinMap`). There is an ideal `I ≠ 0`
whose prime divisors are the primes ramified in `L`, such that the Artin map is trivial on
`P_I`. Start from the reciprocity law modulo `(c) ∞` and remove the unramified primes of `c`
one by one.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions ArtinMertens

/-- A non-zero integer outside `u^{j+1}` has valuation at least `exp(−j)` at `u`. -/
theorem exp_neg_le_intValuation_of_notMem {K : Type*} [Field K] [NumberField K]
    (u : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) {j : ℕ}
    (h : b ∉ u.asIdeal ^ (j + 1)) : WithZero.exp (-(j : ℤ)) ≤ u.intValuation b := by
  have h' : ¬ u.intValuation b ≤ WithZero.exp (-((j + 1 : ℕ) : ℤ)) := fun hle =>
    h ((intValuation_le_pow_iff_mem u b (j + 1)).mp hle)
  rw [intValuation_def, if_neg hb] at h' ⊢
  rw [WithZero.exp_le_exp] at h' ⊢
  push_cast at h'
  omega

/-- A non-zero integer lies outside some power of a prime. -/
theorem exists_notMem_pow_succ {K : Type*} [Field K] [NumberField K]
    (u : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ≠ 0) : ∃ j : ℕ, a ∉ u.asIdeal ^ (j + 1) := by
  refine ⟨(Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {a})).factors, fun h => ?_⟩
  rw [← intValuation_le_pow_iff_mem, intValuation_def, if_neg ha, WithZero.exp_le_exp] at h
  push_cast at h
  omega

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The Artin symbol of an integer of the ray modulo `I ∞`**, when the Artin map is trivial
on the ray modulo `I u^e ∞` for an unramified prime `u ∤ I`. -/
theorem artinMap_toPrincipalIdeal_eq_one_of_mul_pow {I : Ideal (𝓞 K)}
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ I → IsUnramifiedPrime K L G v)
    (hI : I ≠ ⊥) (u : HeightOneSpectrum (𝓞 K)) (hu : ¬ u.asIdeal ∣ I) {e : ℕ} (he : e ≠ 0)
    (hIe : I * u.asIdeal ^ e ≠ ⊥)
    (hrec : rayPrincipal (⟨I * u.asIdeal ^ e, hIe, Set.univ⟩ : Modulus K) ≤
      (artinMap K L G).ker)
    {a : 𝓞 K} (ha0 : algebraMap (𝓞 K) K a ≠ 0) (ha : a - 1 ∈ I)
    (hpos : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.embedding_of_isReal hw (algebraMap (𝓞 K) K a)) :
    artinMap K L G (toPrincipalIdeal (𝓞 K) K (Units.mk0 _ ha0)) = 1 := by
  have ha0' : a ≠ 0 := fun h => ha0 (by rw [h, map_zero])
  obtain ⟨j, hj⟩ := exists_notMem_pow_succ u ha0'
  -- `μ ∈ I` outside `u`
  obtain ⟨μ, hμI, hμu⟩ : ∃ μ ∈ I, μ ∉ u.asIdeal := by
    by_contra h
    exact hu (Ideal.dvd_iff_le.mpr fun x hx => by_contra fun hxu => h ⟨x, hx, hxu⟩)
  -- the modulus `m`: the order of `N(u)` modulo `m` is divisible by `[L:K]`
  obtain ⟨m₀, hm₀, hirr⟩ := exists_forall_coprime_irreducible_cyclotomic L
  have hN2 : 2 ≤ Ideal.absNorm u.asIdeal := two_le_absNorm_of_isPrime u.isPrime u.ne_bot
  have ht : m₀ * Ideal.absNorm u.asIdeal ≠ 0 := Nat.mul_ne_zero hm₀ (by omega)
  obtain ⟨m, b, hm, hmt, harith⟩ :=
    exists_modulus_unit_forall_zpow_mul_zpow (n := Fintype.card G) Fintype.card_ne_zero
      {Ideal.absNorm u.asIdeal} (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hN2) ht
  haveI : NeZero m := ⟨hm⟩
  have hmm₀ : m.Coprime m₀ := Nat.Coprime.coprime_dvd_right (dvd_mul_right m₀ _) hmt
  have hum : (m : 𝓞 K) ∉ u.asIdeal :=
    natCast_notMem_of_absNorm_coprime u
      (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ m₀) hmt).symm
  -- the crossing `M = L(ζ_m)`
  obtain ⟨M, _, _, _, _, _, Γ, _, _, _, _, ζ, hζ, hbij⟩ :=
    exists_cyclotomic_crossing K L (G := G) (hirr m hm hmm₀)
  have hunr : ∀ v : HeightOneSpectrum (𝓞 K), μ * (m : 𝓞 K) ∉ v.asIdeal →
      IsUnramifiedPrime K L G v ∧ IsUnramifiedPrime K M Γ v := fun v hv => by
    have hvI : ¬ v.asIdeal ∣ I := fun h =>
      hv (v.asIdeal.mul_mem_right _ (Ideal.dvd_iff_le.mp h hμI))
    have hvm : (m : 𝓞 K) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
    exact ⟨hram v hvI, isUnramifiedPrime_of_injective_restrictHom_cyclotomicCharacter K L M hζ
      hbij.1 (hram v hvI) hvm⟩
  have hνu : μ * (m : 𝓞 K) ∉ u.asIdeal := fun h => (u.isPrime.mem_or_mem h).elim hμu hum
  have huM : IsUnramifiedPrime K M Γ u := (hunr u hνu).2
  -- the cyclotomic character is injective on `⟨Frob_u⟩`
  have hH : ∀ h ∈ Subgroup.zpowers (frobeniusElement K M Γ u),
      cyclotomicCharacter hζ h = 1 → h = 1 := by
    intro h hh hκ1
    obtain ⟨x, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [map_zpow] at hκ1
    obtain ⟨jx, rfl⟩ := (harith _ (Finset.mem_singleton_self _) _
      (coe_cyclotomicCharacter_frobeniusElement K M hζ u hum) x 0
      (by rw [zpow_zero, mul_one]; exact hκ1)).1
    refine hbij.1 (Prod.ext ?_ ?_)
    · show IsGaloisGroup.restrictHom Γ G K L M _ = IsGaloisGroup.restrictHom Γ G K L M 1
      rw [map_one, map_zpow, zpow_mul, zpow_natCast, pow_card_eq_one, one_zpow]
    · show cyclotomicCharacter hζ _ = cyclotomicCharacter hζ 1
      rw [map_one, map_zpow]
      exact hκ1
  have hκ : Function.Injective (cyclotomicCharacter
      (G := ↥(Subgroup.zpowers (frobeniusElement K M Γ u))) hζ) :=
    (injective_iff_map_eq_one _).mpr fun h hh =>
      Subtype.ext (hH h.1 h.2 ((cyclotomicCharacter_subgroup hζ _ h).symm.trans hh))
  -- `β` in the decomposition field with `N β ≡ a mod u^{e+j}`
  obtain ⟨β, hβ1, hβpos, hβN⟩ := exists_intNorm_sub_mem_pow K M Γ huM hνu a (e + j)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K,
      b = Algebra.intNorm (𝓞 K) (𝓞 (decompositionField K M Γ u)) β := ⟨_, rfl⟩
  rw [← hb] at hβN
  have hμm0 : algebraMap (𝓞 K) K (μ * (m : 𝓞 K)) ≠ 0 := fun h =>
    hνu (by
      rw [(FaithfulSMul.algebraMap_injective (𝓞 K) K) (h.trans (map_zero _).symm)]
      exact u.asIdeal.zero_mem)
  -- `b ≡ 1 mod μ m`
  have hb1 : b - 1 ∈ Ideal.span {μ * (m : 𝓞 K)} := by
    have h := intNorm_sub_intNorm_mem_span K (decompositionField K M Γ u) hμm0 (x := β)
      (y := 1) hβ1
    rwa [map_one, ← hb] at h
  have hbI : b - 1 ∈ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr (I.mul_mem_right _ hμI) hb1
  -- `b ∉ u^{j+1}`
  have hbj : b ∉ u.asIdeal ^ (j + 1) := fun h => hj (by
    have h1 : b - a ∈ u.asIdeal ^ (j + 1) :=
      Ideal.pow_le_pow_right (by have := Nat.pos_of_ne_zero he; omega) hβN
    have h2 := (u.asIdeal ^ (j + 1)).sub_mem h h1
    rwa [sub_sub_cancel] at h2)
  have hb0' : b ≠ 0 := fun h => hbj (h ▸ (u.asIdeal ^ (j + 1)).zero_mem)
  have hb0 : algebraMap (𝓞 K) K b ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hb0'
  have hnorm : Algebra.norm K (algebraMap (𝓞 (decompositionField K M Γ u))
      (decompositionField K M Γ u) β) = algebraMap (𝓞 K) K b := by
    rw [hb]
    exact (Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K) (L := decompositionField K M Γ u)
      (B := 𝓞 (decompositionField K M Γ u)) β).symm
  have hβE : algebraMap (𝓞 (decompositionField K M Γ u)) (decompositionField K M Γ u) β ≠ 0 :=
    fun h => hb0 (by rw [← hnorm, h, Algebra.norm_zero])
  -- `b` is totally positive
  have hbpos : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.embedding_of_isReal hw (algebraMap (𝓞 K) K b) := fun w hw => by
    rw [← hnorm]
    exact embedding_of_isReal_norm_pos K (decompositionField K M Γ u) hβE hβpos hw
  -- `a/b` lies in the ray modulo `I u^e ∞`
  have hγI : Units.mk0 _ ha0 / Units.mk0 _ hb0 ∈ rayGroup (⟨I, hI, Set.univ⟩ : Modulus K) :=
    Subgroup.div_mem _
      (mk0_mem_rayGroup (⟨I, hI, Set.univ⟩ : Modulus K) ha0 ha fun w => hpos w.1.1 w.1.2)
      (mk0_mem_rayGroup (⟨I, hI, Set.univ⟩ : Modulus K) hb0 hbI fun w => hbpos w.1.1 w.1.2)
  have hval : u.valuation K (((Units.mk0 _ ha0 / Units.mk0 _ hb0 : Kˣ) : K) - 1) ≤
      WithZero.exp (-(e : ℤ)) := by
    have h1 : ((Units.mk0 _ ha0 / Units.mk0 _ hb0 : Kˣ) : K) - 1 =
        algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K b := by
      rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, map_sub, sub_div,
        div_self hb0]
    have h2 : u.intValuation (a - b) ≤ WithZero.exp (-(e : ℤ)) * u.intValuation b := by
      have h3 : a - b ∈ u.asIdeal ^ (e + j) := by
        have := (u.asIdeal ^ (e + j)).neg_mem hβN
        rwa [neg_sub] at this
      calc u.intValuation (a - b) ≤ WithZero.exp (-((e + j : ℕ) : ℤ)) :=
            (intValuation_le_pow_iff_mem u (a - b) (e + j)).mpr h3
        _ = WithZero.exp (-(e : ℤ)) * WithZero.exp (-(j : ℤ)) := by
            rw [← WithZero.exp_add]
            congr 1
            push_cast
            ring
        _ ≤ WithZero.exp (-(e : ℤ)) * u.intValuation b :=
            mul_le_mul_right (exp_neg_le_intValuation_of_notMem u hb0' hbj) _
    rw [h1, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap]
    exact (div_le_iff₀ (zero_lt_iff.mpr (intValuation_ne_zero u b hb0'))).mpr h2
  have hγ : artinMap K L G (toPrincipalIdeal (𝓞 K) K (Units.mk0 _ ha0 / Units.mk0 _ hb0)) = 1 :=
    MonoidHom.mem_ker.mp (hrec (Subgroup.mem_map_of_mem _
      (mem_rayGroup_mul_pow hI Set.univ u hu he hIe hγI hval)))
  -- the Artin symbol of `(b)`: `(b)` is the norm of `(β)`, and `β` lies in the ray modulo `(m) ∞`
  have hbart : artinMap K L G (toPrincipalIdeal (𝓞 K) K (Units.mk0 _ hb0)) = 1 := by
    have hspanE : Ideal.span {algebraMap (𝓞 K) (𝓞 (decompositionField K M Γ u))
        (μ * (m : 𝓞 K))} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K)
        (𝓞 (decompositionField K M Γ u)))).mpr fun h => hμm0 (by rw [h, map_zero])
    have hspanK : Ideal.span {μ * (m : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact fun h => hμm0 (by rw [h, map_zero])
    -- the primes of `(β)` lie above primes unramified in `M`
    have hβprime : ∀ w : HeightOneSpectrum (𝓞 (decompositionField K M Γ u)),
        count (decompositionField K M Γ u) w ((toPrincipalIdeal
          (𝓞 (decompositionField K M Γ u)) (decompositionField K M Γ u) (Units.mk0 _ hβE) :
          (FractionalIdeal (𝓞 (decompositionField K M Γ u))⁰
            (decompositionField K M Γ u))ˣ) :
          FractionalIdeal (𝓞 (decompositionField K M Γ u))⁰ (decompositionField K M Γ u)) ≠
          0 → IsUnramifiedPrime K M Γ (w.under (𝓞 K)) := fun w hw => by
      refine (hunr _ fun hmem => hw ?_).2
      refine rayPrincipal_le (⟨_, hspanE, Set.univ⟩ : Modulus (decompositionField K M Γ u))
        (Subgroup.mem_map_of_mem _ (mk0_mem_rayGroup _ hβE hβ1 fun w' => hβpos w'.1.1 w'.1.2))
        w (Ideal.dvd_span_singleton.mpr hmem)
    -- the primes of `(b)` are unramified in `L` and in `M`
    have hbprime : ∀ v : HeightOneSpectrum (𝓞 K),
        count K v ((toPrincipalIdeal (𝓞 K) K (Units.mk0 _ hb0) :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 →
        IsUnramifiedPrime K L G v ∧ IsUnramifiedPrime K M Γ v := fun v hv => by
      refine hunr v fun hmem => hv ?_
      exact rayPrincipal_le (⟨_, hspanK, Set.univ⟩ : Modulus K)
        (Subgroup.mem_map_of_mem _ (mk0_mem_rayGroup _ hb0 hb1 fun w' => hbpos w'.1.1 w'.1.2))
        v (Ideal.dvd_span_singleton.mpr hmem)
    -- `β` lies in the ray modulo `(m) ∞` of the decomposition field
    have hβray : Units.mk0 _ hβE ∈ rayGroup (normModulus (decompositionField K M Γ u) m) := by
      refine mk0_mem_rayGroup _ hβE ?_ fun w' => hβpos w'.1.1 w'.1.2
      refine (Ideal.span_singleton_le_iff_mem _).mpr ?_ hβ1
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hnormu : Units.map (Algebra.norm K : decompositionField K M Γ u →* K)
        (Units.mk0 _ hβE) = Units.mk0 _ hb0 := Units.ext hnorm
    have h1 := map_artinMap_eq_artinMap_idealNormHom K (decompositionField K M Γ u) M
      (Subgroup.zpowers (frobeniusElement K M Γ u)).subtype (fun _ _ => rfl)
      (toPrincipalIdeal (𝓞 (decompositionField K M Γ u)) (decompositionField K M Γ u)
        (Units.mk0 _ hβE)) hβprime
    rw [MonoidHom.mem_ker.mp (rayPrincipal_normModulus_le_ker_artinMap
      (decompositionField K M Γ u) M hζ hκ m (dvd_refl m)
      (Subgroup.mem_map_of_mem _ hβray)), map_one, idealNormHom_toPrincipalIdeal, hnormu] at h1
    have h2 := restrictHom_artinMap K L M (G := G) (Γ := Γ) hbprime
    rw [← h1, map_one] at h2
    exact h2.symm
  have hab : Units.mk0 _ ha0 = Units.mk0 _ ha0 / Units.mk0 _ hb0 * Units.mk0 _ hb0 :=
    (div_mul_cancel _ _).symm
  rw [hab, map_mul, map_mul, hγ, hbart, mul_one]

/-- **Removing an unramified prime from the modulus.** Let the primes `v ∤ I` be unramified in
`L`, `u ∤ I` a prime and `e ≥ 1`. If the Artin map is trivial on the ray modulo `I u^e ∞`, it
is trivial on the ray modulo `I ∞`. -/
theorem rayPrincipal_le_ker_artinMap_of_mul_pow {I : Ideal (𝓞 K)}
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ I → IsUnramifiedPrime K L G v)
    (hI : I ≠ ⊥) (u : HeightOneSpectrum (𝓞 K)) (hu : ¬ u.asIdeal ∣ I) {e : ℕ} (he : e ≠ 0)
    (hIe : I * u.asIdeal ^ e ≠ ⊥)
    (hrec : rayPrincipal (⟨I * u.asIdeal ^ e, hIe, Set.univ⟩ : Modulus K) ≤
      (artinMap K L G).ker) :
    rayPrincipal (⟨I, hI, Set.univ⟩ : Modulus K) ≤ (artinMap K L G).ker := by
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨a₁, a₂, h₁0, h₂0, h₁, h₂, hp₁, hp₂, hfrac⟩ :=
    exists_integral_of_mem_rayGroup (⟨I, hI, Set.univ⟩ : Modulus K) hα
  have hα' : α = Units.mk0 _ h₁0 / Units.mk0 _ h₂0 := by
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0, mul_comm]
      exact hfrac)
  rw [MonoidHom.mem_ker, hα', map_div, map_div,
    artinMap_toPrincipalIdeal_eq_one_of_mul_pow K L G hram hI u hu he hIe hrec h₁0 h₁
      fun w hw => hp₁ ⟨⟨w, hw⟩, Set.mem_univ _⟩,
    artinMap_toPrincipalIdeal_eq_one_of_mul_pow K L G hram hI u hu he hIe hrec h₂0 h₂
      fun w hw => hp₂ ⟨⟨w, hw⟩, Set.mem_univ _⟩, _root_.div_one]

/-- The unramified primes of the modulus can be removed, for moduli whose unramified primes lie
in a given finite set. -/
theorem exists_ideal_rayPrincipal_le_ker_artinMap_of_subset
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥),
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ J → IsUnramifiedPrime K L G v) →
      rayPrincipal (⟨J, hJ, Set.univ⟩ : Modulus K) ≤ (artinMap K L G).ker →
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ J → IsUnramifiedPrime K L G v → v ∈ S) →
      ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
        (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I ↔ ¬ IsUnramifiedPrime K L G v) ∧
        rayPrincipal (⟨I, hI, Set.univ⟩ : Modulus K) ≤ (artinMap K L G).ker := by
  induction S using Finset.induction_on with
  | empty =>
    intro J hJ hram hrec hS
    exact ⟨J, hJ, fun v => ⟨fun hv hunr => absurd (hS v hv hunr) (Finset.notMem_empty v),
      fun hv => not_not.mp fun hdvd => hv (hram v hdvd)⟩, hrec⟩
  | insert u S hu ih =>
    intro J hJ hram hrec hS
    by_cases hcase : u.asIdeal ∣ J ∧ IsUnramifiedPrime K L G u
    · -- `J = u^e Q` with `u ∤ Q`
      haveI := u.isMaximal
      obtain ⟨Q, hcop, hJQ⟩ := Ideal.eq_prime_pow_mul_coprime hJ u.asIdeal
      generalize Multiset.count u.asIdeal (UniqueFactorizationMonoid.normalizedFactors J) = e
        at hJQ
      have huQ : ¬ u.asIdeal ∣ Q := fun h => u.isPrime.ne_top (by
        rw [← hcop]
        exact (sup_eq_left.mpr (Ideal.dvd_iff_le.mp h)).symm)
      have he : e ≠ 0 := fun h0 => huQ (by
          rw [h0, pow_zero, one_mul] at hJQ
          exact hJQ ▸ hcase.1)
      rw [mul_comm] at hJQ
      subst hJQ
      have hQ : Q ≠ ⊥ := fun h => hJ (by rw [h, Ideal.bot_mul])
      have hramQ : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ Q →
          IsUnramifiedPrime K L G v := fun v hv => by
        by_cases hvu : v = u
        · exact hvu ▸ hcase.2
        · refine hram v fun hdvd => ?_
          rcases v.prime.dvd_or_dvd hdvd with h | h
          · exact hv h
          · exact hvu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top
              (Ideal.dvd_iff_le.mp (v.prime.dvd_of_dvd_pow h))).symm)
      refine ih Q hQ hramQ
        (rayPrincipal_le_ker_artinMap_of_mul_pow K L G hramQ hQ u huQ he hJ hrec)
        fun v hv hunr => ?_
      rcases Finset.mem_insert.mp (hS v (Dvd.dvd.mul_right hv _) hunr) with h | h
      · exact absurd (h ▸ hv) huQ
      · exact h
    · refine ih J hJ hram hrec fun v hv hunr => ?_
      rcases Finset.mem_insert.mp (hS v hv hunr) with h | h
      · exact absurd ⟨h ▸ hv, h ▸ hunr⟩ hcase
      · exact h

/-- **The reciprocity law with a modulus supported on the ramified primes.** For an abelian
extension `L/K` of number fields there is an ideal `I ≠ 0` of `𝓞_K`, whose prime divisors are
the primes ramified in `L`, such that the Artin map is trivial on the principal ideals of the
ray modulo `I ∞`. -/
theorem exists_ideal_rayPrincipal_le_ker_artinMap :
    ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I ↔ ¬ IsUnramifiedPrime K L G v) ∧
      rayPrincipal (⟨I, hI, Set.univ⟩ : Modulus K) ≤ (artinMap K L G).ker := by
  obtain ⟨c, hc, hram, hrec⟩ := exists_rayPrincipal_le_ker_artinMap K L G
  refine exists_ideal_rayPrincipal_le_ker_artinMap_of_subset K L G
    (finite_primes_dvd (normModulus K c)).toFinset (normModulus K c).fin
    (normModulus K c).fin_ne_bot
    (fun v hv => hram v fun h => hv ((dvd_normModulus_fin_iff K c v).mpr h)) hrec
    fun v hv _ => (Set.Finite.mem_toFinset _).mpr hv

end GaloisForLFunctions
