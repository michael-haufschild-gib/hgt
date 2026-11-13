import GaloisForLFunctions.RHTower.Artin.FrobeniusElementsRestrictToASubextension
import GaloisForLFunctions.RHTower.Artin.TheCrossingOfAGaloisExtensionWithACyclotomicExtension
import GaloisForLFunctions.RHTower.Artin.ModuliWithIndependentResidueClasses
import GaloisForLFunctions.RHTower.Artin.CyclotomicPolynomialsAreIrreducibleOverANumberFieldAwayFromAFixedModulus

/-!
# Ideals with trivial Artin symbol in a cyclic extension are norms modulo a ray

Let `L/K` be a cyclic extension of number fields with group `G = ⟨σ⟩` of order `n`, and `c ≥ 1`
such that the primes `v ∤ c` of `K` are unramified in `L`.

**Theorem** (`mem_rayPrincipal_sup_range_idealNormHom_of_artinMap_eq_one`). An ideal `𝔞` of `K`
prime to `c` with Artin symbol `(𝔞, L/K) = 1` is the product of a principal ideal of the ray
modulo `(c) ∞` and of the norm of an ideal of `L`.

Proof (crossing with a cyclotomic extension). Let `a_v = N v` and `(v, L/K) = σ^{d_v}` for the
primes `v` of `𝔞`. Choose `m` prime to `c`, to the `a_v` and to the modulus outside of which
cyclotomic polynomials are irreducible over `L`, and a class `b` modulo `m`, such that
`a_v^x b^y ≡ 1 (m)` forces `n | x, y`. In `M = L(ζ_m)`, abelian over `K` with group
`Γ = G × (ℤ/m)ˣ`, put `ρ = (σ, b)` and `Λ = Gal(M/L)`, and take an ideal `𝔟` in the norm group
`D_{⟨ρ⟩}` with `(𝔟, M/K) = ρ`. Then `v 𝔟^{-d_v} ∈ P_{(cm)∞} · D_Λ` for every prime `v` of `𝔞`,
`D_Λ` consists of norms from `L`, and `Π_v 𝔟^{d_v v(𝔞)} = 𝔟^e` with `σ^e = (𝔞, L/K) = 1`, so
`n | e` and `𝔟^e ∈ D_Λ`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions ArtinMertens

/-- The homomorphism with the values `x^{d(v)}` on the primes is `I ↦ x^{e(I)}`, with
`e(I) = Σ_v v(I) d(v)`. -/
theorem primeValuesHom_zpow {K : Type*} [Field K] [NumberField K] {A : Type*} [CommGroup A]
    (x : A) (d : HeightOneSpectrum (𝓞 K) → ℤ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    primeValuesHom (fun v => x ^ d v) I =
      x ^ Multiplicative.toAdd (primeValuesHom (fun v => Multiplicative.ofAdd (d v)) I) := by
  have h := congrArg (fun f : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* A => f I)
    (comp_primeValuesHom (zpowersHom A x) fun v => Multiplicative.ofAdd (d v))
  simpa only [MonoidHom.comp_apply, zpowersHom_apply, toAdd_ofAdd] using h.symm

/-- The norms of the primes of a fractional ideal form a finite set of integers `≥ 2`. -/
theorem exists_finset_absNorm_of_count_ne_zero {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ A : Finset ℕ, (∀ a ∈ A, 2 ≤ a) ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 → Ideal.absNorm v.asIdeal ∈ A := by
  have hfin : {v : HeightOneSpectrum (𝓞 K) |
      ¬ count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 K)⁰ K))
  refine ⟨hfin.toFinset.image fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal, ?_, ?_⟩
  · intro a ha
    obtain ⟨v, -, hva⟩ := Finset.mem_image.mp ha
    rw [← hva]
    exact two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  · intro v hv
    exact Finset.mem_image.mpr ⟨v, (hfin.mem_toFinset).mpr hv, rfl⟩

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **Ideals with trivial Artin symbol in a cyclic extension are norms modulo a ray.** Let
`L/K` be cyclic, unramified outside `c`. An ideal `𝔞` prime to `c` with `(𝔞, L/K) = 1` is the
product of a principal ideal of the ray modulo `(c) ∞` and of the norm of an ideal of `L`. -/
theorem mem_rayPrincipal_sup_range_idealNormHom_of_artinMap_eq_one {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (c : ℕ) [NeZero c]
    (hc : ∀ v : HeightOneSpectrum (𝓞 K), (c : 𝓞 K) ∉ v.asIdeal → IsUnramifiedPrime K L G v)
    {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (h𝔞 : 𝔞 ∈ idealGroup (normModulus K c))
    (hart : artinMap K L G 𝔞 = 1) :
    𝔞 ∈ rayPrincipal (normModulus K c) ⊔ (idealNormHom K L).range := by
  -- the modulus `m` and the class `b`
  obtain ⟨A, hA2, hAmem⟩ := exists_finset_absNorm_of_count_ne_zero 𝔞
  obtain ⟨m₀, hm₀, hirr⟩ := exists_forall_coprime_irreducible_cyclotomic L
  have ht : m₀ * c * ∏ a ∈ A, a ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero hm₀ (NeZero.ne c))
      (Finset.prod_ne_zero_iff.mpr fun a ha => Nat.ne_of_gt (lt_of_lt_of_le two_pos (hA2 a ha)))
  obtain ⟨m, b, hm, hmt, harith⟩ :=
    exists_modulus_unit_forall_zpow_mul_zpow (n := Fintype.card G) Fintype.card_ne_zero A hA2 ht
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero (c * m) := ⟨Nat.mul_ne_zero (NeZero.ne c) hm⟩
  have hmm₀ : m.Coprime m₀ :=
    Nat.Coprime.coprime_dvd_right ((dvd_mul_right m₀ c).mul_right _) hmt
  have hmA : ∀ a ∈ A, m.Coprime a := fun a ha =>
    Nat.Coprime.coprime_dvd_right ((Finset.dvd_prod_of_mem _ ha).mul_left _) hmt
  -- the crossing `M = L(ζ_m)` and `ρ = (σ, b)`
  obtain ⟨M, _, _, _, _, _, Γ, _, _, _, _, ζ, hζ, hbij⟩ :=
    exists_cyclotomic_crossing K L (G := G) (hirr m hm hmm₀)
  obtain ⟨ρ, hρ⟩ := hbij.2 (σ, b)
  obtain ⟨hρσ, hρb⟩ := Prod.mk.inj hρ
  have hur : ∀ v : HeightOneSpectrum (𝓞 K), ((c * m : ℕ) : 𝓞 K) ∉ v.asIdeal →
      IsUnramifiedPrime K M Γ v := fun v hv =>
    isUnramifiedPrime_of_injective_restrictHom_cyclotomicCharacter K L M hζ hbij.1
      (hc v (natCast_notMem_of_dvd K (c * m) (dvd_mul_right c m) hv))
      (natCast_notMem_of_dvd K (c * m) (dvd_mul_left m c) hv)
  obtain ⟨𝔟, h𝔟, h𝔟ρ⟩ := exists_mem_frobeniusPowerGroup_artinMap_eq K M (c * m) hur
    (Subgroup.zpowers ρ) (Subgroup.mem_zpowers ρ)
  -- the exponents `d_v`
  choose d hd using fun v : HeightOneSpectrum (𝓞 K) =>
    Subgroup.mem_zpowers_iff.mp (hσ (frobeniusOrOne K L G v))
  -- every prime `v` of `𝔞` is `𝔟^{d_v}` modulo `P_{(cm)∞} · D_Λ`
  have hstep : ∀ v : HeightOneSpectrum (𝓞 K),
      count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 →
      idealUnit v.ne_bot / 𝔟 ^ d v ∈ rayPrincipal (normModulus K (c * m)) ⊔
        frobeniusPowerGroup K M (c * m) (IsGaloisGroup.restrictHom Γ G K L M).ker := by
    intro v hv
    have hvc : (c : 𝓞 K) ∉ v.asIdeal := fun h =>
      hv (h𝔞 v ((dvd_normModulus_fin_iff K c v).mpr h))
    have hvm : (m : 𝓞 K) ∉ v.asIdeal :=
      natCast_notMem_of_absNorm_coprime v (hmA _ (hAmem v hv)).symm
    have hvN : ((c * m : ℕ) : 𝓞 K) ∉ v.asIdeal := by
      rw [Nat.cast_mul]
      exact fun h => (v.isPrime.mem_or_mem h).elim hvc hvm
    refine idealUnit_div_zpow_mem_rayPrincipal_sup_frobeniusPowerGroup K L M (c * m) hζ hbij.1
      (dvd_mul_left m c) hur h𝔟 h𝔟ρ hvN (hc v hvc) ?_ ?_
    · intro x y hxy
      rw [hρb] at hxy
      exact harith _ (hAmem v hv) _ (coe_cyclotomicCharacter_frobeniusElement K M hζ v hvm)
        x y hxy
    · rw [hρσ, hd, frobeniusOrOne, if_pos (hc v hvc)]
  -- `𝔞 / δ(𝔞)` with `δ(v) = 𝔟^{d_v}`
  have h1 : 𝔞 / primeValuesHom (fun v => 𝔟 ^ d v) 𝔞 ∈
      rayPrincipal (normModulus K (c * m)) ⊔
        frobeniusPowerGroup K M (c * m) (IsGaloisGroup.restrictHom Γ G K L M).ker := by
    have hf := eq_primeValuesHom
      (MonoidHom.id (FractionalIdeal (𝓞 K)⁰ K)ˣ / primeValuesHom fun v => 𝔟 ^ d v)
    simp only [MonoidHom.div_apply, MonoidHom.id_apply, primeValuesHom_idealUnit_prime] at hf
    have h := primeValuesHom_mem _ 𝔞 hstep
    rwa [← hf, MonoidHom.div_apply, MonoidHom.id_apply] at h
  -- `δ(𝔞) = 𝔟^e` with `σ^e = (𝔞, L/K) = 1`
  have hσe : σ ^ Multiplicative.toAdd
      (primeValuesHom (fun v => Multiplicative.ofAdd (d v)) 𝔞) = 1 := by
    rw [← primeValuesHom_zpow σ d 𝔞, primeValuesHom_congr 𝔞 fun v _ => hd v]
    exact hart
  have hdvd : (Fintype.card G : ℤ) ∣ Multiplicative.toAdd
      (primeValuesHom (fun v => Multiplicative.ofAdd (d v)) 𝔞) := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hσe
    rwa [orderOf_eq_card_of_forall_mem_zpowers hσ, Nat.card_eq_fintype_card] at h
  have h2 : primeValuesHom (fun v => 𝔟 ^ d v) 𝔞 ∈
      frobeniusPowerGroup K M (c * m) (IsGaloisGroup.restrictHom Γ G K L M).ker := by
    obtain ⟨j, hj⟩ := hdvd
    rw [primeValuesHom_zpow 𝔟 d 𝔞, hj, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ (pow_card_mem_frobeniusPowerGroup_ker_restrictHom K L M (G := G)
      (c * m) (Subgroup.zpowers ρ) h𝔟) j
  have h3 : 𝔞 ∈ rayPrincipal (normModulus K (c * m)) ⊔
      frobeniusPowerGroup K M (c * m) (IsGaloisGroup.restrictHom Γ G K L M).ker := by
    have h := Subgroup.mul_mem _ h1 (Subgroup.mem_sup_right h2)
    rwa [div_mul_cancel] at h
  exact sup_le_sup (rayPrincipal_normModulus_le_of_dvd K (dvd_mul_right c m))
    (frobeniusPowerGroup_ker_restrictHom_le_range_idealNormHom K L M (G := G) (c * m)) h3

end GaloisForLFunctions
