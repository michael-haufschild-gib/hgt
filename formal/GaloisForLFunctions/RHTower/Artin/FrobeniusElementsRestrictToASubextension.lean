import GaloisForLFunctions.RHTower.Artin.TheNormGroupOfTheFixedFieldOfASubgroupAndItsArtinSymbols

/-!
# Frobenius elements restrict to a subextension

Let `K ⊂ L ⊂ M` be number fields, `M/K` and `L/K` abelian with groups `Γ` and `G`, and
`r : Γ → G` the restriction of automorphisms.

* `r` maps the inertia group of a prime `Q` of `M` into that of `Q ∩ L`
  (`restrictHom_mem_inertia`), and the Frobenius element in `M/K` of a prime `v` of `K`
  unramified in `L` to its Frobenius element in `L/K` (`restrictHom_frobeniusElement`).
* Let `ζ ∈ M` be a primitive `m`-th root of unity with cyclotomic character `κ`, and assume that
  `γ ↦ (r γ, κ(γ))` is injective (as for `M = L(ζ)`). A prime `v ∤ m` unramified in `L` is
  unramified in `M` (`isUnramifiedPrime_of_injective_restrictHom_cyclotomicCharacter`).
* With `D_H = ⟨v^g : v ∤ N, Frob_v^g ∈ H⟩` for `H ≤ Γ` and `Λ = ker r`: the elements of `D_Λ`
  are norms from `L` (`frobeniusPowerGroup_ker_restrictHom_le_range_idealNormHom`), and
  `D_H^{[L:K]} ⊂ D_Λ` (`pow_card_mem_frobeniusPowerGroup_ker_restrictHom`).

**The crossing step** (`idealUnit_div_zpow_mem_rayPrincipal_sup_frobeniusPowerGroup`). Let
`m | N`, the primes `v ∤ N` unramified in `M`, `ρ ∈ Γ` and `𝔟 ∈ D_{⟨ρ⟩}` with `(𝔟, M/K) = ρ`.
Let `v ∤ N` be a prime such that `κ(Frob_v)^x κ(ρ)^y = 1` forces `[L:K] | x, y`, and
`r(ρ)^d = Frob_v(L/K)`. Then `v 𝔟^{-d} ∈ P_{(N)∞} · D_Λ`: the cyclotomic character is injective
on `H = ⟨Frob_v, ρ⟩`, and `v 𝔟^{-d} ∈ D_H` has Artin symbol in `Λ`.

Also: the ray modulo `(N) ∞` lies in the ray modulo `(c) ∞` for `c | N`
(`rayPrincipal_normModulus_le_of_dvd`), and a prime whose norm is prime to `m` does not divide
`m` (`natCast_notMem_of_absNorm_coprime`).
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-! ### Rays and norms of primes -/

/-- A prime whose norm is prime to `m` does not contain `m`. -/
theorem natCast_notMem_of_absNorm_coprime {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (v : HeightOneSpectrum (𝓞 K)) (h : (Ideal.absNorm v.asIdeal).Coprime m) :
    (m : 𝓞 K) ∉ v.asIdeal := fun hm => by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr h
  have h1 : ((x * (Ideal.absNorm v.asIdeal : ℤ) + y * (m : ℤ) : ℤ) : 𝓞 K) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ (Ideal.absNorm_mem _))
      (v.asIdeal.mul_mem_left _ hm)
  rw [hxy, Int.cast_one] at h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The ray group modulo `(N) ∞` lies in the ray group modulo `(c) ∞` for `c | N`. -/
theorem rayGroup_normModulus_le_of_dvd (K : Type*) [Field K] [NumberField K] {c N : ℕ}
    [NeZero c] [NeZero N] (h : c ∣ N) :
    rayGroup (normModulus K N) ≤ rayGroup (normModulus K c) := by
  rintro _ ⟨β, hβ, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one] at hβ
  obtain ⟨hred, hsign⟩ := hβ
  have hcN : (c : 𝓞 K) ∣ (N : 𝓞 K) := Nat.cast_dvd_cast h
  -- the primes dividing `c` divide `N`
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (normModulus K c).fin →
      v.asIdeal ∣ (normModulus K N).fin := fun v hv => by
    rw [dvd_normModulus_fin_iff] at hv ⊢
    obtain ⟨k, hk⟩ := hcN
    rw [hk]
    exact Ideal.mul_mem_right _ _ hv
  have hγ : (β : Kˣ) ∈ primeToUnits (normModulus K c) := fun v hv => β.2 v (hdvd v hv)
  refine ⟨⟨_, hγ⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one]
  constructor
  · -- the residue: `β = a/b` with `a ≡ b mod N`, hence modulo `c`
    obtain ⟨a, b, -, hab, hfrac⟩ := exists_unit_fraction (normModulus K N) β.2
    have ha := fun v hv => (hab v hv).1
    have hb := fun v hv => (hab v hv).2
    have hredN := reduce_eq (normModulus K N) β ha hb hfrac
    rw [hred, eq_comm, mul_inv_eq_one] at hredN
    have hmk : a - b ∈ Ideal.span {(N : 𝓞 K)} :=
      Ideal.Quotient.eq.mp (congrArg Units.val hredN)
    have hmk' : a - b ∈ Ideal.span {(c : 𝓞 K)} :=
      Ideal.span_singleton_le_span_singleton.mpr hcN hmk
    rw [reduce_eq (normModulus K c) ⟨_, hγ⟩ (fun v hv => ha v (hdvd v hv))
      (fun v hv => hb v (hdvd v hv)) hfrac, mul_inv_eq_one]
    exact Units.ext (Ideal.Quotient.eq.mpr hmk')
  · -- the signs
    funext w
    have hw := congrFun hsign ⟨w.1, Set.mem_univ _⟩
    rw [MonoidHom.comp_apply, signAtInf_apply] at hw ⊢
    exact hw

/-- The principal ray ideals modulo `(N) ∞` are principal ray ideals modulo `(c) ∞` for
`c | N`. -/
theorem rayPrincipal_normModulus_le_of_dvd (K : Type*) [Field K] [NumberField K] {c N : ℕ}
    [NeZero c] [NeZero N] (h : c ∣ N) :
    rayPrincipal (normModulus K N) ≤ rayPrincipal (normModulus K c) :=
  Subgroup.map_mono (rayGroup_normModulus_le_of_dvd K h)

variable (K L M : Type u) {G Γ : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [CommGroup Γ] [Fintype Γ] [MulSemiringAction Γ M] [IsGaloisGroup Γ K M]

/-! ### Inertia groups and Frobenius elements -/

/-- The restriction acts on the integers of `L` as the automorphism of `M`. -/
private theorem algebraMap_restrictHom_smul_int (γ : Γ) (y : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 M) (IsGaloisGroup.restrictHom Γ G K L M γ • y) =
      γ • algebraMap (𝓞 L) (𝓞 M) y :=
  RingOfIntegers.ext (IsGaloisGroup.algebraMap_restrictHom_smul Γ G K L M γ (y : L))

/-- **The restriction maps the inertia group of `Q` into the inertia group of `Q ∩ L`.** -/
theorem restrictHom_mem_inertia {Q : Ideal (𝓞 M)} {τ : Γ} (hτ : τ ∈ Q.inertia Γ) :
    IsGaloisGroup.restrictHom Γ G K L M τ ∈ (Q.under (𝓞 L)).inertia G := by
  intro y
  show algebraMap (𝓞 L) (𝓞 M) (IsGaloisGroup.restrictHom Γ G K L M τ • y - y) ∈ Q
  rw [map_sub, algebraMap_restrictHom_smul_int]
  exact hτ _

/-- **The Frobenius element restricts to the Frobenius element**: for a prime `v` of `K`
unramified in `L`, the restriction of `Frob_v(M/K)` is `Frob_v(L/K)`. -/
theorem restrictHom_frobeniusElement {v : HeightOneSpectrum (𝓞 K)}
    (hL : IsUnramifiedPrime K L G v) :
    IsGaloisGroup.restrictHom Γ G K L M (frobeniusElement K M Γ v) =
      frobeniusElement K L G v := by
  haveI : ((primeAbove K M v).under (𝓞 L)).LiesOver v.asIdeal :=
    Ideal.under_liesOver_of_liesOver (𝓞 L) (primeAbove K M v) v.asIdeal
  haveI : ((primeAbove K M v).under (𝓞 L)).IsMaximal := inferInstance
  have hΓ := IsArithFrobAt.arithFrobAt (𝓞 K) Γ (primeAbove K M v)
  have hG := IsArithFrobAt.arithFrobAt (𝓞 K) G ((primeAbove K M v).under (𝓞 L))
  have hunder : ((primeAbove K M v).under (𝓞 L)).under (𝓞 K) =
      (primeAbove K M v).under (𝓞 K) := Ideal.under_under _
  -- both act on the residue ring of `Q ∩ L` as `x ↦ x^{N(v)}`
  have key : ∀ c : 𝓞 L, Ideal.Quotient.mk ((primeAbove K M v).under (𝓞 L))
      (IsGaloisGroup.restrictHom Γ G K L M (frobeniusElement K M Γ v) • c) =
        Ideal.Quotient.mk ((primeAbove K M v).under (𝓞 L))
          (arithFrobAt (𝓞 K) G ((primeAbove K M v).under (𝓞 L)) • c) := by
    intro c
    rw [mk_smul_eq_pow hG, hunder, ← map_pow]
    refine Ideal.Quotient.eq.mpr ?_
    show algebraMap (𝓞 L) (𝓞 M) (_ - _) ∈ primeAbove K M v
    rw [map_sub, map_pow, algebraMap_restrictHom_smul_int]
    exact hΓ _
  have hmem : IsGaloisGroup.restrictHom Γ G K L M (frobeniusElement K M Γ v) *
      (arithFrobAt (𝓞 K) G ((primeAbove K M v).under (𝓞 L)))⁻¹ ∈
        ((primeAbove K M v).under (𝓞 L)).inertia G := fun c => by
    refine Ideal.Quotient.eq.mp ?_
    rw [mul_smul, key, smul_inv_smul]
  rw [hL _ inferInstance inferInstance, Subgroup.mem_bot] at hmem
  rw [← arithFrobAt_eq_frobeniusElement hL ((primeAbove K M v).under (𝓞 L))]
  exact mul_inv_eq_one.mp hmem

/-- **Ramification in the crossing.** If the restriction to `L` together with the cyclotomic
character of a primitive `m`-th root of unity is injective on `Γ`, a prime `v ∤ m` unramified
in `L` is unramified in `M`. -/
theorem isUnramifiedPrime_of_injective_restrictHom_cyclotomicCharacter {m : ℕ} [NeZero m]
    {ζ : 𝓞 M} (hζ : IsPrimitiveRoot ζ m)
    (hinj : Function.Injective fun γ : Γ =>
      (IsGaloisGroup.restrictHom Γ G K L M γ, cyclotomicCharacter hζ γ))
    {v : HeightOneSpectrum (𝓞 K)} (hL : IsUnramifiedPrime K L G v)
    (hm : (m : 𝓞 K) ∉ v.asIdeal) : IsUnramifiedPrime K M Γ v := by
  intro Q hQ hQv
  haveI := hQ
  haveI := hQv
  haveI : (Q.under (𝓞 L)).LiesOver v.asIdeal :=
    Ideal.under_liesOver_of_liesOver (𝓞 L) Q v.asIdeal
  haveI : (Q.under (𝓞 L)).IsMaximal := inferInstance
  have hQm : (m : 𝓞 M) ∉ Q := fun h => hm (by
    rw [hQv.over, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h)
  refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => hinj ?_
  have h1 : IsGaloisGroup.restrictHom Γ G K L M τ = 1 := by
    have h := restrictHom_mem_inertia K L M (G := G) hτ
    rwa [hL _ inferInstance inferInstance, Subgroup.mem_bot] at h
  show (IsGaloisGroup.restrictHom Γ G K L M τ, cyclotomicCharacter hζ τ) =
    (IsGaloisGroup.restrictHom Γ G K L M 1, cyclotomicCharacter hζ 1)
  rw [h1, cyclotomicCharacter_eq_one_of_mem_inertia hζ hQm hτ, map_one, map_one]

/-! ### The norm group of the kernel of the restriction -/

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- **The elements of `D_Λ`, `Λ` the kernel of the restriction, are norms from `L`**: if
`Frob_v^g` fixes `L` then `v^g` is the norm of a power of a prime of `L` above `v`. -/
theorem frobeniusPowerGroup_ker_restrictHom_le_range_idealNormHom :
    frobeniusPowerGroup K M N (IsGaloisGroup.restrictHom Γ G K L M).ker ≤
      (idealNormHom K L).range := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨v, g, -, hg, rfl⟩
  obtain ⟨w, k, -, hnorm⟩ := exists_idealNormHom_pow_eq_idealUnit_pow K L M v (g := g)
    fun x => by
      rw [← IsGaloisGroup.algebraMap_restrictHom_smul Γ G K L M, MonoidHom.mem_ker.mp hg,
        one_smul]
  exact ⟨_, hnorm⟩

omit [NeZero N] in
/-- **The `[L:K]`-th powers of the elements of `D_H` lie in `D_Λ`**, `Λ` the kernel of the
restriction: the `[L:K]`-th power of every element of `Γ` fixes `L`. -/
theorem pow_card_mem_frobeniusPowerGroup_ker_restrictHom (H : Subgroup Γ)
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hI : I ∈ frobeniusPowerGroup K M N H) :
    I ^ Fintype.card G ∈
      frobeniusPowerGroup K M N (IsGaloisGroup.restrictHom Γ G K L M).ker := by
  have hle : frobeniusPowerGroup K M N H ≤
      (frobeniusPowerGroup K M N (IsGaloisGroup.restrictHom Γ G K L M).ker).comap
        (powMonoidHom (Fintype.card G)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨v, g, hv, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, powMonoidHom_apply, ← pow_mul]
    refine Subgroup.subset_closure ⟨v, g * Fintype.card G, hv, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_pow, pow_mul, pow_card_eq_one]
  exact hle hI

/-! ### The crossing step -/

/-- **The crossing step.** Let `m | N`, the primes `v ∤ N` unramified in `M`, `ρ ∈ Γ` and
`𝔟 ∈ D_{⟨ρ⟩}` with Artin symbol `ρ`. For a prime `v ∤ N` unramified in `L` such that
`κ(Frob_v)^x κ(ρ)^y = 1` forces `[L:K] | x, y`, and `d` with `r(ρ)^d = Frob_v(L/K)`:
`v 𝔟^{-d}` is the product of a principal ideal of the ray modulo `(N) ∞` and of an element of
`D_Λ`, `Λ = ker r`. -/
theorem idealUnit_div_zpow_mem_rayPrincipal_sup_frobeniusPowerGroup {m : ℕ} [NeZero m]
    {ζ : 𝓞 M} (hζ : IsPrimitiveRoot ζ m)
    (hinj : Function.Injective fun γ : Γ =>
      (IsGaloisGroup.restrictHom Γ G K L M γ, cyclotomicCharacter hζ γ))
    (hmN : m ∣ N)
    (hur : ∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∉ v.asIdeal → IsUnramifiedPrime K M Γ v)
    {ρ : Γ} {𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h𝔟 : 𝔟 ∈ frobeniusPowerGroup K M N (Subgroup.zpowers ρ)) (h𝔟ρ : artinMap K M Γ 𝔟 = ρ)
    {v : HeightOneSpectrum (𝓞 K)} (hv : (N : 𝓞 K) ∉ v.asIdeal)
    (hL : IsUnramifiedPrime K L G v)
    (harith : ∀ x y : ℤ, cyclotomicCharacter hζ (frobeniusElement K M Γ v) ^ x *
      cyclotomicCharacter hζ ρ ^ y = 1 → (Fintype.card G : ℤ) ∣ x ∧ (Fintype.card G : ℤ) ∣ y)
    {d : ℤ} (hd : IsGaloisGroup.restrictHom Γ G K L M ρ ^ d = frobeniusElement K L G v) :
    idealUnit v.ne_bot / 𝔟 ^ d ∈ rayPrincipal (normModulus K N) ⊔
      frobeniusPowerGroup K M N (IsGaloisGroup.restrictHom Γ G K L M).ker := by
  -- the cyclotomic character is injective on `H = ⟨Frob_v, ρ⟩`
  have hH : ∀ h ∈ Subgroup.closure ({frobeniusElement K M Γ v, ρ} : Set Γ),
      cyclotomicCharacter hζ h = 1 → h = 1 := by
    intro h hh hκ
    obtain ⟨x, y, rfl⟩ := Subgroup.mem_closure_pair.mp hh
    rw [map_mul, map_zpow, map_zpow] at hκ
    obtain ⟨⟨jx, rfl⟩, ⟨jy, rfl⟩⟩ := harith x y hκ
    refine hinj (Prod.ext ?_ ?_)
    · show IsGaloisGroup.restrictHom Γ G K L M _ = IsGaloisGroup.restrictHom Γ G K L M 1
      rw [map_one, map_mul, map_zpow, map_zpow, zpow_mul, zpow_mul, zpow_natCast,
        zpow_natCast, pow_card_eq_one, pow_card_eq_one, one_zpow, one_zpow, mul_one]
    · show cyclotomicCharacter hζ _ = cyclotomicCharacter hζ 1
      rw [map_one, map_mul, map_zpow, map_zpow]
      exact hκ
  have hκ : Function.Injective (cyclotomicCharacter
      (G := ↥(Subgroup.closure ({frobeniusElement K M Γ v, ρ} : Set Γ))) hζ) :=
    (injective_iff_map_eq_one _).mpr fun h hh =>
      Subtype.ext (hH h.1 h.2 ((cyclotomicCharacter_subgroup hζ _ h).symm.trans hh))
  have hφH : frobeniusElement K M Γ v ∈
      Subgroup.closure ({frobeniusElement K M Γ v, ρ} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hρH : Subgroup.zpowers ρ ≤ Subgroup.closure ({frobeniusElement K M Γ v, ρ} : Set Γ) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  -- `v 𝔟^{-d} ∈ D_H` has Artin symbol in `Λ`
  refine mem_rayPrincipal_sup_frobeniusPowerGroup K M N hur hζ hmN _ _ hκ
    (Subgroup.div_mem _ (Subgroup.subset_closure ⟨v, 1, hv, by rwa [pow_one], (pow_one _).symm⟩)
      (Subgroup.zpow_mem _ (frobeniusPowerGroup_mono K M N hρH h𝔟) d)) ?_
  rw [MonoidHom.mem_ker, map_div, map_zpow, artinMap_idealUnit_prime, frobeniusOrOne,
    if_pos (hur v hv), h𝔟ρ, map_div, map_zpow, restrictHom_frobeniusElement K L M hL, hd,
    div_self']

end GaloisForLFunctions
