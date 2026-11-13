import GaloisForLFunctions.RHTower.Artin.NormsArePositiveAtTheRamifiedRealPlaces
import GaloisForLFunctions.RHTower.Artin.RelativeNormsOfRayElementsAreRayElements

/-!
# Ideals are principal up to a descent set of primes

The dictionary between the ideals of a number field and the elements of its multiplicative
group, for an abelian extension `L/K` with group `G`.

* The exponent of `v` in `(α)` is `v_v(α)` (`count_toPrincipalIdeal`).
* `idealsSupportedOn T`: the fractional ideals with trivial exponent outside `T`. Every ideal is
  the product of an ideal prime to `c` and of an ideal supported on the primes dividing `c`
  (`mem_idealGroup_sup_idealsSupportedOn`). If the primes outside `S` are principal up to `S`,
  every ideal is the product of a principal ideal and of an ideal supported on `S`
  (`mem_range_toPrincipalIdeal_sup_idealsSupportedOn`).
* The norm of an ideal of `L` supported above `S` is supported on `S`
  (`idealNormHom_mem_idealsSupportedOn`); an element of `K^×` whose ideal is supported on `S` is
  a unit outside the primes of `L` above `S` (`ofMul_mem_comap_sUnits_of_toPrincipalIdeal_mem`).
* `N_{L/K}(y) = Π_τ τ y` (`algebraMap_norm_eq_prod_smul`), so the norm of an element is a norm
  for the action of `G` on `L^×` (`ofMul_norm_mem_comap_range_actionNorm`).
* An element of the ray modulo `(q^J) ∞`, `J ≥ 1`, is congruent to `1` to the order `J` at the
  primes of `L` above the primes dividing `q`
  (`algebraMap_sub_one_mem_level_of_mem_rayGroup`), and positive at the real places
  (`ofMul_mem_positiveAtRamified_of_mem_rayGroup`).
* **Descent moduli** (`exists_nat_unramified_principalOutside`): there is `q ≥ 1` such that,
  with `S` the set of primes of `K` dividing `q`, `L/K` is unramified outside `S` and the primes
  of `K` and of `L` are principal up to `S`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

section Ideals

variable {K : Type*} [Field K] [NumberField K]

/-- **The exponent of `v` in the principal ideal `(α)` is `v_v(α)`.** -/
theorem count_toPrincipalIdeal (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    count K v ((toPrincipalIdeal (𝓞 K) K α : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = ordAt K v (Additive.ofMul α) := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (α : K)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hxy
    exact α.ne_zero hxy.symm
  have hxK : algebraMap (𝓞 K) K x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hx0
  have hyK : algebraMap (𝓞 K) K y ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hy0
  -- the valuation of `α = x / y`
  have hval := valuation_eq_exp_neg_ordAt K v α
  rw [← hxy, map_div₀, valuation_algebraMap_eq v hx0, valuation_algebraMap_eq v hy0,
    div_eq_iff WithZero.exp_ne_zero, ← WithZero.exp_add, WithZero.exp_inj] at hval
  rw [coe_toPrincipalIdeal, ← hxy, div_eq_mul_inv, ← spanSingleton_mul_spanSingleton,
    ← spanSingleton_inv,
    count_mul K v (spanSingleton_ne_zero_iff.mpr hxK)
      (inv_ne_zero (spanSingleton_ne_zero_iff.mpr hyK)),
    count_inv, count_spanSingleton_algebraMap v hx0, count_spanSingleton_algebraMap v hy0]
  linarith

/-- The fractional ideals supported on a set `T` of primes: trivial exponent outside `T`. -/
def idealsSupportedOn (T : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v, v ∉ T → count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  one_mem' v _ := by rw [Units.val_one, count_one]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]

theorem idealUnit_prime_mem_idealsSupportedOn {T : Set (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ T) :
    idealUnit v.ne_bot ∈ idealsSupportedOn T := by
  intro w hw
  rw [coe_idealUnit]
  exact count_maximal_coprime K w fun h => hw (h ▸ hv)

variable (K) in
/-- **Every ideal is the product of an ideal prime to `c` and of an ideal supported on the
primes dividing `c`.** -/
theorem mem_idealGroup_sup_idealsSupportedOn (c : ℕ) [NeZero c]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    I ∈ idealGroup (normModulus K c) ⊔
      idealsSupportedOn {v : HeightOneSpectrum (𝓞 K) | (c : 𝓞 K) ∈ v.asIdeal} := by
  have key : ∀ v : HeightOneSpectrum (𝓞 K), idealUnit v.ne_bot ∈
      idealGroup (normModulus K c) ⊔
        idealsSupportedOn {v : HeightOneSpectrum (𝓞 K) | (c : 𝓞 K) ∈ v.asIdeal} := fun v => by
    by_cases hv : (c : 𝓞 K) ∈ v.asIdeal
    · exact Subgroup.mem_sup_right (idealUnit_prime_mem_idealsSupportedOn hv)
    · exact Subgroup.mem_sup_left (idealUnit_prime_mem_idealGroup _ fun hdvd =>
        hv ((dvd_normModulus_fin_iff K c v).mp hdvd))
  have h := primeValuesHom_mem _ (u := fun v : HeightOneSpectrum (𝓞 K) => idealUnit v.ne_bot) I
    fun v _ => key v
  rwa [primeValuesHom_idealUnit] at h

/-- **Ideals are principal up to `S`**: if the primes outside `S` are principal up to `S`,
every ideal is the product of a principal ideal and of an ideal supported on `S`. -/
theorem mem_range_toPrincipalIdeal_sup_idealsSupportedOn
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : PrincipalOutside K S)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    I ∈ (toPrincipalIdeal (𝓞 K) K).range ⊔ idealsSupportedOn S := by
  have key : ∀ v : HeightOneSpectrum (𝓞 K), idealUnit v.ne_bot ∈
      (toPrincipalIdeal (𝓞 K) K).range ⊔ idealsSupportedOn S := fun v => by
    by_cases hv : v ∈ S
    · exact Subgroup.mem_sup_right (idealUnit_prime_mem_idealsSupportedOn hv)
    · -- `v = (c) · v (c)⁻¹` with `(c)` equal to `v` outside `S`
      obtain ⟨c, hc1, hc0⟩ := hS v hv
      have hsupp : idealUnit v.ne_bot / toPrincipalIdeal (𝓞 K) K (Additive.toMul c) ∈
          idealsSupportedOn S := by
        intro w hw
        rw [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
          count_mul K w (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)), count_inv,
          count_toPrincipalIdeal, ofMul_toMul, coe_idealUnit]
        by_cases hwv : w = v
        · rw [hwv, count_self, hc1, add_neg_cancel]
        · rw [count_maximal_coprime K w (Ne.symm hwv), hc0 w hw hwv, neg_zero, add_zero]
      have hc : toPrincipalIdeal (𝓞 K) K (Additive.toMul c) ∈
          (toPrincipalIdeal (𝓞 K) K).range ⊔ idealsSupportedOn S :=
        Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨Additive.toMul c, rfl⟩)
      have h := Subgroup.mul_mem _
        (Subgroup.mem_sup_right (S := (toPrincipalIdeal (𝓞 K) K).range) hsupp) hc
      rwa [div_mul_cancel] at h
  have h := primeValuesHom_mem _ (u := fun v : HeightOneSpectrum (𝓞 K) => idealUnit v.ne_bot) I
    fun v _ => key v
  rwa [primeValuesHom_idealUnit] at h

end Ideals

/-- **The norm of an ideal supported above `S` is supported on `S`.** -/
theorem idealNormHom_mem_idealsSupportedOn (K L : Type u) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {S : Set (HeightOneSpectrum (𝓞 K))}
    {𝔄 : (FractionalIdeal (𝓞 L)⁰ L)ˣ}
    (h : 𝔄 ∈ idealsSupportedOn {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}) :
    idealNormHom K L 𝔄 ∈ idealsSupportedOn S := by
  show primeValuesHom (fun w : HeightOneSpectrum (𝓞 L) =>
    idealUnit (w.under (𝓞 K)).ne_bot ^ w.asIdeal.inertiaDeg (𝓞 K)) 𝔄 ∈ _
  refine primeValuesHom_mem _ 𝔄 fun w hw =>
    Subgroup.pow_mem _ (idealUnit_prime_mem_idealsSupportedOn ?_) _
  exact not_not.mp fun hS => hw (h w hS)

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction infinitePlaceMulAction

/-! ### Elements and ideals -/

omit [NumberField K] [NumberField L] [Fintype G] in
/-- **The norm is the product of the conjugates.** -/
theorem algebraMap_norm_eq_prod_smul [Fintype G] (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ τ : G, τ • x := by
  haveI : IsGalois K L := IsGaloisGroup.isGalois G K L
  haveI : FiniteDimensional K L := IsGaloisGroup.finiteDimensional G K L
  rw [Algebra.norm_eq_prod_automorphisms]
  exact (Fintype.prod_equiv (IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv _ _ fun _ => rfl).symm

omit [NumberField K] [NumberField L] in
/-- The norm of `y ∈ L^×` is a norm for the action of `G` on `L^×`. -/
theorem ofMul_norm_mem_comap_range_actionNorm (y : Lˣ) :
    Additive.ofMul (Units.map (Algebra.norm K : L →* K) y) ∈
      (actionNorm (fieldUnitsRep L G)).range.comap (baseIncl K L) := by
  refine AddSubgroup.mem_comap.mpr (AddMonoidHom.mem_range.mpr ⟨Additive.ofMul y, ?_⟩)
  rw [actionNorm_apply]
  refine Additive.toMul.injective (Units.ext ?_)
  rw [toMul_sum, Units.coe_prod]
  exact (algebraMap_norm_eq_prod_smul K L G (y : L)).symm

omit [Fintype G] in
/-- **An element whose ideal is supported on `S` is a unit outside the primes above `S`.** -/
theorem ofMul_mem_comap_sUnits_of_toPrincipalIdeal_mem
    (S : Finset (HeightOneSpectrum (𝓞 K))) {β : Kˣ}
    (h : toPrincipalIdeal (𝓞 K) K β ∈ idealsSupportedOn (S : Set (HeightOneSpectrum (𝓞 K)))) :
    Additive.ofMul β ∈ (sUnits L G (primesAbove K L G S)).comap (baseIncl K L) := by
  show ∀ w, w ∉ primesAbove K L G S → ordAt L w (baseIncl K L (Additive.ofMul β)) = 0
  intro w hw
  rw [ordAt_baseIncl, ← count_toPrincipalIdeal, h _ hw, mul_zero]

/-! ### Elements of the ray -/

omit [Fintype G] in
/-- **Ray elements are congruent to `1` at the primes above `S`**: an element of the ray modulo
`(q^J) ∞`, `J ≥ 1`, is congruent to `1` to the order `J` at the primes of `L` above the primes
of `S`, if these divide `q`. -/
theorem algebraMap_sub_one_mem_level_of_mem_rayGroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    {q J : ℕ} [NeZero (q ^ J)] (hJ : J ≠ 0) (hS : ∀ v ∈ S, (q : 𝓞 K) ∈ v.asIdeal) {γ : Kˣ}
    (hγ : γ ∈ rayGroup (normModulus K (q ^ J))) :
    algebraMap K L ((γ : K) - 1) ∈ level L G (primesAbove K L G S) (J : ℤ) := by
  obtain ⟨β, hβ, rfl⟩ := hγ
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one] at hβ
  -- `β = a / b` with `a ≡ b` modulo `q^J` and `b` prime to `q`
  obtain ⟨a, b, -, hab, hfrac⟩ := exists_unit_fraction (normModulus K (q ^ J)) β.2
  have ha := fun v hv => (hab v hv).1
  have hb := fun v hv => (hab v hv).2
  have hred := reduce_eq (normModulus K (q ^ J)) β ha hb hfrac
  rw [hβ.1, eq_comm, mul_inv_eq_one] at hred
  have hmk : a - b ∈ Ideal.span {((q ^ J : ℕ) : 𝓞 K)} :=
    Ideal.Quotient.eq.mp (congrArg Units.val hred)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmk
  have e : ∀ x : 𝓞 K, algebraMap K L (algebraMap (𝓞 K) K x) =
      algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) := fun x => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
  have hmul : algebraMap K L (algebraMap (𝓞 K) K b) * algebraMap K L (((β : Kˣ) : K) - 1) =
      algebraMap K L (algebraMap (𝓞 K) K (a - b)) := by
    rw [← map_mul, mul_sub, hfrac, mul_one, map_sub (algebraMap (𝓞 K) K)]
  show ∀ w, w ∈ primesAbove K L G S →
    w.valuation L (algebraMap K L (((β : Kˣ) : K) - 1)) ≤ WithZero.exp (-(J : ℤ))
  intro w hw
  have hqv : (q : 𝓞 K) ∈ (w.under (𝓞 K)).asIdeal := hS _ hw
  have hqw : (q : 𝓞 L) ∈ w.asIdeal := by
    have h := hqv
    rwa [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
  have hbw : algebraMap (𝓞 K) (𝓞 L) b ∉ w.asIdeal := fun h => by
    refine hb (w.under (𝓞 K)) ((dvd_normModulus_fin_iff K (q ^ J) _).mpr ?_) ?_
    · rw [Nat.cast_pow]
      exact Ideal.pow_mem_of_mem _ hqv J (Nat.pos_of_ne_zero hJ)
    · rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
      exact h
  -- the valuation of `β − 1 = (a − b) / b`
  have hval := congrArg (w.valuation L) hmul
  rw [map_mul, e, e, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hbw,
    one_mul] at hval
  rw [hval]
  refine (w.intValuation_le_pow_iff_mem _ J).mpr ?_
  rw [← hr, map_mul, Nat.cast_pow, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hqw J)

omit [NumberField L] [Fintype G] [CommGroup G] [MulSemiringAction G L] [IsGaloisGroup G K L] in
/-- The elements of the ray modulo `(c) ∞` are positive at the real places. -/
theorem ofMul_mem_positiveAtRamified_of_mem_rayGroup {c : ℕ} [NeZero c] {γ : Kˣ}
    (hγ : γ ∈ rayGroup (normModulus K c)) : Additive.ofMul γ ∈ positiveAtRamified K L := by
  obtain ⟨β, hβ, rfl⟩ := hγ
  rw [SetLike.mem_coe, MonoidHom.mem_ker, rayHom, MonoidHom.prod_apply, Prod.mk_eq_one] at hβ
  refine AddMonoidHom.mem_ker.mpr (congrArg Additive.ofMul (funext fun v => ?_))
  exact congrFun hβ.2 ⟨⟨v.1, isReal_of_not_isUnramifiedIn K L v.2⟩, Set.mem_univ _⟩

/-! ### Descent moduli -/

/-- **Descent moduli**: there is `q ≥ 1` such that, with `S` the set of primes of `K` dividing
`q`, the extension `L/K` is unramified outside `S` and the primes of `K` and of `L` are
principal up to `S`. -/
theorem exists_nat_unramified_principalOutside :
    ∃ (q : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))), q ≠ 0 ∧
      (∀ v, v ∈ S ↔ (q : 𝓞 K) ∈ v.asIdeal) ∧ (∀ v, v ∉ S → IsUnramifiedPrime K L G v) ∧
      PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K))) ∧
      PrincipalOutside L (primesAbove K L G S : Set (HeightOneSpectrum (𝓞 L))) := by
  obtain ⟨S₀, -, hram, hK, hL⟩ := exists_finset_unramified_principalOutside K L G ∅
  -- `q` the product of the norms; its prime divisors contain `S₀`
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = ∏ v ∈ S₀, Ideal.absNorm v.asIdeal := ⟨_, rfl⟩
  have hq : q ≠ 0 := by
    rw [hqdef]
    exact Finset.prod_ne_zero_iff.mpr fun v _ h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hspan : Ideal.span {(q : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hq
  have hfin : {v : HeightOneSpectrum (𝓞 K) | (q : 𝓞 K) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors hspan).subset fun v hv => Ideal.dvd_span_singleton.mpr hv
  have hsub : ∀ v ∈ S₀, v ∈ hfin.toFinset := fun v hv => by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem
      (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal) hv
    rw [hfin.mem_toFinset, Set.mem_setOf_eq, hqdef, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  exact ⟨q, hfin.toFinset, hq, fun v => hfin.mem_toFinset,
    fun v hv => hram v fun h => hv (hsub v h), hK.mono fun v hv => hsub v hv,
    hL.mono fun w hw => hsub _ hw⟩

end GaloisForLFunctions
