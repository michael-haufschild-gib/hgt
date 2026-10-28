import GaloisForLFunctions.HeckeLFunctions.ElementsPrimeToAModulusReduceModuloIt

/-!
# The ray class group is finite

For a modulus `𝔪` of a number field `K`, let `I^𝔪` be the group of fractional ideals prime to `𝔪₀`
(`idealGroup`) and `P_𝔪 = {(α) : α ∈ K^{𝔪,1}_+}` (`rayPrincipal`). The **ray class group** is
`Cl_𝔪 = I^𝔪 / P_𝔪` (`RayClassGroup`); it is finite (`finite_rayClassGroup`).

* **Valuation and exponent** (`count_spanSingleton_eq_zero_iff`): `(α)` has exponent `0` at `v` iff
  `v(α) = 1`; so `(α) ∈ I^𝔪` iff `α ∈ K_𝔪` (`toPrincipalIdeal_mem_idealGroup_iff`).
* **The map to the class group** (`toClassGroup`) has kernel inside the image of `K_𝔪`
  (`ker_toClassGroup_le`), and `K_𝔪 → Cl_𝔪` factors through `K_𝔪/K^{𝔪,1}_+ ↪ (𝓞_K/𝔪₀)ˣ × {±1}^{𝔪∞}`;
  with `Cl_K` finite this bounds `Cl_𝔪`.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The exponent of `v` in the principal ideal `(r)`. -/
abbrev primeCount (v : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors

theorem count_spanSingleton_algebraMap (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    count K v (spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) = primeCount v r := by
  rw [← coeIdeal_span_singleton, count_coe K v (by simpa using hr)]

theorem valuation_algebraMap_eq (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    valuation K v (algebraMap (𝓞 K) K r) = WithZero.exp (-(primeCount v r : ℤ)) := by
  rw [valuation_of_algebraMap, intValuation_def, if_neg hr]

/-- **Valuation and exponent**: `(α)` has exponent `0` at `v` iff `v(α) = 1`. -/
theorem count_spanSingleton_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    count K v (spanSingleton (𝓞 K)⁰ (α : K)) = 0 ↔ valuation K v (α : K) = 1 := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (α : K)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_div] at hxy
    exact α.ne_zero hxy.symm
  have hxK : algebraMap (𝓞 K) K x ≠ 0 := by simpa using hx0
  have hyK : algebraMap (𝓞 K) K y ≠ 0 := by simpa using hy0
  rw [← hxy, div_eq_mul_inv, ← spanSingleton_mul_spanSingleton, ← spanSingleton_inv,
    count_mul K v (spanSingleton_ne_zero_iff.mpr hxK)
      (inv_ne_zero (spanSingleton_ne_zero_iff.mpr hyK)),
    count_inv, count_spanSingleton_algebraMap v hx0, count_spanSingleton_algebraMap v hy0,
    map_mul, map_inv₀, valuation_algebraMap_eq v hx0, valuation_algebraMap_eq v hy0,
    mul_inv_eq_one₀ (WithZero.exp_ne_zero), WithZero.exp_inj]
  omega

variable (𝔪 : Modulus K)

/-- The group `I^𝔪` of fractional ideals prime to `𝔪₀`. -/
def idealGroup : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  one_mem' v _ := by rw [Units.val_one, count_one]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]

theorem toPrincipalIdeal_mem_idealGroup_iff (α : Kˣ) :
    toPrincipalIdeal (𝓞 K) K α ∈ idealGroup 𝔪 ↔ α ∈ primeToUnits 𝔪 := by
  refine forall₂_congr fun v _ => ?_
  rw [coe_toPrincipalIdeal]
  exact count_spanSingleton_eq_zero_iff v α

/-- The group `P_𝔪` of principal ideals `(α)`, `α ∈ K^{𝔪,1}_+`. -/
def rayPrincipal : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (rayGroup 𝔪).map (toPrincipalIdeal (𝓞 K) K)

theorem rayPrincipal_le : rayPrincipal 𝔪 ≤ idealGroup 𝔪 := by
  rintro _ ⟨α, hα, rfl⟩
  exact (toPrincipalIdeal_mem_idealGroup_iff 𝔪 α).mpr (rayGroup_le 𝔪 hα)

/-- The **ray class group** `Cl_𝔪 = I^𝔪 / P_𝔪`. -/
abbrev RayClassGroup : Type _ := idealGroup 𝔪 ⧸ (rayPrincipal 𝔪).subgroupOf (idealGroup 𝔪)

/-- The ray class of an ideal prime to `𝔪`. -/
def rayClass : idealGroup 𝔪 →* RayClassGroup 𝔪 := QuotientGroup.mk' _

/-- The ray class of a principal ideal `(α)`, `α ∈ K_𝔪`. -/
def rayClassOfElt : primeToUnits 𝔪 →* RayClassGroup 𝔪 :=
  (rayClass 𝔪).comp (((toPrincipalIdeal (𝓞 K) K).comp (primeToUnits 𝔪).subtype).codRestrict
    (idealGroup 𝔪) fun α => (toPrincipalIdeal_mem_idealGroup_iff 𝔪 α).mpr α.2)

/-- The ray group `K^{𝔪,1}_+` has trivial ray classes. -/
theorem ker_rayHom_le : (rayHom 𝔪).ker ≤ (rayClassOfElt 𝔪).ker := by
  intro α hα
  rw [MonoidHom.mem_ker, rayClassOfElt, MonoidHom.comp_apply, rayClass, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨α, ⟨α, hα, rfl⟩, rfl⟩

/-- The map `Cl_𝔪 → Cl_K`. -/
def toClassGroup : RayClassGroup 𝔪 →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ ((ClassGroup.mk K).comp (idealGroup 𝔪).subtype) fun I hI => by
    rw [Subgroup.mem_subgroupOf] at hI
    obtain ⟨α, -, hα⟩ := hI
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hα,
      ClassGroup.mk_eq_one_iff,
      coe_toPrincipalIdeal, coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩

/-- The kernel of `Cl_𝔪 → Cl_K` consists of classes of principal ideals `(γ)`, `γ ∈ K_𝔪`. -/
theorem ker_toClassGroup_le (c : RayClassGroup 𝔪) (hc : toClassGroup 𝔪 c = 1) :
    ∃ γ : primeToUnits 𝔪, rayClassOfElt 𝔪 γ = c := by
  obtain ⟨I, rfl⟩ := QuotientGroup.mk_surjective c
  have h : ClassGroup.mk K (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := hc
  rw [ClassGroup.mk_eq_one_iff] at h
  obtain ⟨g, hg⟩ := h.principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero
    apply coeToSubmodule_injective
    dsimp only
    rw [hg, coe_zero, Submodule.span_singleton_eq_bot.mpr rfl]
  have hI : toPrincipalIdeal (𝓞 K) K (Units.mk0 g hg0) = I := by
    rw [toPrincipalIdeal_eq_iff]
    apply coeToSubmodule_injective
    dsimp only
    rw [hg, coe_spanSingleton]
    rfl
  have hγ : Units.mk0 g hg0 ∈ primeToUnits 𝔪 :=
    (toPrincipalIdeal_mem_idealGroup_iff 𝔪 _).mp (hI ▸ I.2)
  exact ⟨⟨_, hγ⟩, congrArg (rayClass 𝔪) (Subtype.ext hI)⟩

/-- **The ray class group is finite**. -/
theorem finite_rayClassGroup : Finite (RayClassGroup 𝔪) := by
  -- the image of `K_𝔪` is finite: it factors through `K_𝔪 / ker rayHom`
  let ρ' := QuotientGroup.lift (rayHom 𝔪).ker (rayClassOfElt 𝔪) (ker_rayHom_le 𝔪)
  have hfinQ : Finite (primeToUnits 𝔪 ⧸ (rayHom 𝔪).ker) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective (rayHom 𝔪))
  have hker : ((toClassGroup 𝔪).ker : Set (RayClassGroup 𝔪)) ⊆ Set.range ρ' := by
    intro c hc
    obtain ⟨γ, hγ⟩ := ker_toClassGroup_le 𝔪 c hc
    exact ⟨QuotientGroup.mk γ, hγ⟩
  have hkerfin : Finite (toClassGroup 𝔪).ker :=
    ((Set.finite_range ρ').subset hker).to_subtype
  -- `Cl_𝔪` is an extension of a subgroup of `Cl_K` by a finite kernel
  have hQ : Finite (RayClassGroup 𝔪 ⧸ (toClassGroup 𝔪).ker) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective (toClassGroup 𝔪))
  refine Nat.finite_of_card_ne_zero ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (toClassGroup 𝔪).ker]
  exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

instance : Finite (RayClassGroup 𝔪) := finite_rayClassGroup 𝔪

end GaloisForLFunctions.HeckeLFunctions
