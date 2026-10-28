import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersGiveConvergentLSeries

/-!
# Ray classes of principal ideals are read by residues

* **Residues determine ray classes** (`rayResidueClass`, `rayResidueClass_apply`): the ray class of
  `(α)`, `α ∈ K_𝔪`, depends only on `rayHom α ∈ (𝓞_K/𝔪₀)ˣ × {±1}^{𝔪∞}`; its image is the kernel of
  `Cl_𝔪 → Cl_K` (`range_rayResidueClass`).
* **Integral ideals** (`idealUnit_mem_idealGroup_iff`): an integral ideal is prime to `𝔪` iff
  `𝔞 + 𝔪₀ = (1)`.
* **Representatives prime to `𝔪`** (`exists_integral_rep`): every ideal class contains an integral
  ideal prime to `𝔪`: for `J` in the inverse class pick `x` with `J𝔪₀ + (x) = J`, then
  `𝔟 = (x)J⁻¹` (`exists_sup_span_eq`). So `Cl_𝔪 → Cl_K` is onto (`toClassGroup_surjective`).
* **Integral elements** (`rayHom_algebraMap`): for `γ ∈ 𝓞_K` prime to `𝔪₀`, `rayHom γ` is
  `(γ mod 𝔪₀, signs of γ)`.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- The ray class of `(α)` read from `rayHom α`: the map `rayHom(K_𝔪) → Cl_𝔪`. -/
def rayResidueClass : (rayHom 𝔪).range →* RayClassGroup 𝔪 :=
  (QuotientGroup.lift _ (rayClassOfElt 𝔪) (ker_rayHom_le 𝔪)).comp
    (QuotientGroup.quotientKerEquivRange (rayHom 𝔪)).symm.toMonoidHom

theorem rayResidueClass_apply (α : primeToUnits 𝔪) :
    rayResidueClass 𝔪 ⟨rayHom 𝔪 α, α, rfl⟩ = rayClassOfElt 𝔪 α := by
  rw [rayResidueClass, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have h : (QuotientGroup.quotientKerEquivRange (rayHom 𝔪)).symm ⟨rayHom 𝔪 α, α, rfl⟩ =
      (α : primeToUnits 𝔪 ⧸ (rayHom 𝔪).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h, QuotientGroup.lift_mk]

theorem toClassGroup_rayClass (I : idealGroup 𝔪) :
    toClassGroup 𝔪 (rayClass 𝔪 I) = ClassGroup.mk K (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  QuotientGroup.lift_mk _ _ _

/-- The ray classes of principal ideals form the kernel of `Cl_𝔪 → Cl_K`. -/
theorem range_rayResidueClass : (rayResidueClass 𝔪).range = (toClassGroup 𝔪).ker := by
  ext c
  constructor
  · rintro ⟨⟨_, α, rfl⟩, rfl⟩
    rw [rayResidueClass_apply, MonoidHom.mem_ker, rayClassOfElt, MonoidHom.comp_apply,
      toClassGroup_rayClass]
    show ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K (α : Kˣ)) = 1
    rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  · intro hc
    obtain ⟨γ, hγ⟩ := ker_toClassGroup_le 𝔪 c hc
    exact ⟨⟨rayHom 𝔪 γ, γ, rfl⟩, (rayResidueClass_apply 𝔪 γ).trans hγ⟩

/-- The exponent of `v` in a non-zero integral ideal vanishes iff `v` does not divide it. -/
theorem count_coe_eq_zero_iff {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 ↔ ¬ v.asIdeal ∣ I := by
  rw [count_coe K v hI, Nat.cast_eq_zero, ← not_ne_iff,
    Associates.count_ne_zero_iff_dvd hI v.prime.irreducible]

/-- An integral ideal is prime to `𝔪` iff it is coprime to `𝔪₀`. -/
theorem idealUnit_mem_idealGroup_iff {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    idealUnit hI ∈ idealGroup 𝔪 ↔ I ⊔ 𝔪.fin = ⊤ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := fun h0 => 𝔪.fin_ne_bot (le_bot_iff.mp (h0 ▸ le_sup_right.trans hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
    have h1 := h v (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle))
    rw [coe_idealUnit, count_coe_eq_zero_iff hI] at h1
    exact h1 (Ideal.dvd_iff_le.mpr (le_sup_left.trans hle))
  · intro h v hv
    rw [coe_idealUnit, count_coe_eq_zero_iff hI]
    intro hvI
    exact v.isPrime.ne_top (eq_top_iff.mpr (h ▸ sup_le (Ideal.dvd_iff_le.mp hvI)
      (Ideal.dvd_iff_le.mp hv)))

/-- **Every ideal class contains an integral ideal prime to `𝔪`**. -/
theorem exists_integral_rep (k : ClassGroup (𝓞 K)) :
    ∃ (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥), 𝔟 ⊔ 𝔪.fin = ⊤ ∧ ClassGroup.mk K (idealUnit h𝔟) = k := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective k⁻¹
  have hJ0 : (J : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  by_cases htop : 𝔪.fin = ⊤
  · -- the trivial modulus: any integral representative works
    obtain ⟨J', hJ'⟩ := ClassGroup.mk0_surjective k
    refine ⟨J', nonZeroDivisors.coe_ne_zero J', by rw [htop, sup_top_eq], ?_⟩
    rw [← hJ', ← ClassGroup.mk_mk0 K]
    rfl
  -- `J𝔪₀ + (x) = J`
  obtain ⟨x, hx⟩ := exists_sup_span_eq (Ideal.mul_le_right (I := (J : Ideal (𝓞 K))) (J := 𝔪.fin))
    (mul_ne_zero hJ0 𝔪.fin_ne_bot)
  have hxJ : Ideal.span {x} ≤ J := hx ▸ le_sup_right
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.mpr hxJ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at hx
    have : (J : Ideal (𝓞 K)) * 𝔪.fin = J * ⊤ := by rw [hx, Ideal.mul_top]
    exact htop (mul_left_cancel₀ hJ0 this)
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h𝔟
    exact hx0 h𝔟
  refine ⟨𝔟, h𝔟0, ?_, ?_⟩
  · -- `J (𝔪₀ + 𝔟) = J`
    have : (J : Ideal (𝓞 K)) * (𝔟 ⊔ 𝔪.fin) = J * ⊤ := by
      rw [Ideal.mul_sup, ← h𝔟, sup_comm, hx, Ideal.mul_top]
    exact mul_left_cancel₀ hJ0 this
  · -- `[𝔟] = [(x)] [J]⁻¹ = [J]⁻¹ = k`
    have hprod : idealUnit (mul_ne_zero hJ0 h𝔟0) = idealUnit hJ0 * idealUnit h𝔟0 :=
      idealUnit_mul hJ0 h𝔟0
    have hprin : ClassGroup.mk K (idealUnit (mul_ne_zero hJ0 h𝔟0)) = 1 := by
      rw [ClassGroup.mk_eq_one_iff, coe_idealUnit, ← h𝔟]
      exact ⟨⟨_, by rw [coeIdeal_span_singleton, coe_spanSingleton]⟩⟩
    rw [hprod, map_mul] at hprin
    have hJk : ClassGroup.mk K (idealUnit hJ0) = k⁻¹ := by
      rw [← hJ, ← ClassGroup.mk_mk0 K]
      rfl
    rw [hJk] at hprin
    exact (inv_mul_eq_one.mp hprin).symm

/-- `Cl_𝔪 → Cl_K` is onto. -/
theorem toClassGroup_surjective : Function.Surjective (toClassGroup 𝔪) := by
  intro k
  obtain ⟨𝔟, h𝔟0, h𝔟, hk⟩ := exists_integral_rep 𝔪 k
  refine ⟨rayClass 𝔪 ⟨idealUnit h𝔟0, (idealUnit_mem_idealGroup_iff 𝔪 h𝔟0).mpr h𝔟⟩, ?_⟩
  rw [toClassGroup_rayClass]
  exact hk

/-- A non-zero integral element lying in no prime of `𝔪₀` is prime to `𝔪`. -/
theorem mk0_mem_primeToUnits {γ : 𝓞 K} (hγ0 : algebraMap (𝓞 K) K γ ≠ 0)
    (hγ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → γ ∉ v.asIdeal) :
    Units.mk0 _ hγ0 ∈ primeToUnits 𝔪 := by
  intro v hv
  rw [Units.val_mk0, valuation_of_algebraMap]
  rcases (intValuation_le_one v γ).lt_or_eq with h | h
  · exact absurd ((intValuation_lt_one_iff_mem v γ).mp h) (hγ v hv)
  · exact h

/-- **Integral elements**: `rayHom γ = (γ mod 𝔪₀, signs of γ)`. -/
theorem rayHom_algebraMap {γ : 𝓞 K} (hγ0 : algebraMap (𝓞 K) K γ ≠ 0)
    (hγ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → γ ∉ v.asIdeal) :
    rayHom 𝔪 ⟨_, mk0_mem_primeToUnits 𝔪 hγ0 hγ⟩ =
      (unitMod 𝔪 hγ, signAtInf 𝔪 (Units.mk0 _ hγ0)) := by
  have h1 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → (1 : 𝓞 K) ∉ v.asIdeal :=
    fun v _ h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hred : reduce 𝔪 ⟨_, mk0_mem_primeToUnits 𝔪 hγ0 hγ⟩ = unitMod 𝔪 hγ := by
    rw [reduce_eq 𝔪 _ hγ h1 (by simp)]
    have : unitMod 𝔪 h1 = 1 := by
      ext
      simp [coe_unitMod]
    rw [this, inv_one, mul_one]
  exact Prod.ext hred rfl

end GaloisForLFunctions.HeckeLFunctions
