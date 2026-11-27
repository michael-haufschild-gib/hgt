import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.KummerRadicalField
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-! The radical classes and the Galois group of their radical field
are in perfect duality by the action on the roots. -/

noncomputable section

namespace GlobalTheory.Kummer

open IntermediateField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
variable {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Δ : Subgroup (PowerClasses K n))

local notation "L" => (radicalField (Ω := Ω) Δ)

private theorem exists_rep (x : Δ) :
    ∃ a : Kˣ, (a : PowerClasses K n) = x.val ∧ ∃ α : L, α ^ n = algebraMap K L (a : K) := by
  obtain ⟨a, β, ha, hβ, -⟩ := exists_radical_generators Ω Δ
  have hx : (a x : PowerClasses K n) ∈ Δ := by rw [ha x]; exact x.2
  exact ⟨a x, ha x, ⟨β x, mem_radicalField hx (hβ x)⟩, Subtype.ext (hβ x)⟩

private theorem exists_radical_action (σ : Gal(L/K)) (x : Δ) :
    ∃ z : rootsOfUnity n K, ∀ (a : Kˣ), (a : PowerClasses K n) = x.val → ∀ α : L,
      α ^ n = algebraMap K L (a : K) → σ α = algebraMap K L ((z : Kˣ) : K) * α := by
  obtain ⟨b, hb, β, hβ⟩ := exists_rep (Ω := Ω) Δ x
  have hk : (σ β / β) ^ n = 1 := by
    rw [div_pow, ← map_pow, hβ, AlgEquiv.commutes, div_self ((map_ne_zero (algebraMap K L)).mpr b.ne_zero)]
  obtain ⟨z, hz⟩ := exists_rootOfUnity_of_pow_eq_one (K := K) hk
  have hσ : σ β = algebraMap K L ((z : Kˣ) : K) * β :=
    ((eq_div_iff (radical_root_ne_zero hβ)).mp hz).symm
  refine ⟨z, fun a ha α hα => ?_⟩
  obtain ⟨u, hu⟩ := exists_scalar_mul_of_same_class (ha.trans hb.symm) hα hβ
  rw [hu, map_mul, AlgEquiv.commutes, hσ]
  ring

private def radicalAction (σ : Gal(L/K)) (x : Δ) : rootsOfUnity n K :=
  (exists_radical_action Δ σ x).choose

private theorem radicalAction_apply (σ : Gal(L/K)) (x : Δ) {a : Kˣ}
    (ha : (a : PowerClasses K n) = x.val) {α : L} (hα : α ^ n = algebraMap K L (a : K)) :
    σ α = algebraMap K L ((radicalAction Δ σ x : Kˣ) : K) * α :=
  (exists_radical_action Δ σ x).choose_spec a ha α hα

private theorem radicalAction_eq (σ : Gal(L/K)) (x : Δ) {a : Kˣ}
    (ha : (a : PowerClasses K n) = x.val) {α : L} (hα : α ^ n = algebraMap K L (a : K))
    (z : rootsOfUnity n K) (h : σ α = algebraMap K L ((z : Kˣ) : K) * α) :
    radicalAction Δ σ x = z := by
  have he := (radicalAction_apply Δ σ x ha hα).symm.trans h
  exact Subtype.ext (Units.ext ((algebraMap K L).injective (mul_right_cancel₀ (radical_root_ne_zero hα) he)))

private theorem radicalAction_mul_left (σ τ : Gal(L/K)) (x : Δ) :
    radicalAction Δ (σ * τ) x = radicalAction Δ σ x * radicalAction Δ τ x := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep (Ω := Ω) Δ x
  apply radicalAction_eq Δ (σ * τ) x ha hα
  rw [AlgEquiv.mul_apply, radicalAction_apply Δ τ x ha hα, map_mul, AlgEquiv.commutes,
    radicalAction_apply Δ σ x ha hα]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

private theorem radicalAction_mul_right (σ : Gal(L/K)) (x y : Δ) :
    radicalAction Δ σ (x * y) = radicalAction Δ σ x * radicalAction Δ σ y := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep (Ω := Ω) Δ x
  obtain ⟨b, hb, β, hβ⟩ := exists_rep (Ω := Ω) Δ y
  have hab : ((a * b : Kˣ) : PowerClasses K n) = (x * y).val := by rw [QuotientGroup.mk_mul, ha, hb]; rfl
  have hαβ : (α * β) ^ n = algebraMap K L ((a * b : Kˣ) : K) := by
    rw [mul_pow, hα, hβ, Units.val_mul, map_mul]
  apply radicalAction_eq Δ σ (x * y) hab hαβ
  rw [map_mul, radicalAction_apply Δ σ x ha hα, radicalAction_apply Δ σ y hb hβ]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

private theorem radicalAction_one_left (x : Δ) : radicalAction (Ω := Ω) Δ 1 x = 1 := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep (Ω := Ω) Δ x
  exact radicalAction_eq (Ω := Ω) Δ 1 x ha hα 1 (by simp)

private theorem radicalAction_one_right (σ : Gal(L/K)) : radicalAction Δ σ 1 = 1 := by
  have h := radicalAction_mul_right Δ σ 1 1
  rw [mul_one] at h
  exact mul_eq_left.mp h.symm

private def radicalActionLeft : Gal(L/K) →* (Δ →* rootsOfUnity n K) where
  toFun σ :=
    { toFun := radicalAction Δ σ
      map_one' := radicalAction_one_right Δ σ
      map_mul' := radicalAction_mul_right Δ σ }
  map_one' := MonoidHom.ext (radicalAction_one_left (Ω := Ω) Δ)
  map_mul' σ τ := MonoidHom.ext (radicalAction_mul_left Δ σ τ)

private def radicalActionRight : Δ →* (Gal(L/K) →* rootsOfUnity n K) where
  toFun x :=
    { toFun := fun σ => radicalAction Δ σ x
      map_one' := radicalAction_one_left (Ω := Ω) Δ x
      map_mul' := fun σ τ => radicalAction_mul_left Δ σ τ x }
  map_one' := MonoidHom.ext (radicalAction_one_right Δ)
  map_mul' x y := MonoidHom.ext (fun σ => radicalAction_mul_right Δ σ x y)

/-- A Galois automorphism acting trivially on all the radicals is trivial. -/
private theorem radicalActionLeft_injective : Function.Injective (radicalActionLeft (Ω := Ω) Δ) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := L)
    (s := {α : Ω | ∃ a : Kˣ, (a : PowerClasses K n) ∈ Δ ∧ α ^ n = algebraMap K Ω (a : K)})
    rfl ?_
  rintro y ⟨a, ha, hy⟩
  let α : L := ⟨y, mem_radicalField ha hy⟩
  have hα : α ^ n = algebraMap K L (a : K) := Subtype.ext hy
  let x : Δ := ⟨(a : PowerClasses K n), ha⟩
  have e : radicalAction Δ σ x = 1 := DFunLike.congr_fun hσ x
  have h := radicalAction_apply Δ σ x rfl hα
  rw [e] at h
  simpa using h

variable [CharZero K]

/-- A fixed radical root belongs to the base field, so its power class is one. -/
private theorem radicalActionRight_injective [Finite Δ] : Function.Injective (radicalActionRight (Ω := Ω) Δ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨a, ha, α, hα⟩ := exists_rep (Ω := Ω) Δ x
  have hfix : ∀ σ : Gal(L/K), σ α = α := fun σ => by
    have e : radicalAction Δ σ x = 1 := DFunLike.congr_fun hx σ
    simp only [radicalAction_apply Δ σ x ha hα, e, OneMemClass.coe_one, Units.val_one,
      map_one, one_mul]
  obtain ⟨b, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) α).mpr hfix
  have hb : b ≠ 0 := fun h0 => radical_root_ne_zero hα (by simp [h0])
  have hba : (Units.mk0 b hb) ^ n = a := by
    apply Units.ext
    apply (algebraMap K L).injective
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow] using hα
  apply Subtype.ext
  rw [← ha, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
  exact ⟨_, hba⟩

omit [CharZero K] in
private theorem card_dual_roots (G : Type*) [CommGroup G] [Finite G] (hG : ∀ g : G, g ^ n = 1) :
    Nat.card (G →* rootsOfUnity n K) = Nat.card G := by
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  let e : (G →* rootsOfUnity n K) ≃ (G →* Kˣ) :=
    { toFun := fun f => (rootsOfUnity n K).subtype.comp f
      invFun := fun f => f.codRestrict _ (fun g => by rw [mem_rootsOfUnity, ← map_pow, hG, map_one])
      left_inv := fun f => MonoidHom.ext fun g => rfl
      right_inv := fun f => MonoidHom.ext fun g => rfl }
  rw [Nat.card_congr e, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]

theorem radicalField_isAbelianGalois : IsAbelianGalois K L where
  toIsGalois := inferInstance
  is_comm.comm σ τ := (radicalActionLeft_injective Δ) (by rw [map_mul, map_mul, mul_comm])

omit [CharZero K] in
theorem radicalField_pow_eq_one (σ : Gal(L/K)) : σ ^ n = 1 := by
  apply radicalActionLeft_injective Δ
  rw [map_pow, map_one]
  apply MonoidHom.ext
  intro x
  have h := (radicalAction Δ σ x).property
  rw [mem_rootsOfUnity] at h
  exact Subtype.ext h

/-- The degree of a finite radical extension is the order of the subgroup
of power classes used to generate it. -/
theorem finrank_radicalField [Finite Δ] : Module.finrank K L = Nat.card Δ := by
  letI : IsAbelianGalois K L := radicalField_isAbelianGalois Δ
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  haveI : Finite (Δ →* rootsOfUnity n K) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (Gal(L/K) →* rootsOfUnity n K) := Finite.of_injective _ DFunLike.coe_injective
  have hpow (x : Δ) : x ^ n = 1 := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (powMonoidHom n : Kˣ →* Kˣ).range x.val
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ha, ← map_pow]
    change ((a ^ n : Kˣ) : PowerClasses K n) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  rw [← IsGalois.card_aut_eq_finrank]
  apply le_antisymm
  · exact (Nat.card_le_card_of_injective _ (radicalActionLeft_injective Δ)).trans_eq (card_dual_roots Δ hpow)
  · exact (Nat.card_le_card_of_injective _ (radicalActionRight_injective Δ)).trans_eq
      (card_dual_roots Gal(L/K) (radicalField_pow_eq_one Δ))

end GlobalTheory.Kummer
