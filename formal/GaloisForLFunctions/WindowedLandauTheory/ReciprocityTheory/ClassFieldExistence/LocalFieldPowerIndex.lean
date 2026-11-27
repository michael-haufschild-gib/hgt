import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.DeepUnitPowers
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalPowerIndexProducts
import GaloisForLFunctions.HTGeometry.SplitSurjectiveHasse
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.RingTheory.Valuation.Integers

/-! In a local field the uniformizer contributes an extra factor of n
to the power index of the integral units. -/

noncomputable section

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ABHN
open scoped ValuativeRel WithZero

namespace GlobalTheory.Reciprocity

private theorem index_power_integer (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by
  have h : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range =
      (AddSubgroup.zmultiples (n : ℤ)).toSubgroup := by
    ext x
    rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by simp⟩
    · rintro ⟨k, hk⟩
      refine ⟨Multiplicative.ofAdd k, Multiplicative.toAdd.injective ?_⟩
      simp [hk]
  rw [h, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  simp

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [T2Space F]
variable (v : Valuation F ℤᵐ⁰) [v.Compatible]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [T2Space F] in
theorem valuationSubring_eq_integer : v.valuationSubring.toSubring = 𝒪[F] := by
  ext x
  change v x ≤ 1 ↔ ValuativeRel.valuation F x ≤ 1
  simpa only [map_one] using (ValuativeRel.isEquiv v (ValuativeRel.valuation F) x 1)

private def unitsToValuationKernel : v.valuationSubringˣ ≃* (tameValHom v).ker := by
  let f := Units.map (algebraMap v.valuationSubring F).toMonoidHom
  have hf (u : v.valuationSubringˣ) : f u ∈ (tameValHom v).ker := by
    rw [tameValHom_mem_ker_iff]
    exact (Valuation.integer.integers v).isUnit_iff_valuation_eq_one.mp u.isUnit
  exact MulEquiv.ofBijective (f.codRestrict _ hf)
    ⟨fun a b h => Units.ext (Subtype.ext (congrArg (fun x : (tameValHom v).ker => (x.val : F)) h)),
      fun x => by
        obtain ⟨y, hy⟩ := tameValHom_ker_unitsMap_surjective v x.val x.2
        exact ⟨y, Subtype.ext hy⟩⟩

private def unitSplit (hv : Function.Surjective v) : Fˣ ≃* Multiplicative ℤ × 𝒪[F]ˣ := by
  let x := (hv (WithZero.exp (-1 : ℤ))).choose
  have hx : v x = WithZero.exp (-1 : ℤ) := (hv _).choose_spec
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  let π := Units.mk0 x hx0
  have hπ : Multiplicative.toAdd (tameValHom v π) = 1 := by
    rw [tameValHom_toAdd]
    have h : tameUnzero v π = Multiplicative.ofAdd (-1 : ℤ) := by
      apply WithZero.coe_inj.mp
      rw [coe_tameUnzero]
      exact hx
    rw [h]
    rfl
  let D := residueDataOfValuation v π hπ
  let e := splitSurjectiveCommGroupHomEquivProdKer D.val (residueDataValuationSection D)
    (residueDataValuationSection_rightInverse D)
  let j := Units.mapEquiv (RingEquiv.subringCongr (valuationSubring_eq_integer v)).toMulEquiv
  exact e.trans (MulEquiv.prodCongr (MulEquiv.refl _) ((unitsToValuationKernel v).symm.trans j))

include v in
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [T2Space F] in
private theorem card_integral_power_kernel_eq_roots {n : ℕ} (hn : n ≠ 0) :
    Nat.card (powMonoidHom n : 𝒪[F]ˣ →* 𝒪[F]ˣ).ker = Nat.card (rootsOfUnity n F) := by
  let j := Units.mapEquiv (RingEquiv.subringCongr (valuationSubring_eq_integer v)).symm.toMulEquiv
  let f := (Units.map (algebraMap v.valuationSubring F).toMonoidHom).comp j.toMonoidHom
  have hinj : Function.Injective f :=
    (Units.map_injective Subtype.val_injective).comp j.injective
  let U := (powMonoidHom n : 𝒪[F]ˣ →* 𝒪[F]ˣ).ker
  have h : U.map f = rootsOfUnity n F := by
    ext x
    rw [Subgroup.mem_map, mem_rootsOfUnity]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [← map_pow, show a ^ n = 1 from ha, map_one]
    · intro hx
      have hxn : v (x : F) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]
      have hxv : v (x : F) = 1 := by
        have h0 : v (x : F) ≠ 0 := by simp
        have he := congrArg WithZero.log hxn
        rw [WithZero.log_pow, WithZero.log_one, nsmul_eq_mul] at he
        rw [← WithZero.exp_log h0, (mul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr hn),
          WithZero.exp_zero]
      obtain ⟨y, hy⟩ := tameValHom_ker_unitsMap_surjective v x ((tameValHom_mem_ker_iff v x).mpr hxv)
      have hf : f (j.symm y) = x := by
        change Units.map (algebraMap v.valuationSubring F).toMonoidHom (j (j.symm y)) = x
        rw [MulEquiv.apply_symm_apply]
        exact hy
      refine ⟨j.symm y, MonoidHom.mem_ker.mpr (hinj ?_), hf⟩
      rw [powMonoidHom_apply, map_pow, hf, hx, map_one]
  rw [← h, Subgroup.card_map_of_injective hinj]

theorem index_power_localField (hv : Function.Surjective v) {n d : ℕ} (hn : n ≠ 0)
    {π : 𝒪[F]} (hπ : Irreducible π) {ε : 𝒪[F]ˣ}
    (hnd : (n : 𝒪[F]) = (ε : 𝒪[F]) * π ^ d) :
    (powMonoidHom n : Fˣ →* Fˣ).range.index =
      n * Nat.card (rootsOfUnity n F) * Nat.card 𝓀[F] ^ d := by
  rw [index_power_congr (unitSplit v hv), index_power_prod, index_power_integer,
    index_range_pow_integralUnits_of_uniformizer hπ hnd,
    card_integral_power_kernel_eq_roots v hn, mul_assoc]

end GlobalTheory.Reciprocity
