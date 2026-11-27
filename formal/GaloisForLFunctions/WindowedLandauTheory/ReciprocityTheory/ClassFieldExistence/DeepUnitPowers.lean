import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrincipalUnitIndices
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CompactFiltrationLifting
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ImageIndexFromSubgroup

/-! If the valuation of n is d, the n-th power map is injective at
depth d+1 and increases depth by d. Its graded map is multiplication
by the unit part of n. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.ABHN IsLocalRing
open scoped ValuativeRel

namespace GlobalTheory.Reciprocity

private theorem exists_power_displacement {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ c : R, (1 + x) ^ n = 1 + n * x + x ^ 2 * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨n + c + x * c, ?_⟩
    rw [pow_succ, hc]
    push_cast
    ring

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [T2Space K]

local notation "U" => nonarchimedeanLocalFieldPrincipalUnitFiltration K

omit [T2Space K] in
private theorem mem_U_iff {n : ℕ} {u : 𝒪[K]ˣ} :
    u ∈ U n ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n :=
  nonarchimedeanLocalField_mem_principalUnitFiltration_iff K n u

omit [T2Space K] in
private theorem principalUnitFiltration_separated (u : 𝒪[K]ˣ) (hu : ∀ j, u ∈ U j) : u = 1 := by
  apply Units.ext
  change (u : 𝒪[K]) = 1
  rw [← sub_eq_zero]
  by_contra h0
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨m, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  have h := (mem_maximalIdeal_pow_iff hπ).mp (mem_U_iff.mp (hu (m + 1)))
  rw [ha, pow_succ, mul_comm (a : 𝒪[K]),
    mul_dvd_mul_iff_left (pow_ne_zero m hπ.ne_zero)] at h
  exact hπ.not_isUnit (isUnit_of_dvd_unit h a.isUnit)

private theorem isClosed_principalUnitFiltration {π : 𝒪[K]} (hπ : Irreducible π) (j : ℕ) :
    IsClosed (U j : Set 𝒪[K]ˣ) := by
  let S := Set.range fun a : 𝒪[K] => π ^ j * a
  have hS : IsClosed S := (isCompact_range (continuous_const.mul continuous_id)).isClosed
  have h : (U j : Set 𝒪[K]ˣ) = (fun u : 𝒪[K]ˣ => (u : 𝒪[K]) - 1) ⁻¹' S := by
    ext u
    rw [SetLike.mem_coe, mem_U_iff, mem_maximalIdeal_pow_iff hπ]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  rw [h]
  exact hS.preimage (Units.continuous_val.sub continuous_const)

variable {π : 𝒪[K]} (hπ : Irreducible π) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = (ε : 𝒪[K]) * π ^ d)

include hπ hnd

omit hπ [TopologicalSpace K] [IsNonarchimedeanLocalField K] [T2Space K] in
private theorem power_of_uniformizer_displacement {j : ℕ} (hj : d + 1 ≤ j)
    (u : 𝒪[K]ˣ) (a : 𝒪[K]) (ha : (u : 𝒪[K]) - 1 = π ^ j * a) :
    ∃ c : 𝒪[K], ((u ^ n : 𝒪[K]ˣ) : 𝒪[K]) = 1 + π ^ (j + d) * ((ε : 𝒪[K]) * a + π * c) := by
  obtain ⟨c, hc⟩ := exists_power_displacement (π ^ j * a) n
  obtain ⟨k, rfl⟩ : ∃ k, j = d + 1 + k := ⟨j - (d + 1), by omega⟩
  refine ⟨π ^ k * a ^ 2 * c, ?_⟩
  rw [Units.val_pow_eq_pow_val, show (u : 𝒪[K]) = 1 + π ^ (d + 1 + k) * a by
    linear_combination ha, hc, hnd]
  simp only [pow_add, pow_one]
  ring

omit [T2Space K] in
private theorem map_power_le_principalUnitFiltration {j : ℕ} (hj : d + 1 ≤ j) :
    (U j).map (powMonoidHom n) ≤ U (j + d) := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hπ).mp (mem_U_iff.mp hu)
  obtain ⟨c, hc⟩ := power_of_uniformizer_displacement hnd hj u a ha
  rw [powMonoidHom_apply, mem_U_iff, hc, add_sub_cancel_left, mem_maximalIdeal_pow_iff hπ]
  exact dvd_mul_right _ _

omit [T2Space K] in
private theorem exists_power_lift_one_level {j : ℕ} (hj : d + 1 ≤ j) (h : 𝒪[K]ˣ)
    (hh : h ∈ U (j + d)) : ∃ g ∈ U j, h / (powMonoidHom n) g ∈ U (j + d + 1) := by
  obtain ⟨b, hb⟩ := (mem_maximalIdeal_pow_iff hπ).mp (mem_U_iff.mp hh)
  let a : 𝒪[K] := ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * b
  have hg := isUnit_one_add_uniformizer_pow hπ (show 1 ≤ j by omega) a
  have ha : (hg.unit : 𝒪[K]) - 1 = π ^ j * a := by rw [IsUnit.unit_spec, add_sub_cancel_left]
  refine ⟨hg.unit, mem_U_iff.mpr ((mem_maximalIdeal_pow_iff hπ).mpr ⟨a, ha⟩), ?_⟩
  obtain ⟨c, hc⟩ := power_of_uniformizer_displacement hnd hj hg.unit a ha
  rw [powMonoidHom_apply, div_eq_mul_inv, mul_comm h,
    nonarchimedeanLocalField_unit_div_mem_principalUnitFiltration_iff_sub_mem,
    mem_maximalIdeal_pow_iff hπ, pow_succ]
  refine ⟨-c, ?_⟩
  change ((hg.unit ^ n : 𝒪[K]ˣ) : 𝒪[K]) = _ at hc
  have hc' := hc
  dsimp only [a] at hc'
  simp only [Units.val_pow_eq_pow_val] at hc' ⊢
  linear_combination hb - hc' - π ^ (j + d) * b * (Units.mul_inv ε)

omit [T2Space K] in
private theorem deep_unit_eq_one_of_pow_eq_one {u : 𝒪[K]ˣ}
    (hu : u ∈ U (d + 1)) (hun : u ^ n = 1) : u = 1 := by
  classical
  by_contra hne
  have hex : ∃ j, u ∉ U j := by
    by_contra! hn
    exact hne (principalUnitFiltration_separated u hn)
  let m := Nat.find hex
  have hm : u ∉ U m := Nat.find_spec hex
  have hmin : ∀ j < m, u ∈ U j := fun j hj => by
    simpa using Nat.find_min hex hj
  have hdm : d + 1 < m := by
    by_contra h
    exact hm (nonarchimedeanLocalField_principalUnitFiltration_antitone K (not_lt.mp h) hu)
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hπ).mp (mem_U_iff.mp (hmin j (by omega)))
  have hna : ¬ π ∣ a := by
    rintro ⟨b, rfl⟩
    apply hm
    rw [hj, mem_U_iff, mem_maximalIdeal_pow_iff hπ, ha, pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)
  obtain ⟨c, hc⟩ := power_of_uniformizer_displacement hnd (show d + 1 ≤ j by omega) u a ha
  rw [hun, Units.val_one, left_eq_add, mul_eq_zero] at hc
  rcases hc with hc | hc
  · exact pow_ne_zero _ hπ.ne_zero hc
  · apply hna
    refine ⟨-((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c, ?_⟩
    linear_combination ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * hc - a * (Units.inv_mul ε)

theorem map_pow_principalUnitFiltration :
    (U (d + 1)).map (powMonoidHom n) = U (d + 1 + d) := by
  letI : CompactSpace 𝒪[K]ˣ := compactSpace_units_of_compact
  have hU := nonarchimedeanLocalField_principalUnitFiltration_antitone K
  refine map_eq_of_compact_filtration_lifts U U (powMonoidHom n)
    (continuous_id.pow n) (d + 1) d hU hU (isClosed_principalUnitFiltration hπ _).isCompact
    (isClosed_principalUnitFiltration hπ) principalUnitFiltration_separated
    (fun _ hj => map_power_le_principalUnitFiltration hπ hnd hj)
    (fun _ hj => exists_power_lift_one_level hπ hnd hj)

theorem index_range_pow_integralUnits_of_uniformizer
    : (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker * Nat.card 𝓀[K] ^ d := by
  let f := (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ)
  have hdisj : Disjoint (U (d + 1)) f.ker := by
    rw [Subgroup.disjoint_def]
    exact fun {_} hu hf => deep_unit_eq_one_of_pow_eq_one hπ hnd hu hf
  have hpos : 0 < (U (d + 1)).index := by
    rw [index_principalUnitFiltration (by omega)]
    have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  refine index_range_of_index_map f (U (d + 1)) hpos hdisj _ ?_
  rw [map_pow_principalUnitFiltration hπ hnd, index_principalUnitFiltration (by omega),
    index_principalUnitFiltration (by omega)]
  have hd : d + 1 + d - 1 = d + d := by omega
  rw [hd, Nat.add_sub_cancel, pow_add, mul_assoc]

end GlobalTheory.Reciprocity
