import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import Mathlib.GroupTheory.Index

/-! At positive depth, successive principal unit quotients are the
additive residue field via the leading uniformizer coefficient. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.ABHN IsLocalRing
open scoped ValuativeRel

namespace GlobalTheory.Reciprocity

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local notation "U" => nonarchimedeanLocalFieldPrincipalUnitFiltration K

private theorem mem_principalUnitFiltration {n : ℕ} {u : 𝒪[K]ˣ} :
    u ∈ U n ↔ (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n :=
  nonarchimedeanLocalField_mem_principalUnitFiltration_iff K n u

theorem mem_maximalIdeal_pow_iff {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x : 𝒪[K]} :
    x ∈ 𝓂[K] ^ n ↔ π ^ n ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem isUnit_one_add_uniformizer_pow {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ}
    (hn : 1 ≤ n) (a : 𝒪[K]) : IsUnit (1 + π ^ n * a) := by
  have hπm : π ∈ 𝓂[K] := by rw [hπ.maximalIdeal_eq]; exact Ideal.subset_span (Set.mem_singleton _)
  have hm : π ^ n * a ∈ 𝓂[K] :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπm n (by omega))
  simpa using isUnit_one_sub_self_of_mem_nonunits (-(π ^ n * a))
    ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hm))

section Graded

variable {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ}
include hπ

private theorem exists_uniformizerCoefficient (u : U n) :
    ∃ a : 𝒪[K], ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = π ^ n * a :=
  (mem_maximalIdeal_pow_iff hπ).mp (mem_principalUnitFiltration.mp u.2)

private def uniformizerCoefficient (u : U n) : 𝒪[K] :=
  (exists_uniformizerCoefficient hπ u).choose

private theorem sub_one_eq_uniformizerCoefficient (u : U n) :
    ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = π ^ n * uniformizerCoefficient hπ u :=
  (exists_uniformizerCoefficient hπ u).choose_spec

private theorem uniformizerCoefficient_eq {u : U n} {a : 𝒪[K]}
    (h : ((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 = π ^ n * a) :
    uniformizerCoefficient hπ u = a :=
  mul_left_cancel₀ (pow_ne_zero n hπ.ne_zero) ((sub_one_eq_uniformizerCoefficient hπ u).symm.trans h)

private def gradedUnitMap (hn : 1 ≤ n) : U n →* Multiplicative 𝓀[K] where
  toFun u := Multiplicative.ofAdd (residue 𝒪[K] (uniformizerCoefficient hπ u))
  map_one' := by
    rw [uniformizerCoefficient_eq hπ (a := 0) (by simp)]
    simp
  map_mul' u v := by
    have hu := sub_one_eq_uniformizerCoefficient hπ u
    have hv := sub_one_eq_uniformizerCoefficient hπ v
    have h := uniformizerCoefficient_eq hπ (u := u * v)
      (a := uniformizerCoefficient hπ u + uniformizerCoefficient hπ v +
        π ^ n * (uniformizerCoefficient hπ u * uniformizerCoefficient hπ v)) (by
      simp only [Subgroup.coe_mul, Units.val_mul]
      linear_combination ((v : 𝒪[K]ˣ) : 𝒪[K]) * hu + (1 + π ^ n * uniformizerCoefficient hπ u) * hv)
    have hz : residue 𝒪[K] π = 0 := by
      rw [residue_eq_zero_iff, hπ.maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton _)
    change Multiplicative.ofAdd (residue 𝒪[K] (uniformizerCoefficient hπ (u * v))) = _
    rw [h]
    apply congrArg Multiplicative.ofAdd
    change residue 𝒪[K] _ = residue 𝒪[K] (uniformizerCoefficient hπ u) +
      residue 𝒪[K] (uniformizerCoefficient hπ v)
    simp [hz, zero_pow (by omega : n ≠ 0)]

private theorem ker_gradedUnitMap (hn : 1 ≤ n) :
    (gradedUnitMap hπ hn).ker = (U (n + 1)).subgroupOf (U n) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_principalUnitFiltration,
    mem_maximalIdeal_pow_iff hπ, sub_one_eq_uniformizerCoefficient hπ u, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero n hπ.ne_zero), ← Ideal.mem_span_singleton,
    ← hπ.maximalIdeal_eq, ← residue_eq_zero_iff]
  exact Iff.rfl

private theorem gradedUnitMap_surjective (hn : 1 ≤ n) :
    Function.Surjective (gradedUnitMap hπ hn) := by
  intro r
  obtain ⟨a, ha⟩ := residue_surjective (Multiplicative.toAdd r)
  have hu := isUnit_one_add_uniformizer_pow hπ hn a
  have hu' : hu.unit ∈ U n := by
    rw [mem_principalUnitFiltration, IsUnit.unit_spec, add_sub_cancel_left,
      mem_maximalIdeal_pow_iff hπ]
    exact dvd_mul_right _ _
  refine ⟨⟨hu.unit, hu'⟩, ?_⟩
  change Multiplicative.ofAdd (residue 𝒪[K] (uniformizerCoefficient hπ ⟨hu.unit, hu'⟩)) = r
  rw [uniformizerCoefficient_eq hπ (a := a) (by simp [IsUnit.unit_spec]), ha]
  rfl

theorem relIndex_principalUnitFiltration_succ (hn : 1 ≤ n) :
    (U (n + 1)).relIndex (U n) = Nat.card 𝓀[K] := by
  rw [Subgroup.relIndex, ← ker_gradedUnitMap hπ hn, Subgroup.index]
  exact Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective _ (gradedUnitMap_surjective hπ hn)).toEquiv

end Graded

theorem index_principalUnitFiltration {n : ℕ} (hn : 1 ≤ n) :
    (U n).index = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n - 1) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, pow_zero, mul_one, nonarchimedeanLocalField_principalUnitFiltration_one,
      Subgroup.index]
    exact (Nat.card_congr (nonarchimedeanLocalFieldUnitsModPrincipalUnitsEquivResidueUnits K).toEquiv).trans
      (Nat.card_units 𝓀[K])
  | succ n hn ih =>
    rw [← Subgroup.relIndex_mul_index
      (nonarchimedeanLocalField_principalUnitFiltration_antitone K (Nat.le_succ n)),
      relIndex_principalUnitFiltration_succ hπ hn, ih, Nat.succ_sub_one]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ac_rfl

end GlobalTheory.Reciprocity
