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

section Equivariance

variable {π : 𝒪[K]} (hπ : Irreducible π)

private def powIntoPrincipalUnits [Finite 𝓀[K]] : 𝒪[K]ˣ →* U 1 :=
  (powMonoidHom (Nat.card 𝓀[K] - 1)).codRestrict _ fun u => by
    rw [nonarchimedeanLocalField_principalUnitFiltration_one]
    apply MonoidHom.mem_ker.mpr
    change nonarchimedeanLocalFieldReductionUnits K (u ^ (Nat.card 𝓀[K] - 1)) = 1
    rw [map_pow]
    apply Units.ext
    letI : Fintype 𝓀[K] := Fintype.ofFinite _
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)

/-- Raising a unit to the order of the residue multiplicative group
puts it into the first principal layer. The residue coefficient of
that power gives an additive quotient of all integral units. -/
def firstPrincipalUnitCoefficient [Finite 𝓀[K]] : 𝒪[K]ˣ →* Multiplicative 𝓀[K] :=
  (gradedUnitMap hπ (n := 1) le_rfl).comp powIntoPrincipalUnits

theorem firstPrincipalUnitCoefficient_surjective [Finite 𝓀[K]] :
    Function.Surjective (firstPrincipalUnitCoefficient hπ) := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  let g := gradedUnitMap hπ (n := 1) le_rfl
  intro r
  obtain ⟨u, hu⟩ := gradedUnitMap_surjective hπ le_rfl r⁻¹
  refine ⟨u.val, ?_⟩
  change g (u ^ (Nat.card 𝓀[K] - 1)) = r
  rw [map_pow, hu]
  apply Multiplicative.toAdd.injective
  change (Nat.card 𝓀[K] - 1) • (-Multiplicative.toAdd r) = Multiplicative.toAdd r
  have hq : ((Nat.card 𝓀[K] : ℕ) : 𝓀[K]) = 0 := by
    rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
  rw [nsmul_eq_mul, Nat.cast_sub (Nat.card_pos (α := 𝓀[K])), hq, Nat.cast_one,
    zero_sub, neg_mul_neg, one_mul]

theorem firstPrincipalUnitCoefficient_map [Finite 𝓀[K]]
    (e : 𝒪[K] ≃+* 𝒪[K]) (he : e π = π) (u : 𝒪[K]ˣ) :
    firstPrincipalUnitCoefficient hπ (Units.map e.toMonoidHom u) =
      Multiplicative.ofAdd (ResidueField.mapEquiv e
        (Multiplicative.toAdd (firstPrincipalUnitCoefficient hπ u))) := by
  let g := powIntoPrincipalUnits (K := K)
  let z := g (Units.map e.toMonoidHom u)
  let y := g u
  have hz : (((z.val : 𝒪[K]ˣ) : 𝒪[K])) = e (y.val : 𝒪[K]) := by
    change ((Units.map e.toMonoidHom u : 𝒪[K]ˣ) : 𝒪[K]) ^ (Nat.card 𝓀[K] - 1) =
      e ((u : 𝒪[K]) ^ (Nat.card 𝓀[K] - 1))
    rw [Units.coe_map, map_pow]
    rfl
  have heq : ((z.val : 𝒪[K]ˣ) : 𝒪[K]) - 1 = π ^ 1 * e (uniformizerCoefficient hπ y) := by
    rw [hz, ← map_one e, ← map_sub, sub_one_eq_uniformizerCoefficient hπ y,
      map_mul, map_pow, he]
  change Multiplicative.ofAdd (residue 𝒪[K] (uniformizerCoefficient hπ z)) = _
  rw [uniformizerCoefficient_eq hπ heq]
  rfl

theorem firstPrincipalUnitCoefficient_eq_one_of_mem_level_two [Finite 𝓀[K]]
    (u : 𝒪[K]ˣ) (hu : u ∈ U 2) : firstPrincipalUnitCoefficient hπ u = 1 := by
  apply MonoidHom.mem_ker.mp
  change powIntoPrincipalUnits u ∈ (gradedUnitMap hπ (n := 1) le_rfl).ker
  rw [ker_gradedUnitMap, Subgroup.mem_subgroupOf]
  exact (U 2).pow_mem hu _

end Equivariance

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

#print axioms GlobalTheory.Reciprocity.firstPrincipalUnitCoefficient_surjective
#print axioms GlobalTheory.Reciprocity.firstPrincipalUnitCoefficient_map
