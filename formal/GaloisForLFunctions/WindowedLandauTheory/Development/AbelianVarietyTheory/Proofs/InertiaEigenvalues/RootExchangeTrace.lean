import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

/-! Weighted traces on two subgroups agree when their weights coincide on
the intersection and nonintertwining conjugations cancel the other cosets. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
private theorem class_mul_comm {φ : G → ℂ} (hφ : IsClass φ) (x y : G) :
    φ (x * y) = φ (y * x) := by
  rw [← hφ (y * x) x]
  congr 1
  group

private theorem weighted_sum_mul_mem (K : Subgroup G) (χK : K →* ℂˣ) (φ : G → ℂ) (b : K) :
    ∑ a : K, ((χK a⁻¹ : ℂˣ) : ℂ) * φ (a.val * b.val) =
      (χK b : ℂ) * ∑ a : K, ((χK a⁻¹ : ℂˣ) : ℂ) * φ a.val := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.coe_mulRight, mul_inv_rev, inv_inv, map_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, inv_mul_cancel, mul_one, Units.val_mul, mul_assoc]

private theorem weighted_sum_eq_zero (K : Subgroup G) (χK : K →* ℂˣ)
    {φ : G → ℂ} (hφ : IsClass φ) (b : G)
    (x y : K) (hy : y.val = b⁻¹ * x.val * b) (hweight : χK y ≠ χK x) :
    ∑ a : K, ((χK a⁻¹ : ℂˣ) : ℂ) * φ (a.val * b) = 0 := by
  let F (a : K) := ((χK a⁻¹ : ℂˣ) : ℂ) * φ (a.val * b)
  let c : ℂˣ := χK y * (χK x)⁻¹
  have hc : (c : ℂ) ≠ 1 := fun h => hweight (mul_inv_eq_one.mp (Units.val_eq_one.mp h))
  let e : K ≃ K := (Equiv.mulRight x).trans (Equiv.mulLeft y⁻¹)
  have hF (a : K) : F (e a) = (c : ℂ) * F a := by
    have ha : φ ((y⁻¹ * (a * x) : K).val * b) = φ (a.val * b) := by
      rw [← hφ (a.val * b) y.val⁻¹]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hy]
      group
    change ((χK (y⁻¹ * (a * x))⁻¹ : ℂˣ) : ℂ) *
      φ ((y⁻¹ * (a * x) : K).val * b) = (c : ℂ) * F a
    rw [ha]
    simp only [c, F, mul_inv_rev, inv_inv, map_mul, map_inv, Units.val_mul]
    ring
  have he : (∑ a : K, F a) = (c : ℂ) * ∑ a : K, F a :=
    (Equiv.sum_comp e F).symm.trans (by simp only [hF, Finset.mul_sum])
  have hz : (1 - (c : ℂ)) * ∑ a : K, F a = 0 := by
    rw [sub_mul, one_mul, ← he, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc.symm)

private theorem weighted_double_sum (H K : Subgroup G) (χH : H →* ℂˣ) (χK : K →* ℂˣ)
    (hagree : ∀ (a : H) (b : K), a.val = b.val → χH a = χK b)
    (hcancel : ∀ b : K, b.val ∉ H → ∃ x y : H,
      y.val = b.val⁻¹ * x.val * b.val ∧ χH y ≠ χH x)
    {φ : G → ℂ} (hφ : IsClass φ) :
    ∑ b : K, ∑ a : H, ((χK b⁻¹ : ℂˣ) : ℂ) *
        (((χH a⁻¹ : ℂˣ) : ℂ) * φ (a.val * b.val)) =
      (∑ b : K, if b.val ∈ H then (1 : ℂ) else 0) *
        ∑ a : H, ((χH a⁻¹ : ℂˣ) : ℂ) * φ a.val := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  split_ifs with hb
  · let a : H := ⟨b.val, hb⟩
    change ((χK b⁻¹ : ℂˣ) : ℂ) * (∑ x : H, ((χH x⁻¹ : ℂˣ) : ℂ) *
      φ (x.val * a.val)) = _
    rw [weighted_sum_mul_mem H χH φ a, hagree a b rfl, ← mul_assoc,
      map_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · obtain ⟨x, y, hy, hweight⟩ := hcancel b hb
    rw [weighted_sum_eq_zero H χH hφ b.val x y hy hweight, mul_zero, zero_mul]

private theorem subgroup_intersection_weight (H K : Subgroup G) :
    (∑ b : K, if b.val ∈ H then (1 : ℂ) else 0) =
      (Nat.card (H ⊓ K : Subgroup G) : ℂ) := by
  let S := Finset.univ.filter (fun b : K => b.val ∈ H)
  let e : {b : K // b.val ∈ H} ≃ (H ⊓ K : Subgroup G) :=
    { toFun := fun b => ⟨b.val.val, b.property, b.val.property⟩
      invFun := fun b => ⟨⟨b.val, b.property.2⟩, b.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : S.card = Nat.card (H ⊓ K : Subgroup G) := by
    rw [Nat.card_congr e.symm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_boole]
  exact congrArg (fun n : ℕ => (n : ℂ)) hcard

/-- Equal-size subgroup averages agree when their weights agree on the
intersection and each off-intersection coset has a character mismatch. -/
theorem weighted_trace_eq_of_exchange
    (H K : Subgroup G) (χH : H →* ℂˣ) (χK : K →* ℂˣ)
    (hcard : Nat.card H = Nat.card K)
    (hagree : ∀ (a : H) (b : K), a.val = b.val → χH a = χK b)
    (hK : ∀ b : K, b.val ∉ H → ∃ x y : H,
      y.val = b.val⁻¹ * x.val * b.val ∧ χH y ≠ χH x)
    (hH : ∀ a : H, a.val ∉ K → ∃ x y : K,
      y.val = a.val⁻¹ * x.val * a.val ∧ χK y ≠ χK x)
    {φ : G → ℂ} (hφ : IsClass φ) :
    (Nat.card H : ℂ)⁻¹ * (∑ a : H, ((χH a⁻¹ : ℂˣ) : ℂ) * φ a.val) =
      (Nat.card K : ℂ)⁻¹ * (∑ b : K, ((χK b⁻¹ : ℂˣ) : ℂ) * φ b.val) := by
  have hh := weighted_double_sum H K χH χK hagree hK hφ
  have hk := weighted_double_sum K H χK χH (fun b a he => (hagree a b he.symm).symm) hH hφ
  rw [subgroup_intersection_weight H K] at hh
  rw [subgroup_intersection_weight K H, inf_comm K H, Finset.sum_comm] at hk
  rw [hcard]
  congr 1
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := (H ⊓ K : Subgroup G))).ne')
  rw [← hh, ← hk]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [class_mul_comm hφ a.val b.val]
  ring

end GlobalTheory.GLq
