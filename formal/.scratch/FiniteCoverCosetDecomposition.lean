import GaloisForLFunctions.RHTower.MaassRationalHeckeIntegralCoverL2

namespace GaloisForLFunctions.RHTower

open Subgroup

noncomputable section

/-- Every element of an ambient subgroup has a left decomposition by an element
of the smaller subgroup and the inverse of a chosen right-coset representative. -/
theorem subgroup_exists_left_coset_decomposition
    {G : Type*} [Group G] (K Γ : Subgroup G) (hKΓ : K ≤ Γ) (a : Γ) :
    ∃ k : K, ∃ q : Γ ⧸ K.subgroupOf Γ,
      a = Subgroup.inclusion hKΓ k * q.out⁻¹ := by
  let q : Γ ⧸ K.subgroupOf Γ := QuotientGroup.mk a⁻¹
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf Γ) a⁻¹
  refine ⟨⟨k.val, k.property⟩, q, ?_⟩
  change a = k.val * q.out⁻¹
  rw [hk]
  group

/-- Distinct chosen right cosets cannot occur in equal left decompositions. -/
theorem subgroup_rightCoset_eq_of_left_decomposition
    {G : Type*} [Group G] (K Γ : Subgroup G) (hKΓ : K ≤ Γ)
    (k₁ k₂ : K) (q₁ q₂ : Γ ⧸ K.subgroupOf Γ)
    (h : Subgroup.inclusion hKΓ k₁ * q₁.out⁻¹ =
      Subgroup.inclusion hKΓ k₂ * q₂.out⁻¹) :
    q₁ = q₂ := by
  rw [← q₁.out_eq', ← q₂.out_eq']
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  have hEq : q₁.out⁻¹ * q₂.out = Subgroup.inclusion hKΓ (k₁⁻¹ * k₂) := by
    calc
      q₁.out⁻¹ * q₂.out = (Subgroup.inclusion hKΓ k₁)⁻¹ *
          ((Subgroup.inclusion hKΓ k₁ * q₁.out⁻¹) * q₂.out) := by group
      _ = (Subgroup.inclusion hKΓ k₁)⁻¹ *
          ((Subgroup.inclusion hKΓ k₂ * q₂.out⁻¹) * q₂.out) := by rw [h]
      _ = Subgroup.inclusion hKΓ (k₁⁻¹ * k₂) := by simp
  rw [hEq]
  exact (k₁⁻¹ * k₂).property

end

end GaloisForLFunctions.RHTower
