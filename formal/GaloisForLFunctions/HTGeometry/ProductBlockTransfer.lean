import GaloisForLFunctions.HTGeometry.ProductEigenframeMatching

/-!
# Transfer of a row block between two product frames

The eigenspace of a row block is the set of tensors with a prescribed left factor.  A nonzero
decomposable tensor lying in it has its left factor on that same line, by rigidity.  Consequently
two vectors of a second product frame that both lie in the eigenspace share their left index, so a
row block of one grid is a row block of the other with the same left line.

The same statements hold with the two sides exchanged, for column blocks.

This is the `2 + 2` row-split and column-split case of the multiplicity classification, argued
entirely with decomposable tensors: no spectral projector and no operator tensor product is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {K : Type*} [Field K] {I J : Type*}

/-! ### Membership in a row eigenspace -/

/-- A nonzero decomposable tensor with a prescribed left factor has its own left factor on that
line. -/
theorem left_line_of_segreTensor_eq {a a' : I → K} {b' w : J → K}
    (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (h : criticalHorizonSegreTensor a' b' = criticalHorizonSegreTensor a w) :
    ∃ α : K, α ≠ 0 ∧ a' = α • a := by
  have h' : criticalHorizonSegreTensor a' b' = (1 : K) • criticalHorizonSegreTensor a w := by
    rw [one_smul]
    exact h
  exact criticalHorizonSegreTensor_left_line ha' hb' h'

/-- A nonzero decomposable tensor with a prescribed right factor has its own right factor on that
line. -/
theorem right_line_of_segreTensor_eq {a' v : I → K} {b b' : J → K}
    (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (h : criticalHorizonSegreTensor a' b' = criticalHorizonSegreTensor v b) :
    ∃ β : K, β ≠ 0 ∧ b' = β • b := by
  have h' : criticalHorizonSegreTensor a' b' = (1 : K) • criticalHorizonSegreTensor v b := by
    rw [one_smul]
    exact h
  exact criticalHorizonSegreTensor_right_line ha' hb' h'

/-! ### The block transfers -/

/-- **Row-block transfer.**  Two vectors of a second product frame lying in the row eigenspace of
`a i₀` share their left index: both left factors are on the line of `a i₀`, and the frame's left
vectors are linearly independent. -/
theorem rowBlock_left_index_eq [DecidableEq I] {a a' : I → (I → K)} {b' : J → (J → K)}
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, a' i ≠ 0) (hb' : ∀ j, b' j ≠ 0)
    (hindep : LinearIndependent K a') {i₀ : I} {k₁ k₂ : I} {l₁ l₂ : J} {w₁ w₂ : J → K}
    (h₁ : criticalHorizonSegreTensor (a' k₁) (b' l₁) =
      criticalHorizonSegreTensor (a i₀) w₁)
    (h₂ : criticalHorizonSegreTensor (a' k₂) (b' l₂) =
      criticalHorizonSegreTensor (a i₀) w₂) :
    k₁ = k₂ := by
  obtain ⟨α₁, hα₁, hk₁⟩ := left_line_of_segreTensor_eq (ha' k₁) (hb' l₁) h₁
  obtain ⟨α₂, hα₂, hk₂⟩ := left_line_of_segreTensor_eq (ha' k₂) (hb' l₂) h₂
  have e₁ : a i₀ = α₁⁻¹ • a' k₁ := by
    rw [hk₁, smul_smul, inv_mul_cancel₀ hα₁, one_smul]
  have e₂ : a i₀ = α₂⁻¹ • a' k₂ := by
    rw [hk₂, smul_smul, inv_mul_cancel₀ hα₂, one_smul]
  exact eq_of_eq_smul_of_linearIndependent hindep (ha i₀) e₁ e₂

/-- **Column-block transfer.** -/
theorem columnBlock_right_index_eq [DecidableEq J] {a' : I → (I → K)} {b b' : J → (J → K)}
    (hb : ∀ j, b j ≠ 0) (ha' : ∀ i, a' i ≠ 0) (hb' : ∀ j, b' j ≠ 0)
    (hindep : LinearIndependent K b') {j₀ : J} {k₁ k₂ : I} {l₁ l₂ : J} {v₁ v₂ : I → K}
    (h₁ : criticalHorizonSegreTensor (a' k₁) (b' l₁) =
      criticalHorizonSegreTensor v₁ (b j₀))
    (h₂ : criticalHorizonSegreTensor (a' k₂) (b' l₂) =
      criticalHorizonSegreTensor v₂ (b j₀)) :
    l₁ = l₂ := by
  obtain ⟨β₁, hβ₁, hl₁⟩ := right_line_of_segreTensor_eq (ha' k₁) (hb' l₁) h₁
  obtain ⟨β₂, hβ₂, hl₂⟩ := right_line_of_segreTensor_eq (ha' k₂) (hb' l₂) h₂
  have e₁ : b j₀ = β₁⁻¹ • b' l₁ := by
    rw [hl₁, smul_smul, inv_mul_cancel₀ hβ₁, one_smul]
  have e₂ : b j₀ = β₂⁻¹ • b' l₂ := by
    rw [hl₂, smul_smul, inv_mul_cancel₀ hβ₂, one_smul]
  exact eq_of_eq_smul_of_linearIndependent hindep (hb j₀) e₁ e₂

end GaloisForLFunctions.HTGeometry
