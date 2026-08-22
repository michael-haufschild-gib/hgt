import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinGradientDescent
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinResolventExpansion

/-!
# The single-index Wasserstein fields

The cyclic (incremental) schemes split the Wasserstein field into the `m` pieces

`Ψ_i(X) = m w_i (1 - A_i # X⁻¹)`,   `∑_i Ψ_i = m Φ`.

Each `Ψ_i` is Hilbert–Schmidt valued on `1 + S²` and Lipschitz there with the same constant as
the full field, because `1 - A_i # X⁻¹ = A_i # A_i⁻¹ - A_i # X⁻¹` is a difference of geometric
means with a common first argument.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

omit [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
/-- The Hilbert–Schmidt norm is invariant under negation. -/
lemma hsNorm_neg' (T : E →L[ℂ] E) : hsNorm (-T) = hsNorm T := by
  have h := hsNorm_real_smul (-1 : ℝ) T
  rw [neg_one_smul] at h
  rw [h]
  norm_num

/-- The **single-index Wasserstein field** `Ψ_i(X) = m w_i (1 - A_i # X⁻¹)`. -/
noncomputable def wassPsi (m : ℝ) (w : ι → ℝ) (Av : ι → E →L[ℂ] E) (i : ι) (X : E →L[ℂ] E) :
    E →L[ℂ] E :=
  (m * w i) • ((1 : E →L[ℂ] E) - gm (Av i) X⁻¹ʳ)

/-- The single-index fields add up to `m` times the Wasserstein field. -/
lemma sum_wassPsi {X : E →L[ℂ] E} (m : ℝ) (hX : IsStrictlyPositive X) :
    ∑ i ∈ s, wassPsi m w Av i X = m • wassField s w Av X := by
  unfold wassPsi wassField
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [gmInvMap_eq_gm hX, smul_smul]

/-- The Hilbert–Schmidt Lipschitz bound for the geometric mean in its second argument. -/
theorem hsNorm_gm_sub_gm_le {X Y₁ Y₂ : E →L[ℂ] E} (hX : IsStrictlyPositive X)
    (hY₁ : IsStrictlyPositive Y₁) (hY₂ : IsStrictlyPositive Y₂)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hY₁α : α • (1 : E →L[ℂ] E) ≤ Y₁) (hY₁β : Y₁ ≤ β • (1 : E →L[ℂ] E))
    (hY₂α : α • (1 : E →L[ℂ] E) ≤ Y₂) (hY₂β : Y₂ ≤ β • (1 : E →L[ℂ] E))
    (hHS : IsHilbertSchmidt (Y₁ - Y₂)) :
    hsNorm (gm X Y₁⁻¹ʳ - gm X Y₂⁻¹ʳ) ≤ gmFieldLipConst α β * hsNorm (Y₁ - Y₂) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  have hgb : (Real.sqrt (α * β⁻¹)) • (1 : E →L[ℂ] E) ≤ gm X Y₁⁻¹ʳ :=
    smul_one_le_gm hX hY₁.ringInverse hα hβinv hXα
      (smul_one_le_ringInverse_of_le_smul_one hY₁ hβ hY₁β)
  have hgc : (Real.sqrt (α * β⁻¹)) • (1 : E →L[ℂ] E) ≤ gm X Y₂⁻¹ʳ :=
    smul_one_le_gm hX hY₂.ringInverse hα hβinv hXα
      (smul_one_le_ringInverse_of_le_smul_one hY₂ hβ hY₂β)
  have hinvHS : IsHilbertSchmidt ((Y₁⁻¹ʳ : E →L[ℂ] E) - Y₂⁻¹ʳ) :=
    isHilbertSchmidt_ringInverse_sub hY₁ hY₂
      (by rw [show Y₂ - Y₁ = -(Y₁ - Y₂) by abel_nf]; exact hHS.neg)
  have hgmi := hsNorm_gm_sub_le_of_Icc hX hY₁.ringInverse hY₂.ringInverse hα hγ hβ
    hXα hXβ hgb hgc hinvHS
  have hinvn : hsNorm ((Y₁⁻¹ʳ : E →L[ℂ] E) - Y₂⁻¹ʳ) ≤ (α⁻¹ * α⁻¹) * hsNorm (Y₁ - Y₂) := by
    have h := hsNorm_ringInverse_sub_le_of_Icc hY₂ hY₁ hα hY₂α hY₁α
      (by
        have hid : Y₂ - Y₁ = -(Y₁ - Y₂) := by abel_nf
        rw [hid]; exact hHS.neg)
    have hid2 : hsNorm (Y₂ - Y₁) = hsNorm (Y₁ - Y₂) := by
      rw [show Y₂ - Y₁ = -(Y₁ - Y₂) by abel_nf, hsNorm_neg']
    rwa [hid2] at h
  have hstep : (2 * (Real.sqrt (α * β⁻¹) * β⁻¹)) * hsNorm (gm X Y₁⁻¹ʳ - gm X Y₂⁻¹ʳ)
      ≤ (β * α⁻¹) * ((α⁻¹ * α⁻¹) * hsNorm (Y₁ - Y₂)) :=
    hgmi.trans (mul_le_mul_of_nonneg_left hinvn (by positivity))
  rw [← le_div_iff₀' (by positivity : (0:ℝ) < 2 * (Real.sqrt (α * β⁻¹) * β⁻¹))] at hstep
  refine hstep.trans (le_of_eq ?_)
  unfold gmFieldLipConst
  field_simp

/-- The increment of a single-index field is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_wassPsi_sub {X Y : E →L[ℂ] E} {m : ℝ} {i : ι} (hi : i ∈ s)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ j ∈ s, IsStrictlyPositive (Av j))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ j ∈ s, α • (1 : E →L[ℂ] E) ≤ Av j)
    (hAβ : ∀ j ∈ s, Av j ≤ β • (1 : E →L[ℂ] E))
    (hXβ : X ≤ β • (1 : E →L[ℂ] E)) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hHS : IsHilbertSchmidt (X - Y)) :
    IsHilbertSchmidt (wassPsi m w Av i X - wassPsi m w Av i Y) := by
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  have hid : wassPsi m w Av i X - wassPsi m w Av i Y
      = (m * w i) • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ) := by
    unfold wassPsi
    rw [← smul_sub]
    congr 1
    abel
  rw [hid]
  refine IsHilbertSchmidt.real_smul ?_ _
  refine isHilbertSchmidt_gm_sub (hA i hi) hY.ringInverse hX.ringInverse hγ hβ (hAβ i hi)
    (smul_one_le_gm (hA i hi) hY.ringInverse hα hβinv (hAα i hi)
      (smul_one_le_ringInverse_of_le_smul_one hY hβ hYβ))
    (smul_one_le_gm (hA i hi) hX.ringInverse hα hβinv (hAα i hi)
      (smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ))
    (isHilbertSchmidt_ringInverse_sub hY hX hHS)

/-- Each single-index field is Lipschitz in the Hilbert–Schmidt norm. -/
theorem hsNorm_wassPsi_sub_le {X Y : E →L[ℂ] E} {m : ℝ} {i : ι} (hi : i ∈ s)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hA : ∀ j ∈ s, IsStrictlyPositive (Av j))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ j ∈ s, α • (1 : E →L[ℂ] E) ≤ Av j)
    (hAβ : ∀ j ∈ s, Av j ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hHS : IsHilbertSchmidt (X - Y)) :
    hsNorm (wassPsi m w Av i X - wassPsi m w Av i Y)
      ≤ (|m * w i| * gmFieldLipConst α β) * hsNorm (X - Y) := by
  have hid : wassPsi m w Av i X - wassPsi m w Av i Y
      = (m * w i) • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ) := by
    unfold wassPsi
    rw [← smul_sub]
    congr 1
    abel
  rw [hid, hsNorm_real_smul]
  have hgm := hsNorm_gm_sub_gm_le (hA i hi) hY hX hα hαβ (hAα i hi) (hAβ i hi)
    hYα hYβ hXα hXβ (by
      have hid2 : Y - X = -(X - Y) := by abel_nf
      rw [hid2]; exact hHS.neg)
  have hsym : hsNorm (Y - X) = hsNorm (X - Y) := by
    rw [show Y - X = -(X - Y) by abel_nf, hsNorm_neg']
  rw [hsym] at hgm
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hgm (abs_nonneg _)

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
