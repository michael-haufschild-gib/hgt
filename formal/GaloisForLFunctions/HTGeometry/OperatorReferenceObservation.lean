import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-! # Reconstruction from reference norm observations

Norm responses against zero, identity and imaginary identity recover every
complex linear operator. For norm-preserving maps only the last two are needed.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def operatorReferenceNorm (T : H →L[ℂ] H) (z : ℂ) (x : H) : ℝ := ‖T x - z • x‖

theorem operatorReferenceNorm_zero (T : H →L[ℂ] H) (x : H) :
    operatorReferenceNorm T 0 x = ‖T x‖ := by
  simp only [operatorReferenceNorm, zero_smul, sub_zero]

theorem operatorReferenceNorm_one_sq (T : H →L[ℂ] H) (x : H) :
    operatorReferenceNorm T 1 x ^ 2 =
      ‖T x‖ ^ 2 - 2 * (⟪T x, x⟫_ℂ).re + ‖x‖ ^ 2 := by
  simpa only [operatorReferenceNorm, one_smul, RCLike.re_eq_complex_re] using norm_sub_sq (𝕜 := ℂ) (T x) x

theorem operatorReferenceNorm_I_sq (T : H →L[ℂ] H) (x : H) :
    operatorReferenceNorm T Complex.I x ^ 2 =
      ‖T x‖ ^ 2 + 2 * (⟪T x, x⟫_ℂ).im + ‖x‖ ^ 2 := by
  simp only [operatorReferenceNorm, norm_sub_sq (𝕜 := ℂ), inner_smul_right, RCLike.re_eq_complex_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, mul_neg, sub_neg_eq_add, norm_smul, Complex.norm_I]

theorem operatorReferenceNorm_reconstruct_re (T : H →L[ℂ] H) (x : H) :
    (⟪T x, x⟫_ℂ).re =
      (‖T x‖ ^ 2 + ‖x‖ ^ 2 - operatorReferenceNorm T 1 x ^ 2) / 2 := by
  linarith only [operatorReferenceNorm_one_sq T x]

theorem operatorReferenceNorm_reconstruct_im (T : H →L[ℂ] H) (x : H) :
    (⟪T x, x⟫_ℂ).im =
      (operatorReferenceNorm T Complex.I x ^ 2 - ‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2 := by
  linarith only [operatorReferenceNorm_I_sq T x]

/-- Three complete norm profiles determine the actual operator. -/
theorem operatorReferenceNorm_eq_iff (T S : H →L[ℂ] H) :
    ((∀ x, ‖T x‖ = ‖S x‖) ∧
      (∀ x, operatorReferenceNorm T 1 x = operatorReferenceNorm S 1 x) ∧
      (∀ x, operatorReferenceNorm T Complex.I x = operatorReferenceNorm S Complex.I x)) ↔
      T = S := by
  constructor
  · rintro ⟨h0, h1, hi⟩
    apply ContinuousLinearMap.coe_injective
    apply (ext_inner_map T.toLinearMap S.toLinearMap).mp
    intro x
    apply Complex.ext
    · change (⟪T x, x⟫_ℂ).re = (⟪S x, x⟫_ℂ).re
      rw [operatorReferenceNorm_reconstruct_re, operatorReferenceNorm_reconstruct_re, h0, h1]
    · change (⟪T x, x⟫_ℂ).im = (⟪S x, x⟫_ℂ).im
      rw [operatorReferenceNorm_reconstruct_im, operatorReferenceNorm_reconstruct_im, h0, hi]
  · rintro rfl
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem operatorReferenceNorm_pair_eq_iff (T S : H →L[ℂ] H)
    (h : ∀ x, ‖T x‖ = ‖S x‖) :
    ((∀ x, operatorReferenceNorm T 1 x = operatorReferenceNorm S 1 x) ∧
      (∀ x, operatorReferenceNorm T Complex.I x = operatorReferenceNorm S Complex.I x)) ↔
      T = S := by
  constructor
  · exact fun hpair => (operatorReferenceNorm_eq_iff T S).mp ⟨h, hpair⟩
  · rintro rfl
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem operatorReferenceNorm_unitary_eq_iff [CompleteSpace H]
    (T S : unitary (H →L[ℂ] H)) :
    ((∀ x, operatorReferenceNorm T.val 1 x = operatorReferenceNorm S.val 1 x) ∧
      (∀ x, operatorReferenceNorm T.val Complex.I x =
        operatorReferenceNorm S.val Complex.I x)) ↔ T = S := by
  rw [← Subtype.val_inj]
  exact operatorReferenceNorm_pair_eq_iff T.val S.val
    (fun x => (ContinuousLinearMap.norm_map_of_mem_unitary T.property x).trans
      (ContinuousLinearMap.norm_map_of_mem_unitary S.property x).symm)

/-- The comparison budget is independent of the chosen complex reference. -/
theorem operatorReferenceNorm_difference_le (T S : H →L[ℂ] H) (z : ℂ) (x : H) :
    |operatorReferenceNorm T z x - operatorReferenceNorm S z x| ≤ ‖T - S‖ * ‖x‖ := by
  calc
    _ ≤ ‖(T x - z • x) - (S x - z • x)‖ := abs_norm_sub_norm_le _ _
    _ = ‖(T - S) x‖ := by congr 1; simp only [sub_apply]; abel
    _ ≤ _ := (T - S).le_opNorm x

end
end GaloisForLFunctions.HTGeometry
