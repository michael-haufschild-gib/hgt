import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-! # Energy weight detected by almost orthogonal translates of a marked sector -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
noncomputable section
variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

/-- Almost orthogonal operator columns have a Gram sum bounded by their
largest absolute row sum times the number of columns. -/
theorem translate_gram (B : I → A) {δ : ℝ}
    (hd : ∀ i, ‖star (B i)*B i‖≤1) (ho : ∀ i j, i≠j → ‖star (B i)*B j‖≤δ) :
    ‖∑ i, B i‖^2 ≤ (Fintype.card I:ℝ)*(1+((Fintype.card I-1:ℕ):ℝ)*δ) := by
  classical
  have hr (i : I) : ∑ j, ‖star (B i)*B j‖ ≤ 1+((Fintype.card I-1:ℕ):ℝ)*δ := by
    rw [←sum_erase_add _ _ (mem_univ i),add_comm]
    apply add_le_add (hd i)
    have h := sum_le_sum (s:=univ.erase i) fun j hj => ho i j (ne_of_mem_erase hj).symm
    simpa only [sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ i),card_univ] using h
  rw [pow_two,←CStarRing.norm_star_mul_self,star_sum,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  calc _ ≤ ∑ i : I, ∑ j, ‖star (B i)*B j‖ := by
         apply sum_le_sum
         intro i _
         rw [mul_sum]
         exact norm_sum_le _ _
       _ ≤ _ := (sum_le_sum (s:=univ) fun i _ => hr i).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])

/-- If a spectral row agrees on all phase-corrected translates, its
squared mass on their common initial sector is at most the Gram row
bound divided by the number of dates. -/
theorem spectral_weight_from_translates [Nonempty I] (B : I → A) (Q P : A) {δ : ℝ}
    (hQ : ‖Q‖≤1) (he : ∀ i, Q*B i=Q*P) (hd : ∀ i, ‖star (B i)*B i‖≤1)
    (ho : ∀ i j, i≠j → ‖star (B i)*B j‖≤δ) :
    (Fintype.card I:ℝ)*‖Q*P‖^2 ≤ 1+((Fintype.card I-1:ℕ):ℝ)*δ := by
  have hN : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos (α:=I)
  have hx : (Fintype.card I:ℝ)*‖Q*P‖ ≤ ‖∑ i, B i‖ := by
    have h := (norm_mul_le Q (∑ i, B i)).trans (mul_le_of_le_one_left (norm_nonneg _) hQ)
    rw [mul_sum] at h
    simpa only [he,sum_const,card_univ,←Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hN.le] using h
  have h := (pow_le_pow_left₀ (mul_nonneg hN.le (norm_nonneg _)) hx 2).trans (translate_gram B hd ho)
  apply le_of_mul_le_mul_left _ hN
  convert h using 1 <;> ring

#print axioms spectral_weight_from_translates
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
