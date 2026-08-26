import GaloisForLFunctions.RHTower.Sieve.TypeIIBlockSum

/-!
# Support of the long Vaughan Type II coefficient

The long coefficient vanishes through its truncation point.  Consequently any dyadic long-variable
block ending at or below `U + 1` is identically zero.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

theorem typeIILong_eq_zero_of_le {U d : ℕ} (hd : d ≤ U) : typeIILong U d = 0 := by
  exact vonMangoldt_sub_truncAF_eq_zero hd

theorem maskedBlockSum_typeIILong_eq_zero_of_upper_le {U Q : ℕ} (hQU : Q ≤ U + 1)
    (T r : ℝ) (A B L P V : ℕ) :
    maskedBlockSum T r A B L P Q (fun d => typeIILong U d) (fun m => typeIIShort V m) = 0 := by
  rw [maskedBlockSum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_Ico] at hd
  have hdU : d ≤ U := by omega
  rw [typeIILong_eq_zero_of_le hdU]
  norm_num

theorem upper_gt_truncation_of_maskedBlockSum_typeIILong_ne_zero {U Q : ℕ}
    {T r : ℝ} {A B L P V : ℕ}
    (hne : maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m) ≠ 0) :
    U + 1 < Q := by
  by_contra h
  exact hne (maskedBlockSum_typeIILong_eq_zero_of_upper_le (by omega) T r A B L P V)

theorem typeIIShort_eq_zero_of_le {V m : ℕ} (hm : 1 ≤ m) (hmV : m ≤ V) :
    typeIIShort V m = 0 := by
  exact one_sub_zeta_mul_truncAF_moebius_apply_eq_zero hm hmV

theorem maskedBlockSum_typeIIShort_eq_zero_of_effHigh_le {B P V Q : ℕ}
    (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hhigh : effHigh B P ≤ V)
    (T r : ℝ) (A L U : ℕ) :
    maskedBlockSum T r A B L P Q (fun d => typeIILong U d) (fun m => typeIIShort V m) = 0 := by
  rw [maskedBlockSum]
  apply Finset.sum_eq_zero
  intro d hd
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro m hm
  by_cases heff : m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1)
  · rw [Finset.mem_Ico] at heff
    have hm1 : 1 ≤ m := le_trans (one_le_effLow A Q) heff.1
    have hmV : m ≤ V := le_trans (by omega) hhigh
    rw [typeIIShort_eq_zero_of_le hm1 hmV]
    norm_num
  · rw [maskedNdExp_eq_zero_of_not_mem_eff hP hQ T r hd heff]
    norm_num

theorem effHigh_gt_short_truncation_of_maskedBlockSum_ne_zero {B P V Q : ℕ}
    (hP : 1 ≤ P) (hQ : 2 ≤ Q) {T r : ℝ} {A L U : ℕ}
    (hne : maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m) ≠ 0) :
    V < effHigh B P := by
  by_contra h
  exact hne (maskedBlockSum_typeIIShort_eq_zero_of_effHigh_le hP hQ (by omega) T r A L U)

theorem mul_succ_le_pred_of_maskedBlockSum_ne_zero {B P V Q : ℕ}
    (hP : 1 ≤ P) (hQ : 2 ≤ Q) {T r : ℝ} {A L U : ℕ}
    (hne : maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m) ≠ 0) :
    P * (V + 1) ≤ B - 1 := by
  have hhigh := effHigh_gt_short_truncation_of_maskedBlockSum_ne_zero hP hQ hne
  rw [effHigh] at hhigh
  simpa [mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < P)).mp hhigh

end

end RHTower.Sieve
