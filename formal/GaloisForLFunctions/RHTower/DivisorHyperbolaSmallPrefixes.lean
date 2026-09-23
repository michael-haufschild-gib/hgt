import GaloisForLFunctions.RHTower.DivisorHyperbolaAbelBound
import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorAbelProducer
/-!
# Analytic initial divisor-source prefixes

Rational logarithm inequalities and a harmonic error bound certify the initial
ordinary prefixes through 24 and the first four smooth square blocks. Closed
rational identities are proved by kernel-checked arithmetic; no experimental
source values or numerical certificates are assumed.
-/

noncomputable section
open Finset
namespace RHTower
private theorem orientation_gamma_lower : (5768/10000:ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]
    norm_num
  norm_num [harmonic,Finset.sum_range_succ,hlog] at h
  linarith [Real.log_two_lt_d9]
private theorem orientation_log_bounds :
    (1.9455:ℝ) ≤ Real.log 7 ∧ (2.3977:ℝ) ≤ Real.log 11 ∧
    (2.5649:ℝ) ≤ Real.log 13 ∧ (2.8331:ℝ) ≤ Real.log 17 ∧
    (2.9444:ℝ) ≤ Real.log 19 ∧ (3.1354:ℝ) ≤ Real.log 23 := by
  have h7 := log_le_half_sub_inv (x := (8:ℝ)/7) (by norm_num)
  have h11 := log_le_half_sub_inv (x := (12:ℝ)/11) (by norm_num)
  have h13 := (Real.lt_log_one_add_of_pos (x := (1:ℝ)/12) (by norm_num)).le
  have h17 := (Real.lt_log_one_add_of_pos (x := (1:ℝ)/16) (by norm_num)).le
  have h19 := log_le_half_sub_inv (x := (20:ℝ)/19) (by norm_num)
  have h23 := log_le_half_sub_inv (x := (24:ℝ)/23) (by norm_num)
  have l8 : Real.log 8=3*Real.log 2 := by rw [show (8:ℝ)=2^(3 : ℕ) by norm_num,Real.log_pow]; norm_num
  have l12 : Real.log 12=2*Real.log 2+Real.log 3 := by
    rw [show (12:ℝ)=4*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq]
  have l16 : Real.log 16=4*Real.log 2 := by rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]; norm_num
  have l20 : Real.log 20=2*Real.log 2+Real.log 5 := by
    rw [show (20:ℝ)=4*5 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq]
  have l24 : Real.log 24=3*Real.log 2+Real.log 3 := by
    rw [show (24:ℝ)=8*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),l8]
  rw [show (1:ℝ)+1/12=13/12 by norm_num] at h13
  rw [show (1:ℝ)+1/16=17/16 by norm_num] at h17
  rw [Real.log_div (by norm_num) (by norm_num),l8] at h7
  rw [Real.log_div (by norm_num) (by norm_num),l12] at h11 h13
  rw [Real.log_div (by norm_num) (by norm_num),l16] at h17
  rw [Real.log_div (by norm_num) (by norm_num),l20] at h19
  rw [Real.log_div (by norm_num) (by norm_num),l24] at h23
  norm_num at h7 h11 h13 h17 h19 h23
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_gt_d9
  constructor
  · linarith only [h7,h2]
  constructor
  · linarith only [h11,h2,h3]
  constructor
  · linarith only [h13,h2,h3]
  constructor
  · linarith only [h17,h2]
  constructor
  · linarith only [h19,h2,h5]
  · linarith only [h23,h2,h3]

private def orientationLogLower : ℕ → ℝ
  | 1 => 0
  | 2 => 0.6931
  | 3 => 1.0986
  | 4 => 1.3862
  | 5 => 1.6094
  | 6 => 1.7917
  | 7 => 1.9455
  | 8 => 2.0793
  | 9 => 2.1972
  | 10 => 2.3025
  | 11 => 2.3977
  | 12 => 2.4848
  | 13 => 2.5649
  | 14 => 2.6386
  | 15 => 2.7080
  | 16 => 2.7724
  | 17 => 2.8331
  | 18 => 2.8903
  | 19 => 2.9444
  | 20 => 2.9956
  | 21 => 3.0441
  | 22 => 3.0908
  | 23 => 3.1354
  | 24 => 3.1779
  | _ => 0

private theorem orientation_log_small {n : ℕ} (hn : n ∈ Icc 1 24) :
    orientationLogLower n ≤ Real.log n := by
  obtain ⟨h7,h11,h13,h17,h19,h23⟩ := orientation_log_bounds
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_gt_d9
  have l4 : Real.log 4=Real.log 2+Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have l6 : Real.log 6=Real.log 2+Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have l8 : Real.log 8=Real.log 2+Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]
    norm_num
  have l9 : Real.log 9=Real.log 3+Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have l10 : Real.log 10=Real.log 2+Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    norm_num
  have l12 : Real.log 12=Real.log 3+Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]
    norm_num
  have l14 : Real.log 14=Real.log 2+Real.log 7 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (7:ℝ) ≠ 0)]
    norm_num
  have l15 : Real.log 15=Real.log 3+Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    norm_num
  have l16 : Real.log 16=Real.log 4+Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]
    norm_num
  have l18 : Real.log 18=Real.log 2+Real.log 9 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (9:ℝ) ≠ 0)]
    norm_num
  have l20 : Real.log 20=Real.log 4+Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    norm_num
  have l21 : Real.log 21=Real.log 3+Real.log 7 := by
    rw [← Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (7:ℝ) ≠ 0)]
    norm_num
  have l22 : Real.log 22=Real.log 2+Real.log 11 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (11:ℝ) ≠ 0)]
    norm_num
  have l24 : Real.log 24=Real.log 3+Real.log 8 := by
    rw [← Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (8:ℝ) ≠ 0)]
    norm_num
  obtain ⟨hn1,hn24⟩ := mem_Icc.mp hn
  interval_cases n <;> norm_num [orientationLogLower,l24,l22,l21,l20,l18,l16,l15,l14,l12,l10,l9,l8,l6,l4]
  all_goals linarith only [h2,h3,h5,h7,h11,h13,h17,h19,h23]

private def orientationDefectLower (k : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 k, orientationLogLower m)-(∑ d ∈ Icc 1 k, ((k/d:ℕ):ℝ))+
    2*(5768/10000)*k
private theorem orientation_defect_lower {k : ℕ} (hk : k ≤ 24) :
    orientationDefectLower k ≤ primeFreeDivisorDefect k := by
  have hl := sum_le_sum (s := Icc 1 k) (fun m hm =>
    orientation_log_small (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans hk⟩))
  have hg := mul_le_mul_of_nonneg_right orientation_gamma_lower (show (0:ℝ) ≤ 2*k by positivity)
  unfold orientationDefectLower primeFreeDivisorDefect
  linarith only [hl,hg]


private def orientationDefectLowerValue : ℕ → ℝ
  | 0 => 0/1
  | 1 => 96/625
  | 2 => 3/10000
  | 3 => 101/400
  | 4 => -2077/10000
  | 5 => 5553/10000
  | 6 => -2497/5000
  | 7 => 5997/10000
  | 8 => -837/5000
  | 9 => 917/5000
  | 10 => -721/2000
  | 11 => 2977/2500
  | 12 => -2927/2500
  | 13 => 5477/10000
  | 14 => 3399/10000
  | 15 => 403/2000
  | 16 => -349/400
  | 17 => 5571/5000
  | 18 => -8419/10000
  | 19 => 12561/10000
  | 20 => -5947/10000
  | 21 => -397/1000
  | 22 => -763/5000
  | 23 => 5341/2500
  | 24 => -15321/10000
  | _ => 0
set_option maxHeartbeats 800000 in
private theorem orientation_defect_lower_eval {k : ℕ} (hk : k ≤ 24) :
    orientationDefectLower k=orientationDefectLowerValue k := by
  interval_cases k <;> norm_num [orientationDefectLower,orientationDefectLowerValue,orientationLogLower,sum_Icc_succ_top]

set_option maxHeartbeats 800000 in
/-- Analytic initial ordinary-prefix certificate; no numerical experiment enters the proof. -/
theorem sum_primeFreeDivisorDefect_nonneg_of_le_twentyFour {N : ℕ} (hN : N ≤ 24) :
    0 ≤ ∑ k ∈ Icc 1 N, primeFreeDivisorDefect k := by
  have h := sum_le_sum (s := Icc 1 N) (fun k hk => orientation_defect_lower ((mem_Icc.mp hk).2.trans hN))
  have hbase : 0 ≤ ∑ k ∈ Icc 1 N, orientationDefectLower k := by
    have heq : (∑ k ∈ Icc 1 N, orientationDefectLower k)=∑ k ∈ Icc 1 N, orientationDefectLowerValue k := by
      apply sum_congr rfl
      intro k hk
      exact orientation_defect_lower_eval ((mem_Icc.mp hk).2.trans hN)
    rw [heq]
    interval_cases N <;> norm_num [orientationDefectLowerValue,sum_Icc_succ_top]
  exact hbase.trans h

private def orientationSmoothLower (k : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 k, orientationLogLower m)-(2*(k:ℝ)+1)*((harmonic (Nat.sqrt k):ℚ):ℝ)+
    (Nat.sqrt k:ℝ)^(2 : ℕ)+Nat.sqrt k+2*(5768/10000)*k
/-- The first four complete smooth square blocks cover the sharp centered-prefix allowance. -/
theorem sum_divisorHyperbolaSmoothRemainder_twentyFour_ge :
    (7/2:ℝ) ≤ ∑ k ∈ Icc 1 24, divisorHyperbolaSmoothRemainder k := by
  have hpoint (k : ℕ) (hk : k ∈ Icc 1 24) :
      orientationSmoothLower k ≤ divisorHyperbolaSmoothRemainder k := by
    have hl := sum_le_sum (s := Icc 1 k) (fun m hm =>
      orientation_log_small (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans (mem_Icc.mp hk).2⟩))
    have hg := mul_le_mul_of_nonneg_right orientation_gamma_lower (show (0:ℝ) ≤ 2*k by positivity)
    unfold orientationSmoothLower divisorHyperbolaSmoothRemainder
    linarith only [hl,hg]
  have hsum := sum_le_sum hpoint
  have hbase : (7/2:ℝ) ≤ ∑ k ∈ Icc 1 24, orientationSmoothLower k := by
    have r1 : Nat.sqrt 1=1 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r2 : Nat.sqrt 2=1 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r3 : Nat.sqrt 3=1 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r4 : Nat.sqrt 4=2 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r5 : Nat.sqrt 5=2 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r6 : Nat.sqrt 6=2 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r7 : Nat.sqrt 7=2 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r8 : Nat.sqrt 8=2 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r9 : Nat.sqrt 9=3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r10 : Nat.sqrt 10=3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r11 : Nat.sqrt 11=3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r12 : Nat.sqrt 12=3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r13 : Nat.sqrt 13=3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r14 : Nat.sqrt 14=3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r15 : Nat.sqrt 15=3 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r16 : Nat.sqrt 16=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r17 : Nat.sqrt 17=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r18 : Nat.sqrt 18=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r19 : Nat.sqrt 19=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r20 : Nat.sqrt 20=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r21 : Nat.sqrt 21=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r22 : Nat.sqrt 22=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r23 : Nat.sqrt 23=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    have r24 : Nat.sqrt 24=4 := (Nat.eq_sqrt.mpr (by norm_num)).symm
    norm_num [orientationSmoothLower,orientationLogLower,sum_Icc_succ_top,harmonic,Finset.sum_range_succ,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24]
  exact hbase.trans hsum

end RHTower
