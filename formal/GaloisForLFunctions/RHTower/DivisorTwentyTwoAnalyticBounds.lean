import GaloisForLFunctions.RHTower.HarmonicGeometricBounds
import GaloisForLFunctions.RHTower.DivisorUniformSquareRootBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
/-!
# Analytic source boxes for signed reserve and repair witnesses

Rational logarithm series bounds, harmonic Euler-constant corrections, and
exact square inequalities enclose every source term. Signed interval products
retain the full Abel sum. The public bounds certify the five retained
coefficients and original diagonals needed for the successor-average and
inherited-contraction witnesses, and the odd/even profiles at eleven and
fifteen used by the inherited-debt source circuit.
No numerical experiment is a proof premise.
-/

noncomputable section
open Finset
namespace RHTower
private lemma gamma_box : (0.577215:ℝ) ≤ Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant ≤ 0.577216 := by
  have h := harmonic_mascheroni_le_half_sub_twelfth (n:=64) (by norm_num)
  have he : Real.log (64:ℝ)=6*Real.log 2 := by
    rw [show (64:ℝ)=2^(6 : ℕ) by norm_num,Real.log_pow]; norm_num
  norm_num [harmonic,Finset.sum_range_succ,he] at h
  constructor
  · linarith [Real.log_two_lt_d9]
  · linarith [eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]
private lemma ratio_box {x : ℝ} (h0 : 0≤x) (h1 : x<1) :
    2*(x+x^(3 : ℕ)/3+x^(5 : ℕ)/5) ≤ Real.log ((1+x)/(1-x)) ∧
      Real.log ((1+x)/(1-x)) ≤ 2*(x+x^(3 : ℕ)/3+x^(5 : ℕ)/5+x^(7 : ℕ)/(1-x^(2 : ℕ))) := by
  have hl := Real.sum_range_le_log_div h0 h1 3
  have hu := Real.log_div_le_sum_range_add h0 h1 3
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith only [hl,hu]

private lemma prime_log_boxes :
    (1.945909 ≤ Real.log 7 ∧ Real.log 7 ≤ 1.945911) ∧
    (2.397894 ≤ Real.log 11 ∧ Real.log 11 ≤ 2.397896) ∧
    (2.564948 ≤ Real.log 13 ∧ Real.log 13 ≤ 2.564950) ∧
    (2.833212 ≤ Real.log 17 ∧ Real.log 17 ≤ 2.833214) ∧
    (2.944438 ≤ Real.log 19 ∧ Real.log 19 ≤ 2.944440) := by
  have h7 := ratio_box (x:=(1/15:ℝ)) (by norm_num) (by norm_num)
  have h11 := ratio_box (x:=(1/21:ℝ)) (by norm_num) (by norm_num)
  have h13 := ratio_box (x:=(1/53:ℝ)) (by norm_num) (by norm_num)
  have h17 := ratio_box (x:=(1/33:ℝ)) (by norm_num) (by norm_num)
  have h19 := ratio_box (x:=(1/39:ℝ)) (by norm_num) (by norm_num)
  norm_num at h7 h11 h13 h17 h19
  have l8 : Real.log (8:ℝ)=3*Real.log 2 := by
    rw [show (8:ℝ)=2^(3 : ℕ) by norm_num,Real.log_pow]; norm_num
  have l10 : Real.log (10:ℝ)=Real.log 2+Real.log 5 := by
    rw [show (10:ℝ)=2*5 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have l27 : Real.log (27:ℝ)=3*Real.log 3 := by
    rw [show (27:ℝ)=3^(3 : ℕ) by norm_num,Real.log_pow]; norm_num
  have l26 : Real.log (26:ℝ)=Real.log 2+Real.log 13 := by
    rw [show (26:ℝ)=2*13 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have l16 : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]; norm_num
  have l20 : Real.log (20:ℝ)=2*Real.log 2+Real.log 5 := by
    rw [show (20:ℝ)=4*5 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq]
  rw [Real.log_div (by norm_num) (by norm_num),l8] at h7
  rw [Real.log_div (by norm_num) (by norm_num),l10] at h11
  rw [Real.log_div (by norm_num) (by norm_num),l27,l26] at h13
  rw [Real.log_div (by norm_num) (by norm_num),l16] at h17
  rw [Real.log_div (by norm_num) (by norm_num),l20] at h19
  have a := Real.log_two_gt_d9
  have b := Real.log_two_lt_d9
  have c := Real.log_three_gt_d9
  have d := Real.log_three_lt_d9
  have e := Real.log_five_gt_d9
  have f := Real.log_five_lt_d9
  constructor
  · constructor <;> linarith only [h7.1,h7.2,a,b]
  constructor
  · constructor <;> linarith only [h11.1,h11.2,a,b,e,f]
  constructor
  · constructor <;> linarith only [h13.1,h13.2,a,b,c,d]
  constructor <;> constructor <;> linarith only [h17.1,h17.2,h19.1,h19.2,a,b,e,f]

end RHTower
namespace RHTower
private def logLower : ℕ → ℝ
  | 1 => 0
  | 2 => 0.693147180
  | 3 => 1.098612288
  | 4 => 2*0.693147180
  | 5 => 1.609437912
  | 6 => 0.693147180+1.098612288
  | 7 => 1.945909
  | 8 => 3*0.693147180
  | 9 => 2*1.098612288
  | 10 => 0.693147180+1.609437912
  | 11 => 2.397894
  | 12 => 2*0.693147180+1.098612288
  | 13 => 2.564948
  | 14 => 0.693147180+1.945909
  | 15 => 1.098612288+1.609437912
  | 16 => 4*0.693147180
  | 17 => 2.833212
  | 18 => 0.693147180+2*1.098612288
  | 19 => 2.944438
  | 20 => 2*0.693147180+1.609437912
  | 21 => 1.098612288+1.945909
  | 22 => 0.693147180+2.397894
  | 23 => 3.135493
  | 24 => 3*0.693147180+1.098612288
  | _ => 0
private def logUpper : ℕ → ℝ
  | 1 => 0
  | 2 => 0.693147182
  | 3 => 1.098612290
  | 4 => 2*0.693147182
  | 5 => 1.609437914
  | 6 => 0.693147182+1.098612290
  | 7 => 1.945911
  | 8 => 3*0.693147182
  | 9 => 2*1.098612290
  | 10 => 0.693147182+1.609437914
  | 11 => 2.397896
  | 12 => 2*0.693147182+1.098612290
  | 13 => 2.564950
  | 14 => 0.693147182+1.945911
  | 15 => 1.098612290+1.609437914
  | 16 => 4*0.693147182
  | 17 => 2.833214
  | 18 => 0.693147182+2*1.098612290
  | 19 => 2.944440
  | 20 => 2*0.693147182+1.609437914
  | 21 => 1.098612290+1.945911
  | 22 => 0.693147182+2.397896
  | 23 => 3.135495
  | 24 => 3*0.693147182+1.098612290
  | _ => 0
set_option maxHeartbeats 800000 in
private lemma log_box {n : ℕ} (hn : n∈Icc 1 21) :
    logLower n ≤ Real.log n ∧ Real.log n ≤ logUpper n := by
  have hmul (a b : ℕ) (ha : a≠0) (hb : b≠0) :
      Real.log ((a*b:ℕ):ℝ)=Real.log a+Real.log b := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]
  have h4 := hmul 2 2 (by omega) (by omega)
  have h6 := hmul 2 3 (by omega) (by omega)
  have h8 := hmul 2 4 (by omega) (by omega)
  have h9 := hmul 3 3 (by omega) (by omega)
  have h10 := hmul 2 5 (by omega) (by omega)
  have h12 := hmul 4 3 (by omega) (by omega)
  have h14 := hmul 2 7 (by omega) (by omega)
  have h15 := hmul 3 5 (by omega) (by omega)
  have h16 := hmul 4 4 (by omega) (by omega)
  have h18 := hmul 2 9 (by omega) (by omega)
  have h20 := hmul 4 5 (by omega) (by omega)
  have h21 := hmul 3 7 (by omega) (by omega)
  norm_num only [Nat.cast_ofNat] at h4 h6 h8 h9 h10 h12 h14 h15 h16 h18 h20 h21
  obtain ⟨h7,h11,h13,h17,h19⟩ := prime_log_boxes
  obtain ⟨ha,hb⟩ := mem_Icc.mp hn
  interval_cases n
  all_goals norm_num [Nat.cast_ofNat,logLower,logUpper,h21,h20,h18,h16,h15,h14,h12,h10,h9,h8,h6,h4,Real.log_one]
  all_goals constructor <;> linarith only [h7.1,h7.2,h11.1,h11.2,h13.1,h13.2,h17.1,h17.2,h19.1,h19.2,Real.log_two_gt_d9,Real.log_two_lt_d9,
    Real.log_three_gt_d9,Real.log_three_lt_d9,Real.log_five_gt_d9,Real.log_five_lt_d9]

private def rootLower : ℕ → ℝ
  | 1 => 1
  | 2 => 1.41421
  | 3 => 1.73205
  | 4 => 2
  | 5 => 2.23606
  | 6 => 2.44948
  | 7 => 2.64575
  | 8 => 2.82842
  | 9 => 3
  | 10 => 3.16227
  | 11 => 3.31662
  | 12 => 3.46410
  | 13 => 3.60555
  | 14 => 3.74165
  | 15 => 3.87298
  | 16 => 4
  | 17 => 4.12310
  | 18 => 4.24264
  | 19 => 4.35889
  | 20 => 4.47213
  | 21 => 4.58257
  | 22 => 4.69041
  | 23 => 4.7958
  | 24 => 4.8989
  | 25 => 5
  | _ => 0
private def rootUpper : ℕ → ℝ
  | 1 => 1
  | 2 => 1.41422
  | 3 => 1.73206
  | 4 => 2
  | 5 => 2.23607
  | 6 => 2.44949
  | 7 => 2.64576
  | 8 => 2.82843
  | 9 => 3
  | 10 => 3.16228
  | 11 => 3.31663
  | 12 => 3.46411
  | 13 => 3.60556
  | 14 => 3.74166
  | 15 => 3.87299
  | 16 => 4
  | 17 => 4.12311
  | 18 => 4.24265
  | 19 => 4.35890
  | 20 => 4.47214
  | 21 => 4.58258
  | 22 => 4.69042
  | 23 => 4.7959
  | 24 => 4.8990
  | 25 => 5
  | _ => 0
private lemma root_box {n : ℕ} (hn : n∈Icc 1 22) :
    rootLower n ≤ Real.sqrt n ∧ Real.sqrt n ≤ rootUpper n := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  have hp := Real.sqrt_nonneg (n:ℝ)
  obtain ⟨ha,hb⟩ := mem_Icc.mp hn
  interval_cases n
  all_goals norm_num only [Nat.cast_ofNat] at hs hp ⊢
  all_goals norm_num [rootLower,rootUpper]
  all_goals constructor <;> nlinarith only [hs,hp]
end RHTower

namespace RHTower
private def defectLower (n : ℕ) : ℝ :=
  (∑ k∈Icc 1 n,logLower k)-(∑ k∈Icc 1 n,((n/k:ℕ):ℝ))+2*0.577215*n
private def defectUpper (n : ℕ) : ℝ :=
  (∑ k∈Icc 1 n,logUpper k)-(∑ k∈Icc 1 n,((n/k:ℕ):ℝ))+2*0.577216*n
private lemma defect_box {n : ℕ} (hn : n≤21) :
    defectLower n ≤ primeFreeDivisorDefect n ∧ primeFreeDivisorDefect n ≤ defectUpper n := by
  have hl := sum_le_sum (fun k (hk : k∈Icc 1 n) =>
    (log_box (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩)).1)
  have hu := sum_le_sum (fun k (hk : k∈Icc 1 n) =>
    (log_box (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩)).2)
  have gl := mul_le_mul_of_nonneg_right gamma_box.1 (Nat.cast_nonneg (α:=ℝ) n)
  have gu := mul_le_mul_of_nonneg_right gamma_box.2 (Nat.cast_nonneg (α:=ℝ) n)
  dsimp [defectLower,defectUpper,primeFreeDivisorDefect]
  constructor <;> linarith only [hl,hu,gl,gu]

private def weightLower (n : ℕ) : ℝ := rootLower (n+1)-rootUpper n
private def weightUpper (n : ℕ) : ℝ := rootUpper (n+1)-rootLower n
private def termLower (k n : ℕ) : ℝ :=
  min (weightLower k*defectLower n) (weightUpper k*defectLower n)
private def termUpper (k n : ℕ) : ℝ :=
  max (weightLower k*defectUpper n) (weightUpper k*defectUpper n)
private lemma product_box {w x l u a b : ℝ} (hw0 : 0≤w)
    (hw : l≤w ∧ w≤u) (hx : a≤x ∧ x≤b) :
    min (l*a) (u*a) ≤ w*x ∧ w*x ≤ max (l*b) (u*b) := by
  constructor
  · have hax := mul_le_mul_of_nonneg_left hx.1 hw0
    by_cases ha : 0≤a
    · exact (min_le_left _ _).trans ((mul_le_mul_of_nonneg_right hw.1 ha).trans hax)
    · exact (min_le_right _ _).trans ((mul_le_mul_of_nonpos_right hw.2 (by linarith)).trans hax)
  · have hxb := mul_le_mul_of_nonneg_left hx.2 hw0
    by_cases hb : 0≤b
    · exact hxb.trans ((mul_le_mul_of_nonneg_right hw.2 hb).trans (le_max_right _ _))
    · exact hxb.trans ((mul_le_mul_of_nonpos_right hw.1 (by linarith)).trans (le_max_left _ _))
private lemma term_box {k n : ℕ} (hk : k∈Icc 1 21) (hn : n≤21) :
    termLower k n ≤ (Real.sqrt (k+1:ℕ)-Real.sqrt k)*primeFreeDivisorDefect n ∧
      (Real.sqrt (k+1:ℕ)-Real.sqrt k)*primeFreeDivisorDefect n ≤ termUpper k n := by
  have hk0 := (mem_Icc.mp hk).1
  have hk1 := (mem_Icc.mp hk).2
  have a := root_box (n:=k) (mem_Icc.mpr ⟨hk0,by omega⟩)
  have b := root_box (n:=k+1) (mem_Icc.mpr ⟨by omega,by omega⟩)
  apply product_box (sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)))
    (And.intro (by dsimp [weightLower]; linarith only [a.2,b.1])
      (by dsimp [weightUpper]; linarith only [a.1,b.2])) (defect_box hn)

private def channelLower (d : ℕ) : ℝ := ∑ k∈Icc d 21,termLower k (k/d)
private def channelUpper (d : ℕ) : ℝ := ∑ k∈Icc d 21,termUpper k (k/d)
private lemma channel_box {d : ℕ} (hd : 1≤d) :
    channelLower d ≤ divisorUnsignedDilationChannel 22 d ∧
      divisorUnsignedDilationChannel 22 d ≤ channelUpper d := by
  have hlo := sum_le_sum (fun k (hk : k∈Icc d 21) =>
    (term_box (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,(mem_Icc.mp hk).2⟩)
      ((Nat.div_le_self k d).trans (mem_Icc.mp hk).2)).1)
  have hhi := sum_le_sum (fun k (hk : k∈Icc d 21) =>
    (term_box (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,(mem_Icc.mp hk).2⟩)
      ((Nat.div_le_self k d).trans (mem_Icc.mp hk).2)).2)
  constructor
  · simpa [channelLower,divisorUnsignedDilationChannel] using hlo
  · simpa [channelUpper,divisorUnsignedDilationChannel] using hhi
end RHTower
namespace RHTower
private def witnessHead : ℝ := divisorUnsignedDilationChannel 22 1-
  divisorUnsignedDilationChannel 22 3-divisorUnsignedDilationChannel 22 7-
  divisorUnsignedDilationChannel 22 11-divisorUnsignedDilationChannel 22 17-
  divisorUnsignedDilationChannel 22 19+divisorUnsignedDilationChannel 22 21
private def witnessTwo : ℝ := -divisorUnsignedDilationChannel 22 2+
  divisorUnsignedDilationChannel 22 6+divisorUnsignedDilationChannel 22 14
private def witnessFive : ℝ := -divisorUnsignedDilationChannel 22 5+divisorUnsignedDilationChannel 22 15
private def witnessTen : ℝ := divisorUnsignedDilationChannel 22 10
private def witnessThirteen : ℝ := -divisorUnsignedDilationChannel 22 13

set_option maxHeartbeats 3000000 in
private lemma witness_boxes :
    (-0.480 ≤ witnessHead ∧ witnessHead ≤ -0.479) ∧
    (0.182 ≤ witnessTwo ∧ witnessTwo ≤ 0.183) ∧
    (-0.127 ≤ witnessFive ∧ witnessFive ≤ -0.126) ∧
    (0.202 ≤ witnessTen ∧ witnessTen ≤ 0.203) ∧
    (-0.168 ≤ witnessThirteen ∧ witnessThirteen ≤ -0.167) := by
  have h1 := channel_box (d:=1) (by norm_num)
  have h2 := channel_box (d:=2) (by norm_num)
  have h3 := channel_box (d:=3) (by norm_num)
  have h5 := channel_box (d:=5) (by norm_num)
  have h6 := channel_box (d:=6) (by norm_num)
  have h7 := channel_box (d:=7) (by norm_num)
  have h10 := channel_box (d:=10) (by norm_num)
  have h11 := channel_box (d:=11) (by norm_num)
  have h13 := channel_box (d:=13) (by norm_num)
  have h14 := channel_box (d:=14) (by norm_num)
  have h15 := channel_box (d:=15) (by norm_num)
  have h17 := channel_box (d:=17) (by norm_num)
  have h19 := channel_box (d:=19) (by norm_num)
  have h21 := channel_box (d:=21) (by norm_num)
  norm_num [channelLower,channelUpper,Finset.sum_Icc_succ_top]
    at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14 h15 h17 h19 h21
  norm_num [termLower,termUpper,weightLower,weightUpper,defectLower,defectUpper,
    logLower,logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top]
    at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14 h15 h17 h19 h21
  dsimp [witnessHead,witnessTwo,witnessFive,witnessTen,witnessThirteen]
  constructor
  · constructor <;> linarith only [h1.1,h1.2,h3.1,h3.2,h7.1,h7.2,h11.1,h11.2,h17.1,h17.2,h19.1,h19.2,h21.1,h21.2]
  constructor
  · constructor <;> linarith only [h2.1,h2.2,h6.1,h6.2,h14.1,h14.2]
  constructor
  · constructor <;> linarith only [h5.1,h5.2,h15.1,h15.2]
  constructor
  · constructor <;> linarith only [h10.1,h10.2]
  · constructor <;> linarith only [h13.1,h13.2]

private def active : Finset ℕ := {1,2,3,5,6,7,10,11,13,14,15,17,19,21}
set_option maxHeartbeats 3000000 in
private lemma initial_unsigned_box :
    (0.550:ℝ) ≤ ∑ d∈active,(divisorUnsignedDilationChannel 22 d)^(2 : ℕ) ∧
      (∑ d∈active,(divisorUnsignedDilationChannel 22 d)^(2 : ℕ)) ≤ 0.553 := by
  have hl (d : ℕ) (hd : d∈active) : 0≤channelLower d := by
    simp only [active,mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [channelLower,Finset.sum_Icc_succ_top]
    all_goals norm_num [termLower,weightLower,weightUpper,defectLower,
      logLower,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  have hpos (d : ℕ) (hd : d∈active) : 1≤d := by
    simp only [active,mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have hlo := sum_le_sum (fun d (hd : d∈active) =>
    mul_le_mul (channel_box (hpos d hd)).1 (channel_box (hpos d hd)).1
      (hl d hd) ((hl d hd).trans (channel_box (hpos d hd)).1))
  have hhi := sum_le_sum (fun d (hd : d∈active) =>
    mul_le_mul (channel_box (hpos d hd)).2 (channel_box (hpos d hd)).2
      (divisorUnsignedDilationChannel_nonneg 22 d)
      ((divisorUnsignedDilationChannel_nonneg 22 d).trans (channel_box (hpos d hd)).2))
  simp only [← pow_two] at hlo hhi
  have hlow : (0.550:ℝ) ≤ ∑ d∈active,(channelLower d)^(2 : ℕ) := by
    norm_num [active,channelLower,Finset.sum_Icc_succ_top]
    norm_num [termLower,weightLower,weightUpper,defectLower,
      logLower,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  have hupp : (∑ d∈active,(channelUpper d)^(2 : ℕ)) ≤ (0.553:ℝ) := by
    norm_num [active,channelUpper,Finset.sum_Icc_succ_top]
    norm_num [termUpper,weightLower,weightUpper,defectUpper,
      logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  exact ⟨hlow.trans hlo,hhi.trans hupp⟩
end RHTower

namespace RHTower
/-- Analytic bounds for the literal five-coordinate source after the displayed prime core. -/
theorem divisorUnsignedDilationChannel_twentyTwo_profile_boxes :
    (-0.480 ≤ (divisorUnsignedDilationChannel 22 1-divisorUnsignedDilationChannel 22 3-
      divisorUnsignedDilationChannel 22 7-divisorUnsignedDilationChannel 22 11-
      divisorUnsignedDilationChannel 22 17-divisorUnsignedDilationChannel 22 19+
      divisorUnsignedDilationChannel 22 21) ∧ (divisorUnsignedDilationChannel 22 1-divisorUnsignedDilationChannel 22 3-
      divisorUnsignedDilationChannel 22 7-divisorUnsignedDilationChannel 22 11-
      divisorUnsignedDilationChannel 22 17-divisorUnsignedDilationChannel 22 19+
      divisorUnsignedDilationChannel 22 21) ≤ -0.479) ∧
    (0.182 ≤ (-divisorUnsignedDilationChannel 22 2+divisorUnsignedDilationChannel 22 6+
      divisorUnsignedDilationChannel 22 14) ∧ (-divisorUnsignedDilationChannel 22 2+divisorUnsignedDilationChannel 22 6+
      divisorUnsignedDilationChannel 22 14) ≤ 0.183) ∧
    (-0.127 ≤ (-divisorUnsignedDilationChannel 22 5+divisorUnsignedDilationChannel 22 15) ∧ (-divisorUnsignedDilationChannel 22 5+divisorUnsignedDilationChannel 22 15) ≤ -0.126) ∧
    (0.202 ≤ divisorUnsignedDilationChannel 22 10 ∧ divisorUnsignedDilationChannel 22 10 ≤ 0.203) ∧
    (-0.168 ≤ (-divisorUnsignedDilationChannel 22 13) ∧ (-divisorUnsignedDilationChannel 22 13) ≤ -0.167) := witness_boxes

/-- The original squarefree unsigned diagonal at cutoff twenty-two has a
strict rational enclosure, derived solely from the actual analytic source. -/
theorem sum_divisorUnsignedDilationChannel_twentyTwo_sq_bounds :
    (0.550:ℝ) ≤ ∑ d∈({1,2,3,5,6,7,10,11,13,14,15,17,19,21}:Finset ℕ),
      (divisorUnsignedDilationChannel 22 d)^(2 : ℕ) ∧
    (∑ d∈({1,2,3,5,6,7,10,11,13,14,15,17,19,21}:Finset ℕ),
      (divisorUnsignedDilationChannel 22 d)^(2 : ℕ)) ≤ 0.553 := initial_unsigned_box
end RHTower
namespace RHTower

private def seventeenLower (d : ℕ) : ℝ := ∑ k∈Icc d 16,termLower k (k/d)
private def seventeenUpper (d : ℕ) : ℝ := ∑ k∈Icc d 16,termUpper k (k/d)
private lemma seventeen_channel_box {d : ℕ} (hd : 1≤d) :
    seventeenLower d ≤ divisorUnsignedDilationChannel 17 d ∧
      divisorUnsignedDilationChannel 17 d ≤ seventeenUpper d := by
  have hlo := sum_le_sum (fun k (hk : k∈Icc d 16) =>
    (term_box (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans (by omega)⟩)
      (show k/d≤21 by have := Nat.div_le_self k d; have := (mem_Icc.mp hk).2; omega)).1)
  have hhi := sum_le_sum (fun k (hk : k∈Icc d 16) =>
    (term_box (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans (by omega)⟩)
      (show k/d≤21 by have := Nat.div_le_self k d; have := (mem_Icc.mp hk).2; omega)).2)
  constructor
  · simpa [seventeenLower,divisorUnsignedDilationChannel] using hlo
  · simpa [seventeenUpper,divisorUnsignedDilationChannel] using hhi

set_option maxHeartbeats 3000000 in
/-- Analytic source boxes at cutoff seventeen after processing primes three,
five and seven. The full retained source has one positive and three negative coordinates. -/
theorem divisorUnsignedDilationChannel_seventeen_profile_boxes :
    (-0.402 ≤ (divisorUnsignedDilationChannel 17 1-divisorUnsignedDilationChannel 17 3-
      divisorUnsignedDilationChannel 17 5-divisorUnsignedDilationChannel 17 7+
      divisorUnsignedDilationChannel 17 15) ∧
      (divisorUnsignedDilationChannel 17 1-divisorUnsignedDilationChannel 17 3-
      divisorUnsignedDilationChannel 17 5-divisorUnsignedDilationChannel 17 7+
      divisorUnsignedDilationChannel 17 15) ≤ -0.401) ∧
    (0.076 ≤ (-divisorUnsignedDilationChannel 17 2+divisorUnsignedDilationChannel 17 6+
      divisorUnsignedDilationChannel 17 10+divisorUnsignedDilationChannel 17 14) ∧
      (-divisorUnsignedDilationChannel 17 2+divisorUnsignedDilationChannel 17 6+
      divisorUnsignedDilationChannel 17 10+divisorUnsignedDilationChannel 17 14) ≤ 0.078) ∧
    (-0.125 ≤ -divisorUnsignedDilationChannel 17 11 ∧
      -divisorUnsignedDilationChannel 17 11 ≤ -0.124) ∧
    (-0.080 ≤ -divisorUnsignedDilationChannel 17 13 ∧
      -divisorUnsignedDilationChannel 17 13 ≤ -0.079) := by
  have h1 := seventeen_channel_box (d:=1) (by norm_num)
  have h2 := seventeen_channel_box (d:=2) (by norm_num)
  have h3 := seventeen_channel_box (d:=3) (by norm_num)
  have h5 := seventeen_channel_box (d:=5) (by norm_num)
  have h6 := seventeen_channel_box (d:=6) (by norm_num)
  have h7 := seventeen_channel_box (d:=7) (by norm_num)
  have h10 := seventeen_channel_box (d:=10) (by norm_num)
  have h11 := seventeen_channel_box (d:=11) (by norm_num)
  have h13 := seventeen_channel_box (d:=13) (by norm_num)
  have h14 := seventeen_channel_box (d:=14) (by norm_num)
  have h15 := seventeen_channel_box (d:=15) (by norm_num)
  norm_num [seventeenLower,seventeenUpper,Finset.sum_Icc_succ_top] at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14 h15
  norm_num [termLower,termUpper,weightLower,weightUpper,defectLower,defectUpper,
    logLower,logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top] at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14 h15
  constructor
  · constructor <;> linarith only [h1.1,h1.2,h3.1,h3.2,h5.1,h5.2,h7.1,h7.2,h15.1,h15.2]
  constructor
  · constructor <;> linarith only [h2.1,h2.2,h6.1,h6.2,h10.1,h10.2,h14.1,h14.2]
  constructor <;> constructor <;> linarith only [h11.1,h11.2,h13.1,h13.2]

set_option maxHeartbeats 3000000 in
/-- The actual original diagonal at seventeen has a strict analytic enclosure. -/
theorem sum_divisorUnsignedDilationChannel_seventeen_sq_bounds :
    (0.360:ℝ) ≤ ∑ d∈({1,2,3,5,6,7,10,11,13,14,15}:Finset ℕ),
      (divisorUnsignedDilationChannel 17 d)^(2 : ℕ) ∧
    (∑ d∈({1,2,3,5,6,7,10,11,13,14,15}:Finset ℕ),
      (divisorUnsignedDilationChannel 17 d)^(2 : ℕ)) ≤ 0.365 := by
  let active : Finset ℕ := {1,2,3,5,6,7,10,11,13,14,15}
  have hpos (d : ℕ) (hd : d∈active) : 1≤d := by
    simp only [active,mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have hl (d : ℕ) (hd : d∈active) : 0 ≤ seventeenLower d := by
    simp only [active,mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [seventeenLower,Finset.sum_Icc_succ_top]
    all_goals norm_num [termLower,weightLower,weightUpper,defectLower,
      logLower,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  have hlo := sum_le_sum (fun d (hd : d∈active) =>
    mul_le_mul (seventeen_channel_box (hpos d hd)).1 (seventeen_channel_box (hpos d hd)).1
      (hl d hd) ((hl d hd).trans (seventeen_channel_box (hpos d hd)).1))
  have hhi := sum_le_sum (fun d (hd : d∈active) =>
    mul_le_mul (seventeen_channel_box (hpos d hd)).2 (seventeen_channel_box (hpos d hd)).2
      (divisorUnsignedDilationChannel_nonneg 17 d)
      ((divisorUnsignedDilationChannel_nonneg 17 d).trans (seventeen_channel_box (hpos d hd)).2))
  have hlow : (0.360:ℝ) ≤ ∑ d∈active,(seventeenLower d)^(2 : ℕ) := by
    norm_num [active,seventeenLower,Finset.sum_Icc_succ_top]
    norm_num [termLower,weightLower,weightUpper,defectLower,
      logLower,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  have hupp : (∑ d∈active,(seventeenUpper d)^(2 : ℕ)) ≤ (0.365:ℝ) := by
    norm_num [active,seventeenUpper,Finset.sum_Icc_succ_top]
    norm_num [termUpper,weightLower,weightUpper,defectUpper,
      logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  simp only [← pow_two] at hlo hhi
  exact ⟨hlow.trans hlo,hhi.trans hupp⟩
end RHTower

namespace RHTower
private def debtChannelLower (M d : ℕ) : ℝ := ∑ k∈Icc d (M-1),termLower k (k/d)
private def debtChannelUpper (M d : ℕ) : ℝ := ∑ k∈Icc d (M-1),termUpper k (k/d)
private lemma debt_channel_box {M d : ℕ} (hM : M≤22) (hd : 1≤d) :
    debtChannelLower M d ≤ divisorUnsignedDilationChannel M d ∧
      divisorUnsignedDilationChannel M d ≤ debtChannelUpper M d := by
  have hlo := sum_le_sum (fun k (hk : k∈Icc d (M-1)) =>
    (term_box (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,by have := (mem_Icc.mp hk).2; omega⟩)
      (show k/d≤21 by have := Nat.div_le_self k d; have := (mem_Icc.mp hk).2; omega)).1)
  have hhi := sum_le_sum (fun k (hk : k∈Icc d (M-1)) =>
    (term_box (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,by have := (mem_Icc.mp hk).2; omega⟩)
      (show k/d≤21 by have := Nat.div_le_self k d; have := (mem_Icc.mp hk).2; omega)).2)
  exact ⟨by simpa [debtChannelLower,divisorUnsignedDilationChannel] using hlo,
    by simpa [debtChannelUpper,divisorUnsignedDilationChannel] using hhi⟩

set_option maxHeartbeats 3000000 in
/-- Analytic odd/even source boxes at eleven for the inherited-debt circuit. -/
theorem divisorUnsignedDilationChannel_eleven_debt_profile_boxes :
    (-0.273 ≤ divisorUnsignedDilationChannel 11 1-divisorUnsignedDilationChannel 11 3-
      divisorUnsignedDilationChannel 11 5-divisorUnsignedDilationChannel 11 7 ∧
      divisorUnsignedDilationChannel 11 1-divisorUnsignedDilationChannel 11 3-
      divisorUnsignedDilationChannel 11 5-divisorUnsignedDilationChannel 11 7 ≤ -0.271) ∧
    (-0.050 ≤ -divisorUnsignedDilationChannel 11 2+divisorUnsignedDilationChannel 11 6+
      divisorUnsignedDilationChannel 11 10 ∧
      -divisorUnsignedDilationChannel 11 2+divisorUnsignedDilationChannel 11 6+
      divisorUnsignedDilationChannel 11 10 ≤ -0.047) := by
  have h1 := debt_channel_box (M:=11) (d:=1) (by omega) (by omega)
  have h2 := debt_channel_box (M:=11) (d:=2) (by omega) (by omega)
  have h3 := debt_channel_box (M:=11) (d:=3) (by omega) (by omega)
  have h5 := debt_channel_box (M:=11) (d:=5) (by omega) (by omega)
  have h6 := debt_channel_box (M:=11) (d:=6) (by omega) (by omega)
  have h7 := debt_channel_box (M:=11) (d:=7) (by omega) (by omega)
  have h10 := debt_channel_box (M:=11) (d:=10) (by omega) (by omega)
  norm_num [debtChannelLower,debtChannelUpper,Finset.sum_Icc_succ_top] at h1 h2 h3 h5 h6 h7 h10
  norm_num [termLower,termUpper,weightLower,weightUpper,defectLower,defectUpper,
    logLower,logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top] at h1 h2 h3 h5 h6 h7 h10
  constructor <;> constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h10.1,h10.2]

set_option maxHeartbeats 3000000 in
/-- Analytic odd/even source boxes at fifteen for the inherited-debt circuit. -/
theorem divisorUnsignedDilationChannel_fifteen_debt_profile_boxes :
    (-0.286 ≤ divisorUnsignedDilationChannel 15 1-divisorUnsignedDilationChannel 15 3-
      divisorUnsignedDilationChannel 15 5-divisorUnsignedDilationChannel 15 7-
      divisorUnsignedDilationChannel 15 11-divisorUnsignedDilationChannel 15 13 ∧
      divisorUnsignedDilationChannel 15 1-divisorUnsignedDilationChannel 15 3-
      divisorUnsignedDilationChannel 15 5-divisorUnsignedDilationChannel 15 7-
      divisorUnsignedDilationChannel 15 11-divisorUnsignedDilationChannel 15 13 ≤ -0.283) ∧
    (0.055 ≤ -divisorUnsignedDilationChannel 15 2+divisorUnsignedDilationChannel 15 6+
      divisorUnsignedDilationChannel 15 10+divisorUnsignedDilationChannel 15 14 ∧
      -divisorUnsignedDilationChannel 15 2+divisorUnsignedDilationChannel 15 6+
      divisorUnsignedDilationChannel 15 10+divisorUnsignedDilationChannel 15 14 ≤ 0.058) := by
  have h1 := debt_channel_box (M:=15) (d:=1) (by omega) (by omega)
  have h2 := debt_channel_box (M:=15) (d:=2) (by omega) (by omega)
  have h3 := debt_channel_box (M:=15) (d:=3) (by omega) (by omega)
  have h5 := debt_channel_box (M:=15) (d:=5) (by omega) (by omega)
  have h6 := debt_channel_box (M:=15) (d:=6) (by omega) (by omega)
  have h7 := debt_channel_box (M:=15) (d:=7) (by omega) (by omega)
  have h10 := debt_channel_box (M:=15) (d:=10) (by omega) (by omega)
  have h11 := debt_channel_box (M:=15) (d:=11) (by omega) (by omega)
  have h13 := debt_channel_box (M:=15) (d:=13) (by omega) (by omega)
  have h14 := debt_channel_box (M:=15) (d:=14) (by omega) (by omega)
  norm_num [debtChannelLower,debtChannelUpper,Finset.sum_Icc_succ_top] at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14
  norm_num [termLower,termUpper,weightLower,weightUpper,defectLower,defectUpper,
    logLower,logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top] at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14
  constructor <;> constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h10.1,h10.2,h11.1,h11.2,h13.1,h13.2,h14.1,h14.2]
end RHTower

namespace RHTower
private lemma log_twentyThree_box : (3.135493:ℝ) ≤ Real.log 23 ∧ Real.log 23 ≤ 3.135495 := by
  have h := ratio_box (x:=(1/47:ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  have he : Real.log (24:ℝ)=3*Real.log 2+Real.log 3 := by
    rw [show (24:ℝ)=8*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),
      show Real.log (8:ℝ)=3*Real.log 2 by rw [show (8:ℝ)=2^(3 : ℕ) by norm_num,Real.log_pow]; norm_num]
  rw [Real.log_div (by norm_num) (by norm_num),he] at h
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9,Real.log_three_gt_d9,Real.log_three_lt_d9]

private lemma log_box_twentyFour {n : ℕ} (hn : n∈Icc 1 24) :
    logLower n ≤ Real.log n ∧ Real.log n ≤ logUpper n := by
  by_cases h21 : n ≤ 21
  · exact log_box (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,h21⟩)
  have he22 : Real.log (22:ℝ)=Real.log 2+Real.log 11 := by
    rw [show (22:ℝ)=2*11 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have he24 : Real.log (24:ℝ)=3*Real.log 2+Real.log 3 := by
    rw [show (24:ℝ)=8*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),
      show Real.log (8:ℝ)=3*Real.log 2 by rw [show (8:ℝ)=2^(3 : ℕ) by norm_num,Real.log_pow]; norm_num]
  have h11 := prime_log_boxes.2.1
  have h23 := log_twentyThree_box
  have hlo : 22 ≤ n := by omega
  have hhi := (mem_Icc.mp hn).2
  interval_cases n
  all_goals norm_num only [logLower,logUpper,Nat.cast_ofNat,he22,he24]
  all_goals constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9,Real.log_three_gt_d9,Real.log_three_lt_d9]

private lemma root_box_twentyFive {n : ℕ} (hn : n∈Icc 1 25) :
    rootLower n ≤ Real.sqrt n ∧ Real.sqrt n ≤ rootUpper n := by
  by_cases h22 : n ≤ 22
  · exact root_box (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,h22⟩)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  have hp := Real.sqrt_nonneg (n:ℝ)
  have hlo : 23 ≤ n := by omega
  have hhi := (mem_Icc.mp hn).2
  interval_cases n
  all_goals norm_num only [Nat.cast_ofNat] at hs hp ⊢
  all_goals norm_num [rootLower,rootUpper]
  all_goals constructor <;> nlinarith only [hs,hp]

private lemma defect_box_twentyFour {n : ℕ} (hn : n ≤ 24) :
    defectLower n ≤ primeFreeDivisorDefect n ∧ primeFreeDivisorDefect n ≤ defectUpper n := by
  have hl := sum_le_sum (fun k (hk : k∈Icc 1 n) =>
    (log_box_twentyFour (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩)).1)
  have hu := sum_le_sum (fun k (hk : k∈Icc 1 n) =>
    (log_box_twentyFour (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans hn⟩)).2)
  have gl := mul_le_mul_of_nonneg_right gamma_box.1 (Nat.cast_nonneg (α:=ℝ) n)
  have gu := mul_le_mul_of_nonneg_right gamma_box.2 (Nat.cast_nonneg (α:=ℝ) n)
  dsimp [defectLower,defectUpper,primeFreeDivisorDefect]
  constructor <;> linarith only [hl,hu,gl,gu]

private lemma term_box_twentyFour {k n : ℕ} (hk : k∈Icc 1 24) (hn : n ≤ 24) :
    termLower k n ≤ (Real.sqrt (k+1:ℕ)-Real.sqrt k)*primeFreeDivisorDefect n ∧
      (Real.sqrt (k+1:ℕ)-Real.sqrt k)*primeFreeDivisorDefect n ≤ termUpper k n := by
  have hk0 := (mem_Icc.mp hk).1
  have hk1 := (mem_Icc.mp hk).2
  have a := root_box_twentyFive (n:=k) (mem_Icc.mpr ⟨hk0,by omega⟩)
  have b := root_box_twentyFive (n:=k+1) (mem_Icc.mpr ⟨by omega,by omega⟩)
  apply product_box (sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)))
    (And.intro (by dsimp [weightLower]; linarith only [a.2,b.1])
      (by dsimp [weightUpper]; linarith only [a.1,b.2])) (defect_box_twentyFour hn)

private def twentyFiveLower (d : ℕ) : ℝ := ∑ k∈Icc d 24,termLower k (k/d)
private def twentyFiveUpper (d : ℕ) : ℝ := ∑ k∈Icc d 24,termUpper k (k/d)
private lemma twentyFive_channel_box {d : ℕ} (hd : 1 ≤ d) :
    twentyFiveLower d ≤ divisorUnsignedDilationChannel 25 d ∧
      divisorUnsignedDilationChannel 25 d ≤ twentyFiveUpper d := by
  have hlo := sum_le_sum (fun k (hk : k∈Icc d 24) =>
    (term_box_twentyFour (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,(mem_Icc.mp hk).2⟩)
      ((Nat.div_le_self k d).trans (mem_Icc.mp hk).2)).1)
  have hhi := sum_le_sum (fun k (hk : k∈Icc d 24) =>
    (term_box_twentyFour (mem_Icc.mpr ⟨hd.trans (mem_Icc.mp hk).1,(mem_Icc.mp hk).2⟩)
      ((Nat.div_le_self k d).trans (mem_Icc.mp hk).2)).2)
  exact ⟨by simpa [twentyFiveLower,divisorUnsignedDilationChannel] using hlo,
    by simpa [twentyFiveUpper,divisorUnsignedDilationChannel] using hhi⟩

set_option maxHeartbeats 3000000 in
/-- Analytic four-coordinate source bounds for the actual two-prime nonempty-energy trap at twenty-five. -/
theorem divisorUnsignedDilationChannel_twentyFive_profile_boxes :
    (-0.75 ≤ divisorUnsignedDilationChannel 25 1-divisorUnsignedDilationChannel 25 2-
      divisorUnsignedDilationChannel 25 7-divisorUnsignedDilationChannel 25 11-
      divisorUnsignedDilationChannel 25 13+divisorUnsignedDilationChannel 25 14-
      divisorUnsignedDilationChannel 25 17-divisorUnsignedDilationChannel 25 19+
      divisorUnsignedDilationChannel 25 22-divisorUnsignedDilationChannel 25 23 ∧
      divisorUnsignedDilationChannel 25 1-divisorUnsignedDilationChannel 25 2-
      divisorUnsignedDilationChannel 25 7-divisorUnsignedDilationChannel 25 11-
      divisorUnsignedDilationChannel 25 13+divisorUnsignedDilationChannel 25 14-
      divisorUnsignedDilationChannel 25 17-divisorUnsignedDilationChannel 25 19+
      divisorUnsignedDilationChannel 25 22-divisorUnsignedDilationChannel 25 23 ≤ -0.73) ∧
    (0.007 ≤ -divisorUnsignedDilationChannel 25 3+divisorUnsignedDilationChannel 25 6+
      divisorUnsignedDilationChannel 25 21 ∧
      -divisorUnsignedDilationChannel 25 3+divisorUnsignedDilationChannel 25 6+
      divisorUnsignedDilationChannel 25 21 ≤ 0.010) ∧
    (0.013 ≤ -divisorUnsignedDilationChannel 25 5+divisorUnsignedDilationChannel 25 10 ∧
      -divisorUnsignedDilationChannel 25 5+divisorUnsignedDilationChannel 25 10 ≤ 0.015) ∧
    (0.173 ≤ divisorUnsignedDilationChannel 25 15 ∧ divisorUnsignedDilationChannel 25 15 ≤ 0.175) := by
  have h1 := twentyFive_channel_box (d:=1) (by omega)
  have h2 := twentyFive_channel_box (d:=2) (by omega)
  have h3 := twentyFive_channel_box (d:=3) (by omega)
  have h5 := twentyFive_channel_box (d:=5) (by omega)
  have h6 := twentyFive_channel_box (d:=6) (by omega)
  have h7 := twentyFive_channel_box (d:=7) (by omega)
  have h10 := twentyFive_channel_box (d:=10) (by omega)
  have h11 := twentyFive_channel_box (d:=11) (by omega)
  have h13 := twentyFive_channel_box (d:=13) (by omega)
  have h14 := twentyFive_channel_box (d:=14) (by omega)
  have h15 := twentyFive_channel_box (d:=15) (by omega)
  have h17 := twentyFive_channel_box (d:=17) (by omega)
  have h19 := twentyFive_channel_box (d:=19) (by omega)
  have h21 := twentyFive_channel_box (d:=21) (by omega)
  have h22 := twentyFive_channel_box (d:=22) (by omega)
  have h23 := twentyFive_channel_box (d:=23) (by omega)
  norm_num [twentyFiveLower,twentyFiveUpper,Finset.sum_Icc_succ_top]
    at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14 h15 h17 h19 h21 h22 h23
  norm_num [termLower,termUpper,weightLower,weightUpper,defectLower,defectUpper,
    logLower,logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top]
    at h1 h2 h3 h5 h6 h7 h10 h11 h13 h14 h15 h17 h19 h21 h22 h23
  constructor
  · constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,h7.1,h7.2,h11.1,h11.2,h13.1,h13.2,
      h14.1,h14.2,h17.1,h17.2,h19.1,h19.2,h22.1,h22.2,h23.1,h23.2]
  constructor
  · constructor <;> linarith only [h3.1,h3.2,h6.1,h6.2,h21.1,h21.2]
  constructor
  · constructor <;> linarith only [h5.1,h5.2,h10.1,h10.2]
  · exact ⟨by linarith only [h15.1],by linarith only [h15.2]⟩

set_option maxHeartbeats 3000000 in
/-- A squarefree source subdiagonal already supplies four fifths of energy at cutoff twenty-five. -/
theorem sum_divisorUnsignedDilationChannel_twentyFive_sq_lower :
    (0.8:ℝ) ≤ ∑ d∈({1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23}:Finset ℕ),
      (divisorUnsignedDilationChannel 25 d)^(2 : ℕ) := by
  let active : Finset ℕ := {1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23}
  have hpos (d : ℕ) (hd : d∈active) : 1 ≤ d := by
    simp only [active,mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have hl (d : ℕ) (hd : d∈active) : 0 ≤ twentyFiveLower d := by
    simp only [active,mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [twentyFiveLower,Finset.sum_Icc_succ_top]
    all_goals norm_num [termLower,weightLower,weightUpper,defectLower,
      logLower,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  have hlo := sum_le_sum (fun d (hd : d∈active) =>
    mul_le_mul (twentyFive_channel_box (hpos d hd)).1 (twentyFive_channel_box (hpos d hd)).1
      (hl d hd) ((hl d hd).trans (twentyFive_channel_box (hpos d hd)).1))
  have hlower : (0.8:ℝ) ≤ ∑ d∈active,(twentyFiveLower d)^(2 : ℕ) := by
    norm_num [active,twentyFiveLower,Finset.sum_Icc_succ_top]
    norm_num [termLower,weightLower,weightUpper,defectLower,
      logLower,rootLower,rootUpper,Finset.sum_Icc_succ_top]
  simp only [← pow_two] at hlo
  exact hlower.trans hlo
set_option maxHeartbeats 1000000 in
/-- The actual remaining seven-fibre at cutoff twenty-five is strictly negative with analytic rational margins. -/
theorem divisorUnsignedDilationChannel_twentyFive_seven_leaf_box :
    (-0.020:ℝ) ≤ -divisorUnsignedDilationChannel 25 7+
      divisorUnsignedDilationChannel 25 14+divisorUnsignedDilationChannel 25 21 ∧
    -divisorUnsignedDilationChannel 25 7+
      divisorUnsignedDilationChannel 25 14+divisorUnsignedDilationChannel 25 21 ≤ -0.017 := by
  have h7 := twentyFive_channel_box (d:=7) (by omega)
  have h14 := twentyFive_channel_box (d:=14) (by omega)
  have h21 := twentyFive_channel_box (d:=21) (by omega)
  norm_num [twentyFiveLower,twentyFiveUpper,Finset.sum_Icc_succ_top] at h7 h14 h21
  norm_num [termLower,termUpper,weightLower,weightUpper,defectLower,defectUpper,
    logLower,logUpper,rootLower,rootUpper,Finset.sum_Icc_succ_top] at h7 h14 h21
  constructor <;> linarith only [h7.1,h7.2,h14.1,h14.2,h21.1,h21.2]

end RHTower
