import GaloisForLFunctions.RHTower.HarmonicGeometricSecondCorrection
import GaloisForLFunctions.RHTower.DivisorSmoothSquareBlockMean

/-!
# Signed mean ceiling for complete smooth divisor square blocks

Symmetric pairing around s(s+1), the geometric harmonic second correction,
and exact Stirling bounds show that every complete smooth block lies below
its exact limiting mean. The ceiling coefficient is optimal. Terminal partial
blocks and nonconstant Abel weights are not replaced by this block estimate.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma paired_log_bound {s j : ℝ} (hs : 1 ≤ s) (hj0 : 0 ≤ j) (hjs : j ≤ s) :
    let c := s*(s+1)
    (c-j+1/2)*Real.log ((c-j)/c)+(c+j+1/2)*Real.log ((c+j)/c) ≤ 
      j^2*(1/c-1/(2*c^2)+1/(6*c*s*(s+2))) := by
  let c := s*(s+1)
  have hs0 : 0 < s := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hjc : j < c := by dsimp [c]; nlinarith
  have hsq : j^2 ≤ s^2 := by nlinarith [mul_self_le_mul_self hj0 hjs]
  have hmin : 0 < c^2-s^2 := by dsimp [c]; nlinarith [sq_nonneg s]
  have hden : 0 < c^2-j^2 := by linarith
  let t := j/c
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t < 1 := by dsimp [t]; rwa [div_lt_one hc]
  have hpos : 0 < 1+t := by linarith
  have hneg : 0 < 1-t := by linarith
  have htden : 0 < 1-t^2 := by nlinarith
  have he := log_symmetric_entropy_le_quartic ht0 ht1
  have hl := Real.log_le_sub_one_of_pos htden
  have hlog : Real.log (1-t^2)=Real.log (1+t)+Real.log (1-t) := by
    rw [show 1-t^2=(1+t)*(1-t) by ring,Real.log_mul hpos.ne' hneg.ne']
  have hminus : (c-j)/c=1-t := by dsimp [t]; field_simp
  have hplus : (c+j)/c=1+t := by dsimp [t]; field_simp
  have hid : (c-j+1/2)*Real.log ((c-j)/c)+(c+j+1/2)*Real.log ((c+j)/c)=
      c*((1+t)*Real.log (1+t)+(1-t)*Real.log (1-t))+Real.log (1-t^2)/2 := by
    rw [hminus,hplus,hlog]
    dsimp [t]
    field_simp
    ring
  have hu := add_le_add (mul_le_mul_of_nonneg_left he hc.le)
    (div_le_div_of_nonneg_right hl (by norm_num : (0:ℝ) ≤ 2))
  have hpoly : c*(t^2+t^4/(6*(1-t^2)))+(1-t^2-1)/2=
      (c-1/2)*j^2/c^2+j^4/(6*c*(c^2-j^2)) := by
    have ht : 1-(j/c)^2=(c^2-j^2)/c^2 := by field_simp
    dsimp [t]
    rw [ht]
    field_simp [hc.ne',hden.ne']
    ring
  rw [hpoly] at hu
  have hb : j^2/(c^2-j^2) ≤ s^2/(c^2-s^2) :=
    (div_le_div_of_nonneg_right hsq hden.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg s) hmin (by linarith))
  have hr : s^2/(c^2-s^2)=1/(s*(s+2)) := by
    dsimp [c]
    have hd : (s*(s+1))^2-s^2=s^3*(s+2) := by ring
    rw [hd]
    field_simp
  rw [hr] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ j^2/(6*c) by positivity)
  have hpoly2 : j^2/(6*c)*(j^2/(c^2-j^2))=j^4/(6*c*(c^2-j^2)) := by field_simp [hc.ne',hden.ne']
  rw [hpoly2] at hb'
  change (c-j+1/2)*Real.log ((c-j)/c)+(c+j+1/2)*Real.log ((c+j)/c) ≤ _
  rw [hid]
  calc
    _  ≤  (c-1/2)*j^2/c^2+j^4/(6*c*(c^2-j^2)) := hu
    _  ≤  (c-1/2)*j^2/c^2+j^2/(6*c)*(1/(s*(s+2))) := add_le_add_right hb' _
    _ = _ := by field_simp; ring

private lemma smooth_upper {s n : ℕ} (hs : 1 ≤ s)
    (hn : n ∈ Ico (s*s) ((s+1)*(s+1))) :
    let c : ℝ := s*(s+1)
    divisorHyperbolaSmoothRemainder n ≤ 
      Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant+
        ((n:ℝ)+1/2)*Real.log ((n:ℝ)/c)-(n:ℝ)+c-
        (2*(n:ℝ)+1)*(1/(6*c)-1/(30*c^2))+1/(12*(n:ℝ)) := by
  have hs0 : (0:ℝ) < s := by positivity
  have hn1 : 1 ≤ n := by have := (mem_Ico.mp hn).1; nlinarith
  have hn0 : (0:ℝ) < n := by positivity
  have hc : 0 < (s:ℝ)*(s+1) := by positivity
  have hH := harmonic_mascheroni_geometric_lower_second hs
  rw [← Real.log_mul hs0.ne' (by positivity)] at hH
  have hHm := mul_le_mul_of_nonneg_left hH (show (0:ℝ) ≤ 2*n+1 by positivity)
  have hF := (sum_log_Icc_exact_stirling_bounds hn1).2
  have hr : Nat.sqrt n=s := (Nat.eq_sqrt.mpr (mem_Ico.mp hn)).symm
  dsimp only
  rw [Real.log_div hn0.ne' hc.ne']
  unfold divisorHyperbolaSmoothRemainder
  rw [hr]
  simp only [mul_assoc] at hHm ⊢
  nlinarith only [hHm,hF]

private lemma smooth_center_upper {s : ℕ} (hs : 1 ≤ s) :
    let c : ℝ := s*(s+1)
    divisorHyperbolaSmoothRemainder (s*(s+1)) ≤ 
      Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-
        (2*c+1)*(1/(6*c)-1/(30*c^2))+1/(12*(s:ℝ)^2) := by
  have hm : s*(s+1) ∈ Ico (s*s) ((s+1)*(s+1)) := mem_Ico.mpr ⟨by nlinarith,by nlinarith⟩
  have h := smooth_upper hs hm
  dsimp only at h ⊢
  have hc : (s:ℝ)*(s+1)≠0 := by positivity
  push_cast at h
  rw [div_self hc,Real.log_one,mul_zero] at h
  have hf : 1/(12*((s:ℝ)*(s+1))) ≤ 1/(12*(s:ℝ)^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  linarith only [h,hf]

private lemma smooth_pair_upper {s j : ℕ} (hs : 1 ≤ s) (hj : j ≤ s) :
    let c : ℝ := s*(s+1)
    divisorHyperbolaSmoothRemainder (s*(s+1)-j)+
      divisorHyperbolaSmoothRemainder (s*(s+1)+j) ≤ 
        2*(Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-
          (2*c+1)*(1/(6*c)-1/(30*c^2))+1/(12*(s:ℝ)^2))+
        (j:ℝ)^2*(1/c-1/(2*c^2)+1/(6*c*s*(s+2))) := by
  have hjc : j ≤ s*(s+1) := by nlinarith
  have hmul : s*(s+1)=s*s+s := by ring
  have hsub : s*(s+1)-j ≤ s*(s+1) := Nat.sub_le _ _
  have hl : s*(s+1)-j ∈ Ico (s*s) ((s+1)*(s+1)) := mem_Ico.mpr ⟨by omega,by nlinarith⟩
  have hr : s*(s+1)+j ∈ Ico (s*s) ((s+1)*(s+1)) := mem_Ico.mpr ⟨by nlinarith,by nlinarith⟩
  have hL := smooth_upper hs hl
  have hR := smooth_upper hs hr
  have hp := paired_log_bound (show (1:ℝ) ≤ s by exact_mod_cast hs)
    (Nat.cast_nonneg j) (show (j:ℝ) ≤ s by exact_mod_cast hj)
  have h0 : 0 < (s:ℝ)^2 := by positivity
  have hlow : (s:ℝ)^2 ≤ (s*(s+1)-j:ℕ) := by rw [pow_two]; exact_mod_cast (mem_Ico.mp hl).1
  have hhigh : (s:ℝ)^2 ≤ (s*(s+1)+j:ℕ) := by rw [pow_two]; exact_mod_cast (mem_Ico.mp hr).1
  have hfracL := one_div_le_one_div_of_le (show (0:ℝ) < 12*(s:ℝ)^2 by positivity)
    (show 12*(s:ℝ)^2 ≤ 12*(s*(s+1)-j:ℕ) by nlinarith)
  have hfracR := one_div_le_one_div_of_le (show (0:ℝ) < 12*(s:ℝ)^2 by positivity)
    (show 12*(s:ℝ)^2 ≤ 12*(s*(s+1)+j:ℕ) by nlinarith)
  dsimp only at hL hR hp ⊢
  rw [Nat.cast_sub hjc] at hL hfracL
  push_cast at hL hR hfracL hfracR
  nlinarith only [hL,hR,hp,hfracL,hfracR]

private lemma sum_symmetric (f : ℕ → ℝ) {c s : ℕ} (hs : s ≤ c) :
    (∑ k ∈ Ico (c-s) (c+s+1),f k)=f c+∑ j ∈ Icc 1 s,(f (c-j)+f (c+j)) := by
  have hleft := sum_Ico_reflect f 1 (m := s+1) (n := c) (by omega)
  have hright := sum_Ico_add f 1 (s+1) c
  have he1 : c+1-(s+1)=c-s := by omega
  have he2 : c+1-1=c := by omega
  rw [he1,he2] at hleft
  rw [show s+1+c=c+s+1 by omega,show 1+c=c+1 by omega] at hright
  rw [← sum_Ico_consecutive (show c-s ≤ c by omega) (show c ≤ c+s+1 by omega) (f := f)]
  rw [← sum_Ico_consecutive (show c ≤ c+1 by omega) (show c+1 ≤ c+s+1 by omega) (f := f)]
  rw [Nat.Ico_succ_singleton,sum_singleton,← hleft,← hright,← Ico_add_one_right_eq_Icc,sum_add_distrib]
  ring

private lemma sum_sq (s : ℕ) :
    (∑ j ∈ Icc 1 s,(j:ℝ)^2)=(s:ℝ)*(s+1)*(2*s+1)/6 := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_Icc_succ_top (by omega : 1 ≤ s+1),ih]; push_cast; ring

private lemma correction_nonpos {s : ℝ} (hs : 2 ≤ s) :
    let c := s*(s+1);
    -1/(4*c)+(2*c+1)/(30*c^2)+1/(12*s^2)+1/(36*s*(s+2)) ≤ 0 := by
  have hs0 : 0 < s := by linarith
  have ht : 0 ≤ s-2 := by linarith
  dsimp only
  have he : -1/(4*(s*(s+1)))+(2*(s*(s+1))+1)/(30*(s*(s+1))^2)+
      1/(12*s^2)+1/(36*s*(s+2))=
      -(13*(s-2)^3+107*(s-2)^2+252*(s-2)+138)/(180*s^2*(s+1)^2*(s+2)) := by
    field_simp
    ring
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (by positivity)
  · positivity

private lemma block_upper_of_two {s : ℕ} (hs : 2 ≤ s) :
    (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),divisorHyperbolaSmoothRemainder n) ≤ 
      (2*(s:ℝ)+1)*divisorHyperbolaSmoothMean := by
  have hs1 : 1 ≤ s := by omega
  have hjc : s ≤ s*(s+1) := by nlinarith
  have ha : s*(s+1)-s=s*s := by
    have : s*(s+1)=s*s+s := by ring
    omega
  have hb : s*(s+1)+s+1=(s+1)*(s+1) := by ring
  rw [← ha,← hb,sum_symmetric _ hjc]
  have hpair := sum_le_sum (fun j (hj : j ∈ Icc 1 s) => smooth_pair_upper hs1 (mem_Icc.mp hj).2)
  have hcenter := smooth_center_upper hs1
  dsimp only at hpair hcenter
  simp only [sum_add_distrib,sum_const,← sum_mul,sum_sq,
    Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hpair
  rw [sum_add_distrib]
  have hsum := add_le_add hcenter hpair
  have hc := correction_nonpos (show (2:ℝ) ≤ s by exact_mod_cast hs)
  have hmul := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 2*s+1 by positivity)
  dsimp [divisorHyperbolaSmoothMean]
  have hs0 : (0:ℝ) < s := by positivity
  have he : (2*(s:ℝ)+1)*(Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-
      (2*(s*(s+1))+1)*(1/(6*(s*(s+1)))-1/(30*(s*(s+1))^2))+1/(12*s^2))+
      ((s:ℝ)*(s+1)*(2*s+1)/6)*(1/(s*(s+1))-1/(2*(s*(s+1))^2)+1/(6*(s*(s+1))*s*(s+2))) =
      (2*s+1)*(Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/6)+
      (2*s+1)*(-1/(4*(s*(s+1)))+(2*(s*(s+1))+1)/(30*(s*(s+1))^2)+1/(12*s^2)+1/(36*s*(s+2))) := by
    field_simp
    ring
  nlinarith only [hsum,hmul,he]

/-- Every complete smooth divisor square block lies below its exact mean,
with no additive error. -/
theorem sum_divisorHyperbolaSmooth_square_block_le_mean {s : ℕ} (hs : 1 ≤ s) :
    (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),divisorHyperbolaSmoothRemainder n) ≤
      (2*(s:ℝ)+1)*divisorHyperbolaSmoothMean := by
  by_cases hs2 : 2 ≤ s
  · exact block_upper_of_two hs2
  have he : s=1 := by omega
  subst s
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<6)
    (by linarith [Real.pi_gt_three] : (6:ℝ) ≤ 2*Real.pi)
  have h6 : Real.log (6:ℝ)=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  rw [h6] at hlog
  norm_num [divisorHyperbolaSmoothRemainder,divisorHyperbolaSmoothMean,
    Finset.sum_Ico_succ_top,Finset.sum_Icc_succ_top,harmonic,Finset.sum_range_succ,h6]
  linarith only [hg,hlog,Real.log_two_lt_d9,Real.log_three_gt_d9]

/-- The signed square-block ceiling has the smallest possible uniform
coefficient. Its optimality is forced by the existing exact block mean. -/
theorem sum_divisorHyperbolaSmooth_square_block_ceiling_iff (C : ℝ) :
    (∀ s : ℕ, 1 ≤ s →
      (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),divisorHyperbolaSmoothRemainder n) ≤
        (2*(s:ℝ)+1)*C) ↔ divisorHyperbolaSmoothMean ≤ C := by
  constructor
  · intro h
    by_contra hC
    have hd : 0<divisorHyperbolaSmoothMean-C := by linarith
    obtain ⟨s,hs⟩ := exists_nat_gt ((15:ℝ)/(divisorHyperbolaSmoothMean-C)+1)
    have hsR : (1:ℝ)<s := by have := div_pos (by norm_num : (0:ℝ)<15) hd; linarith
    have hs1 : 1 ≤ s := by exact_mod_cast hsR.le
    have hsd : (15:ℝ)<(s:ℝ)*(divisorHyperbolaSmoothMean-C) :=
      (div_lt_iff₀ hd).mp (by linarith only [hs])
    have hlow := (abs_le.mp (sum_divisorHyperbolaSmooth_square_block_mean_error hs1)).1
    have hhigh := h s hs1
    have hcard : (Ico (s*s) ((s+1)*(s+1))).card=2*s+1 := by
      rw [Nat.card_Ico]
      have : (s+1)*(s+1)=s*s+(2*s+1) := by ring
      omega
    rw [sum_sub_distrib,sum_const,hcard,nsmul_eq_mul] at hlow
    push_cast at hlow
    nlinarith only [hlow,hhigh,hsd,hd]
  · intro hC s hs
    exact (sum_divisorHyperbolaSmooth_square_block_le_mean hs).trans
      (mul_le_mul_of_nonneg_left hC (by positivity))

end RHTower
