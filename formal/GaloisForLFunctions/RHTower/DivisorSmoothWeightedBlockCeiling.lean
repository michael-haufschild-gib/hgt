import GaloisForLFunctions.RHTower.DivisorSmoothSignedBlockCeiling
import GaloisForLFunctions.RHTower.DivisorSmoothBlockOrientation
import GaloisForLFunctions.RHTower.SquareBlockSqrtClockMoment

/-!
# Exact smooth-block ceiling under the Abel clock

Rightward source orientation, the explicit geometric quadratic source majorant,
and the clock's excess quadratic moment retain the exact block mean under the
varying square-root weights. Analytic bounds settle the initial block.
-/

noncomputable section
open Finset HTGeometry
namespace RHTower

private lemma sum_symmetric (f : ℕ → ℝ) {c s : ℕ} (hs : s ≤ c) :
    (∑ k ∈ Ico (c-s) (c+s+1),f k)=f c+∑ j ∈ Icc 1 s,(f (c-j)+f (c+j)) := by
  have hleft := sum_Ico_reflect f 1 (m := s+1) (n := c) (by omega)
  have hright := sum_Ico_add f 1 (s+1) c
  rw [show c+1-(s+1)=c-s by omega,show c+1-1=c by omega] at hleft
  rw [show s+1+c=c+s+1 by omega,show 1+c=c+1 by omega] at hright
  rw [← sum_Ico_consecutive (show c-s ≤ c by omega) (show c ≤ c+s+1 by omega) (f := f)]
  rw [← sum_Ico_consecutive (show c ≤ c+1 by omega) (show c+1 ≤ c+s+1 by omega) (f := f)]
  rw [Nat.Ico_succ_singleton,sum_singleton,← hleft,← hright,← Ico_add_one_right_eq_Icc,sum_add_distrib]
  ring

private lemma weighted_correction_nonpos {s : ℝ} (hs : 2 ≤ s) :
    let c := s*(s+1);
    -1/(4*c)+(2*c+1)/(30*c^(2 : ℕ))+1/(12*s^(2 : ℕ))+1/(36*s*(s+2))+
      (1/c-1/(2*c^(2 : ℕ))+1/(6*c*s*(s+2)))/36 ≤ 0 := by
  have hs0 : 0<s := by linarith
  have ht : 0 ≤ s-2 := by linarith
  dsimp only
  have he : -1/(4*(s*(s+1)))+(2*(s*(s+1))+1)/(30*(s*(s+1))^(2 : ℕ))+
      1/(12*s^(2 : ℕ))+1/(36*s*(s+2))+
      (1/(s*(s+1))-1/(2*(s*(s+1))^(2 : ℕ))+1/(6*(s*(s+1))*s*(s+2)))/36 =
      -(48*(s-2)^(3 : ℕ)+372*(s-2)^(2 : ℕ)+742*(s-2)+153)/(1080*s^(2 : ℕ)*(s+1)^(2 : ℕ)*(s+2)) := by
    field_simp
    ring
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (by positivity)
  · positivity

private lemma weighted_block_of_two {s : ℕ} (hs : 2 ≤ s) :
    (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),divisorHyperbolaSmoothRemainder n*
      halfOrderAbelStep 0 n) ≤ divisorHyperbolaSmoothMean := by
  let C := s*(s+1)
  let c : ℝ := s*(s+1)
  let B := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-
    (2*c+1)*(1/(6*c)-1/(30*c^(2 : ℕ)))+1/(12*(s:ℝ)^(2 : ℕ))
  let A := 1/c-1/(2*c^(2 : ℕ))+1/(6*c*s*(s+2))
  let w := halfOrderAbelStep 0
  let q := fun n : ℕ => ((n:ℝ)-c)^(2 : ℕ)
  have hs1 : 1 ≤ s := by omega
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ)<s := by positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by
    have hh : 1/(2*c^(2 : ℕ)) ≤ 1/c := by
      apply one_div_le_one_div_of_le hc
      have hc1 : 1 ≤ c := by dsimp [c]; nlinarith only [hsR]
      nlinarith only [hc1]
    have hp : 0 ≤ 1/(6*c*s*(s+2)) := by positivity
    dsimp [A]
    linarith only [hh,hp]
  have hcs : s ≤ C := by dsimp [C]; nlinarith
  have ha : C-s=s*s := by
    have : C=s*s+s := by dsimp [C]; ring
    omega
  have hb : C+s+1=(s+1)*(s+1) := by dsimp [C]; ring
  have hpair (j : ℕ) (hj : j ≤ s) :
      divisorHyperbolaSmoothRemainder (C-j)*w (C-j)+
        divisorHyperbolaSmoothRemainder (C+j)*w (C+j) ≤
          B*(w (C-j)+w (C+j))+A/2*((j:ℝ)^(2 : ℕ)*w (C-j)+(j:ℝ)^(2 : ℕ)*w (C+j)) := by
    have hsource := divisorHyperbolaSmoothRemainder_reflection_le hs1 hj
    have hp := divisorHyperbolaSmoothRemainder_pair_le_geometric_quadratic hs1 hj
    change divisorHyperbolaSmoothRemainder (C-j) ≤ divisorHyperbolaSmoothRemainder (C+j) at hsource
    change divisorHyperbolaSmoothRemainder (C-j)+divisorHyperbolaSmoothRemainder (C+j) ≤ 2*B+(j:ℝ)^(2 : ℕ)*A at hp
    have hw := halfOrderAbelStep_antitone 0 (show C-j ≤ C+j by omega)
    have hprod := mul_nonneg (sub_nonneg.mpr hsource) (sub_nonneg.mpr hw)
    have hpmul := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ (w (C-j)+w (C+j))/2 by
        have h1 := halfOrderAbelStep_nonneg 0 (C-j)
        have h2 := halfOrderAbelStep_nonneg 0 (C+j)
        dsimp [w]
        positivity)
    change 0 ≤ (divisorHyperbolaSmoothRemainder (C+j)-divisorHyperbolaSmoothRemainder (C-j))*
      (w (C-j)-w (C+j)) at hprod
    nlinarith only [hprod,hpmul]
  have hcenter : divisorHyperbolaSmoothRemainder C*w C ≤ B*w C := by
    have h := divisorHyperbolaSmoothRemainder_pair_le_geometric_quadratic hs1 (show 0 ≤ s by omega)
    norm_num only [Nat.sub_zero,Nat.add_zero,Nat.cast_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,add_zero] at h
    change divisorHyperbolaSmoothRemainder C+divisorHyperbolaSmoothRemainder C ≤ 2*B at h
    have hc0 : divisorHyperbolaSmoothRemainder C ≤ B := by linarith only [h]
    exact mul_le_mul_of_nonneg_right hc0 (halfOrderAbelStep_nonneg 0 C)
  have hm (j : ℕ) (hj : j ≤ s) :
      q (C-j)=(j:ℝ)^(2 : ℕ) ∧ q (C+j)=(j:ℝ)^(2 : ℕ) := by
    have hjc : j ≤ C := hj.trans hcs
    dsimp [q]
    rw [Nat.cast_sub hjc]
    dsimp [C,c]
    push_cast
    constructor <;> ring
  have hq0 : q C=0 := by dsimp [q,C,c]; push_cast; ring
  have hmajor : (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),divisorHyperbolaSmoothRemainder n*w n) ≤
      B*(∑ n ∈ Ico (s*s) ((s+1)*(s+1)),w n)+
        A/2*(∑ n ∈ Ico (s*s) ((s+1)*(s+1)),q n*w n) := by
    rw [← ha,← hb,sum_symmetric _ hcs,sum_symmetric _ hcs,sum_symmetric _ hcs]
    have hh := sum_le_sum (fun j (hj : j ∈ Icc 1 s) => hpair j (mem_Icc.mp hj).2)
    have hq : (∑ j ∈ Icc 1 s,(q (C-j)*w (C-j)+q (C+j)*w (C+j)))=
        ∑ j ∈ Icc 1 s,((j:ℝ)^(2 : ℕ)*w (C-j)+(j:ℝ)^(2 : ℕ)*w (C+j)) := by
      exact sum_congr rfl (fun j hj => by rw [(hm j (mem_Icc.mp hj).2).1,(hm j (mem_Icc.mp hj).2).2])
    rw [hq0,zero_mul,hq]
    simp only [sum_add_distrib,← mul_sum] at hh
    simp only [sum_add_distrib]
    nlinarith only [hh,hcenter]
  have hw : (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),w n)=1 := by
    have htel (N : ℕ) : (∑ n ∈ range N,w n)=Real.sqrt N := by
      simpa only [w,halfOrderAbelStep,Nat.zero_add,Nat.cast_zero,Real.sqrt_zero,sub_zero]
        using Finset.sum_range_sub (fun n : ℕ => Real.sqrt n) N
    rw [sum_Ico_eq_sub _ (show s*s ≤ (s+1)*(s+1) by nlinarith),htel,htel]
    push_cast
    rw [← pow_two,← pow_two,Real.sqrt_sq (by positivity),Real.sqrt_sq (by positivity)]
    ring
  have hmoment := sum_square_block_sqrtStep_quadratic_le hs
  have hmoment' : (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),q n*w n) ≤ c/3+1/18 := by
    simpa only [q,w,halfOrderAbelStep,Nat.zero_add,c] using hmoment
  have hweighted := mul_le_mul_of_nonneg_left hmoment' (show 0 ≤ A/2 by positivity)
  rw [hw,mul_one] at hmajor
  have hcor := weighted_correction_nonpos hsR
  have he : B+A/2*(c/3+1/18)=divisorHyperbolaSmoothMean+
      (-1/(4*c)+(2*c+1)/(30*c^(2 : ℕ))+1/(12*(s:ℝ)^(2 : ℕ))+1/(36*(s:ℝ)*(s+2))+A/36) := by
    dsimp [B,A,c,divisorHyperbolaSmoothMean]
    field_simp
    ring
  have hsum : B+A/2*(c/3+1/18) ≤ divisorHyperbolaSmoothMean := by
    rw [he]
    change _ ≤ 0 at hcor
    dsimp [c,A]
    linarith only [hcor]
  exact hmajor.trans ((add_le_add_right hweighted B).trans hsum)

/-- Every complete smooth divisor block retains its exact mean ceiling
under the actual varying square-root Abel clock. -/
theorem sum_divisorHyperbolaSmooth_square_block_mul_sqrtStep_le_mean
    {s : ℕ} (hs : 1 ≤ s) :
    (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),divisorHyperbolaSmoothRemainder n*
      halfOrderAbelStep 0 n) ≤ divisorHyperbolaSmoothMean := by
  by_cases hs2 : 2 ≤ s
  · exact weighted_block_of_two hs2
  have he : s=1 := by omega
  subst s
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have h6 : Real.log (6:ℝ)=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have h1 : divisorHyperbolaSmoothRemainder 1 ≤ (4/25:ℝ) := by
    norm_num [divisorHyperbolaSmoothRemainder,harmonic,Finset.sum_Icc_succ_top,Finset.sum_range_succ]
    linarith only [hg]
  have h2 : divisorHyperbolaSmoothRemainder 2 ≤ (1/100:ℝ) := by
    norm_num [divisorHyperbolaSmoothRemainder,harmonic,Finset.sum_Icc_succ_top,Finset.sum_range_succ]
    linarith only [hg,Real.log_two_lt_d9]
  have h3 : divisorHyperbolaSmoothRemainder 3 ≤ (13/50:ℝ) := by
    norm_num [divisorHyperbolaSmoothRemainder,harmonic,Finset.sum_Icc_succ_top,Finset.sum_range_succ,h6]
    linarith only [hg,Real.log_two_lt_d9,Real.log_three_lt_d9]
  have hw1 : halfOrderAbelStep 0 1 ≤ (1/2:ℝ) := by
    norm_num [halfOrderAbelStep]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  have hw2 : halfOrderAbelStep 0 2 ≤ (1/2:ℝ) :=
    (halfOrderAbelStep_antitone 0 (by omega : (1:ℕ) ≤ 2)).trans hw1
  have hw3 : halfOrderAbelStep 0 3 ≤ (3/10:ℝ) := by
    norm_num [halfOrderAbelStep]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]
  have hh1 := mul_le_mul h1 hw1 (halfOrderAbelStep_nonneg 0 1) (by norm_num : (0:ℝ) ≤ 4/25)
  have hh2 := mul_le_mul h2 hw2 (halfOrderAbelStep_nonneg 0 2) (by norm_num : (0:ℝ) ≤ 1/100)
  have hh3 := mul_le_mul h3 hw3 (halfOrderAbelStep_nonneg 0 3) (by norm_num : (0:ℝ) ≤ 13/50)
  norm_num [Finset.sum_Ico_succ_top]
  linarith only [hh1,hh2,hh3,divisorHyperbolaSmoothMean_gt_one_sixth]

end RHTower
