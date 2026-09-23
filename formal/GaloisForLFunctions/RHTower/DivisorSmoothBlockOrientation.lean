import GaloisForLFunctions.RHTower.DivisorHyperbolaSharpBlocks

/-!
# Rightward orientation of smooth divisor square blocks

The exact difference of reflected smooth source values is a paired logarithmic
product minus a harmonic slope. The geometric harmonic upper correction and
an analytic quadratic logarithm lower bound give its nonnegative sign.
-/

noncomputable section
open Finset
namespace RHTower

private lemma log_one_add_lower {x : ℝ} (hx : 0 ≤ x) :
    x-x^(2 : ℕ)/2 ≤ Real.log (1+x) := by
  have h := Real.le_log_one_add_of_nonneg hx
  have hp : 0<x+2 := by linarith
  have he : 2*x/(x+2)-(x-x^(2 : ℕ)/2)=x^(3 : ℕ)/(2*(x+2)) := by field_simp; ring
  have hn : 0 ≤ x^(3 : ℕ)/(2*(x+2)) := by positivity
  linarith only [h,he,hn]

private def profile (s n : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 n,Real.log m)-(2*(n:ℝ)+1)*((harmonic s:ℚ):ℝ)+
    (s:ℝ)^(2 : ℕ)+s+2*Real.eulerMascheroniConstant*n

private lemma profile_step (s n : ℕ) :
    profile s (n+1)-profile s n=
      Real.log (n+1:ℕ)-2*(((harmonic s:ℚ):ℝ)-Real.eulerMascheroniConstant) := by
  unfold profile
  rw [sum_Icc_succ_top (by omega : 1 ≤ n+1)]
  push_cast
  ring

private lemma profile_pair_difference {s j : ℕ} (hj : j ≤ s) :
    profile s (s*(s+1)+j)-profile s (s*(s+1)-j)=
      (∑ i ∈ Icc 1 j,(Real.log (s*(s+1)-i+1:ℕ)+Real.log (s*(s+1)+i:ℕ)))-
        4*(j:ℝ)*(((harmonic s:ℚ):ℝ)-Real.eulerMascheroniConstant) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjc : j+1 ≤ s*(s+1) := by nlinarith
    have hi := ih (by omega : j ≤ s)
    have hp := profile_step s (s*(s+1)+j)
    have hm := profile_step s (s*(s+1)-(j+1))
    rw [show s*(s+1)-(j+1)+1=s*(s+1)-j by omega] at hm
    rw [sum_Icc_succ_top (by omega : 1 ≤ j+1)]
    rw [show s*(s+1)-(j+1)+1=s*(s+1)-j by omega]
    simp only [Nat.cast_add,Nat.cast_one] at hi hp hm ⊢
    rw [show s*(s+1)+(j+1)=s*(s+1)+j+1 by omega]
    simp only [add_assoc] at hi hp hm ⊢
    linarith only [hi,hp,hm]

private lemma log_pair_lower {s i : ℕ} (hs : 1 ≤ s) (hi1 : 1 ≤ i) (his : i ≤ s) :
    let c : ℝ := s*(s+1)
    2*Real.log c+(1-1/(2*c))*((c-(i:ℝ)*((i:ℝ)-1))/c^(2 : ℕ)) ≤
      Real.log (s*(s+1)-i+1:ℕ)+Real.log (s*(s+1)+i:ℕ) := by
  let c : ℝ := s*(s+1)
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hiR : (1:ℝ) ≤ i := by exact_mod_cast hi1
  have hisR : (i:ℝ) ≤ s := by exact_mod_cast his
  have hc : 0<c := by dsimp [c]; positivity
  have hci : 0<c-(i:ℝ)*((i:ℝ)-1) := by
    dsimp [c]
    nlinarith [mul_self_le_mul_self (show (0:ℝ) ≤ i by positivity) hisR]
  let x := (c-(i:ℝ)*((i:ℝ)-1))/c^(2 : ℕ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxc : x ≤ 1/c := by
    dsimp [x]
    rw [div_le_div_iff₀ (sq_pos_of_pos hc) hc]
    nlinarith only [hc,hiR,mul_nonneg hc.le (show (0:ℝ) ≤ (i:ℝ)*((i:ℝ)-1) by positivity)]
  have hlog := log_one_add_lower hx
  have hmul := mul_le_mul_of_nonneg_left hxc hx
  have hlow : (1-1/(2*c))*x ≤ Real.log (1+x) := by
    have he : (1-1/(2*c))*x=x-x*(1/c)/2 := by ring
    rw [he]
    nlinarith only [hlog,hmul]
  have hjc : i ≤ s*(s+1) := by nlinarith
  have hm : (0:ℝ)<c-(i:ℝ)+1 := by dsimp [c]; nlinarith
  have hp : (0:ℝ)<c+(i:ℝ) := by positivity
  have hid : (c-(i:ℝ)+1)*(c+(i:ℝ))=c^(2 : ℕ)*(1+x) := by
    dsimp [x]
    field_simp
    ring
  have he : Real.log (s*(s+1)-i+1:ℕ)+Real.log (s*(s+1)+i:ℕ)=
      2*Real.log c+Real.log (1+x) := by
    rw [Nat.cast_add,Nat.cast_sub hjc]
    push_cast
    change Real.log (c-(i:ℝ)+1)+Real.log (c+(i:ℝ))=_
    rw [← Real.log_mul hm.ne' hp.ne',hid,
      Real.log_mul (pow_ne_zero _ hc.ne') (by positivity),Real.log_pow]
    norm_num
  dsimp only
  rw [he]
  exact add_le_add_right hlow _

private lemma sum_i_mul_sub_one (j : ℕ) :
    (∑ i ∈ Icc 1 j,(i:ℝ)*((i:ℝ)-1))=(j:ℝ)*((j:ℝ)^(2 : ℕ)-1)/3 := by
  induction j with
  | zero => simp
  | succ j ih => rw [sum_Icc_succ_top (by omega : 1 ≤ j+1),ih]; push_cast; ring

/-- The literal smooth source is oriented to the right within each symmetric
square-block pair. Decreasing Abel weights therefore favor its smaller member. -/
theorem divisorHyperbolaSmoothRemainder_reflection_le {s j : ℕ}
    (hs : 1 ≤ s) (hj : j ≤ s) :
    divisorHyperbolaSmoothRemainder (s*(s+1)-j) ≤
      divisorHyperbolaSmoothRemainder (s*(s+1)+j) := by
  let c : ℝ := s*(s+1)
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hjR : (j:ℝ) ≤ s := by exact_mod_cast hj
  have hs0 : (0:ℝ)<s := by positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hcor : 0 ≤ 1-1/(2*c) := by
    rw [sub_nonneg,div_le_one (by positivity)]
    dsimp [c]
    nlinarith
  have hsum := sum_le_sum (fun i (hi : i ∈ Icc 1 j) =>
    log_pair_lower hs (mem_Icc.mp hi).1 ((mem_Icc.mp hi).2.trans hj))
  simp only [sum_add_distrib,sum_const,← mul_sum,← sum_div,sum_sub_distrib,
    Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,sum_i_mul_sub_one] at hsum
  change (j:ℝ)*(2*Real.log c)+(1-1/(2*c))*
    (((j:ℝ)*c-(j:ℝ)*((j:ℝ)^(2 : ℕ)-1)/3)/c^(2 : ℕ)) ≤ _ at hsum
  have hsq : (j:ℝ)^(2 : ℕ) ≤ (s:ℝ)^(2 : ℕ) := by nlinarith [Nat.cast_nonneg (α:=ℝ) j]
  have hpoly : (j:ℝ)/c-(j:ℝ)*((s:ℝ)^(2 : ℕ)-1)/(3*c^(2 : ℕ)) ≤
      ((j:ℝ)*c-(j:ℝ)*((j:ℝ)^(2 : ℕ)-1)/3)/c^(2 : ℕ) := by
    rw [le_div_iff₀ (sq_pos_of_pos hc)]
    field_simp
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) j) (sub_nonneg.mpr hsq)]
  have hcorr := mul_le_mul_of_nonneg_left hpoly hcor
  have he : (1-1/(2*c))*((j:ℝ)/c-(j:ℝ)*((s:ℝ)^(2 : ℕ)-1)/(3*c^(2 : ℕ)))=
      2*(j:ℝ)/(3*c)+(j:ℝ)*(2*(s:ℝ)^(2 : ℕ)-1)/(6*c^(2 : ℕ)*s) := by
    dsimp [c]
    field_simp
    ring
  rw [he] at hcorr
  have hpos : 0 ≤ (j:ℝ)*(2*(s:ℝ)^(2 : ℕ)-1)/(6*c^(2 : ℕ)*s) := by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg j); nlinarith
    · positivity
  have hH := (harmonic_mascheroni_geometric_bounds hs).2
  rw [← Real.log_mul hs0.ne' (by positivity)] at hH
  have hHmul := mul_le_mul_of_nonneg_left hH (show (0:ℝ) ≤ 4*j by positivity)
  have hconst : 4*(j:ℝ)*(1/(6*(s:ℝ)*(s+1)))=2*(j:ℝ)/(3*c) := by
    dsimp [c]
    field_simp
    ring
  rw [hconst] at hHmul
  have hid := profile_pair_difference hj
  have hleft : Nat.sqrt (s*(s+1)-j)=s := by
    apply (Nat.eq_sqrt.mpr _).symm
    have he : s*(s+1)=s*s+s := by ring
    have hh := Nat.sub_le (s*(s+1)) j
    exact ⟨by omega,by nlinarith⟩
  have hright : Nat.sqrt (s*(s+1)+j)=s :=
    (Nat.eq_sqrt.mpr ⟨by nlinarith,by nlinarith⟩).symm
  have hdiff : 0 ≤ profile s (s*(s+1)+j)-profile s (s*(s+1)-j) := by
    rw [hid,sum_add_distrib]
    dsimp [c] at hsum hcorr hpos
    simp only [mul_assoc,div_eq_mul_inv] at hHmul hsum hcorr hpos ⊢
    nlinarith only [hHmul,hsum,hcorr,hpos]
  unfold divisorHyperbolaSmoothRemainder
  rw [hleft,hright]
  exact sub_nonneg.mp hdiff

end RHTower
