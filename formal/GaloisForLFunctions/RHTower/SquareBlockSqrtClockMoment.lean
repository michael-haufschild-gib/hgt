import GaloisForLFunctions.RHTower.SymmetricSqrtClockBounds
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Quadratic square-block moment of the square-root clock

The symmetric clock slope and the exact finite covariance identity retain
both second and fourth uniform block moments. The resulting excess over the
uniform quadratic mean is at most one eighteenth on every block from two.
-/

noncomputable section
open Finset
namespace RHTower

private lemma covariance_identity {ι : Type*} (S : Finset ι) (q w : ι → ℝ) :
    (∑ i ∈ S,∑ j ∈ S,(q i-q j)*(w i-w j))=
      2*(S.card:ℝ)*(∑ i ∈ S,q i*w i)-2*(∑ i ∈ S,q i)*(∑ i ∈ S,w i) := by
  simp_rw [sub_mul,mul_sub,sum_sub_distrib]
  simp only [sum_const,nsmul_eq_mul,← mul_sum,← sum_mul]
  ring

private lemma covariance_bound {ι : Type*} (S : Finset ι) (q w : ι → ℝ) (L : ℝ)
    (h : ∀ i ∈ S,∀ j ∈ S,(q i-q j)*(w i-w j) ≤ L*(q i-q j)^(2 : ℕ)) :
    (S.card:ℝ)*(∑ i ∈ S,q i*w i)-(∑ i ∈ S,q i)*(∑ i ∈ S,w i) ≤
      L*((S.card:ℝ)*(∑ i ∈ S,(q i)^(2 : ℕ))-(∑ i ∈ S,q i)^(2 : ℕ)) := by
  have hh := sum_le_sum (fun i hi => sum_le_sum (fun j hj => h i hi j hj))
  simp_rw [← mul_sum,pow_two] at hh
  rw [covariance_identity,covariance_identity] at hh
  simp only [pow_two]
  nlinarith only [hh]

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

private lemma sum_sq (s : ℕ) :
    (∑ j ∈ Icc 1 s,(j:ℝ)^(2 : ℕ))=(s:ℝ)*(s+1)*(2*s+1)/6 := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_Icc_succ_top (by omega : 1 ≤ s+1),ih]; push_cast; ring

private lemma sum_fourth (s : ℕ) :
    (∑ j ∈ Icc 1 s,(j:ℝ)^(4 : ℕ))=(s:ℝ)*(s+1)*(2*s+1)*(3*s^(2 : ℕ)+3*s-1)/30 := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_Icc_succ_top (by omega : 1 ≤ s+1),ih]; push_cast; ring

private lemma sum_block_moments (s : ℕ) :
    (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),((n:ℝ)-s*(s+1))^(2 : ℕ))=
      (s:ℝ)*(s+1)*(2*s+1)/3 ∧
    (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),((n:ℝ)-s*(s+1))^(4 : ℕ))=
      (s:ℝ)*(s+1)*(2*s+1)*(3*(s*(s+1))-1)/15 := by
  have hcs : s ≤ s*(s+1) := by nlinarith
  have ha : s*(s+1)-s=s*s := by
    have : s*(s+1)=s*s+s := by ring
    omega
  have hb : s*(s+1)+s+1=(s+1)*(s+1) := by ring
  have hh (k : ℕ) :
      (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),((n:ℝ)-s*(s+1))^(2*k))=
        0^(2*k)+2*∑ j ∈ Icc 1 s,(j:ℝ)^(2*k) := by
    rw [← ha,← hb,sum_symmetric _ hcs]
    have hc : ((s*(s+1):ℕ):ℝ)-(s:ℝ)*(s+1)=0 := by push_cast; ring
    rw [hc]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjc : j ≤ s*(s+1) := (mem_Icc.mp hj).2.trans hcs
    rw [Nat.cast_sub hjc]
    push_cast
    rw [show (s:ℝ)*(s+1)-j-s*(s+1)=-(j:ℝ) by ring,
      show (s:ℝ)*(s+1)+j-s*(s+1)=(j:ℝ) by ring,Even.neg_pow (even_two_mul k)]
    ring
  have h2 := hh 1
  have h4 := hh 2
  norm_num at h2 h4
  rw [h2,h4,sum_sq,sum_fourth]
  constructor <;> ring

private def clock (n : ℕ) : ℝ := Real.sqrt (n+1:ℕ)-Real.sqrt n

/-- The literal square-root clock has uniformly bounded excess quadratic
moment on every complete block from the second onward. -/
theorem sum_square_block_sqrtStep_quadratic_le {s : ℕ} (hs : 2 ≤ s) :
    (∑ n ∈ Ico (s*s) ((s+1)*(s+1)),((n:ℝ)-s*(s+1))^(2 : ℕ)*
      (Real.sqrt (n+1:ℕ)-Real.sqrt n)) ≤ (s:ℝ)*(s+1)/3+1/18 := by
  let C := s*(s+1)
  let c : ℝ := C
  let S := Ico (s*s) ((s+1)*(s+1))
  let q := fun n : ℕ => ((n:ℝ)-c)^(2 : ℕ)
  let W := fun n : ℕ => (clock n+clock (2*C-n))/2
  let v := fun t : ℝ => ((Real.sqrt (c-t+1)-Real.sqrt (c-t))+
    (Real.sqrt (c+t+1)-Real.sqrt (c+t)))/2
  let L := c^(-(5:ℝ)/2)/4
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hc : 0<c := by dsimp [c,C]; positivity
  have hcs : s ≤ C := by dsimp [C]; nlinarith
  have hCe : C=s*s+s := by dsimp [C]; ring
  have ha : C-s=s*s := by omega
  have hb : C+s+1=(s+1)*(s+1) := by dsimp [C]; ring
  have hn (n : ℕ) (hn : n ∈ S) : n ≤ 2*C ∧ |(n:ℝ)-c| ≤ s := by
    obtain ⟨hn0,hn1⟩ := mem_Ico.mp hn
    have hn2 : n ≤ s*s+2*s := by nlinarith
    constructor
    · omega
    · rw [abs_le]
      have hlo : (s:ℝ)^(2 : ℕ) ≤ n := by rw [pow_two]; exact_mod_cast hn0
      have hhi : (n:ℝ) ≤ (s:ℝ)^(2 : ℕ)+2*s := by rw [pow_two]; exact_mod_cast hn2
      dsimp [c,C]
      push_cast
      constructor <;> nlinarith only [hlo,hhi]
  have hvneg (t : ℝ) : v (-t)=v t := by
    dsimp [v]
    simp only [sub_neg_eq_add,← sub_eq_add_neg]
    ring
  have hvabs (t : ℝ) : v |t|=v t := by
    rcases le_total 0 t with ht|ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht,hvneg]
  have hv (n : ℕ) (hnS : n ∈ S) : W n=v ((n:ℝ)-c) := by
    have hn2 := (hn n hnS).1
    dsimp [W,clock,v]
    simp only [Nat.cast_add,Nat.cast_sub hn2,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    change (Real.sqrt ((n:ℝ)+1)-Real.sqrt n+(Real.sqrt (2*c-n+1)-Real.sqrt (2*c-n)))/2=_
    rw [show c-((n:ℝ)-c)=2*c-n by ring,show c+((n:ℝ)-c)=n by ring]
    ring
  have hpair (i : ℕ) (hi : i ∈ S) (j : ℕ) (hj : j ∈ S)
      (hij : |(i:ℝ)-c| ≤ |(j:ℝ)-c|) :
      (q i-q j)*(W i-W j) ≤ L*(q i-q j)^(2 : ℕ) := by
    have hjc : |(j:ℝ)-c| ≤ c/3 := by
      apply ((hn j hj).2).trans
      dsimp [c,C]
      push_cast
      nlinarith
    have h := symmetricSqrtStep_quadratic_lipschitz hc (abs_nonneg ((i:ℝ)-c)) hij hjc
    change v |(j:ℝ)-c|-v |(i:ℝ)-c| ≤ _ at h
    rw [hvabs,hvabs,← hv j hj,← hv i hi,sq_abs,sq_abs] at h
    have hsq : q i ≤ q j := by
      dsimp [q]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ((i:ℝ)-c)) (abs_nonneg ((j:ℝ)-c))).mpr hij
    have hh := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hsq)
    dsimp [L,q] at hh ⊢
    nlinarith only [hh]
  have hcov := covariance_bound S q W L (fun i hi j hj => by
    rcases le_total |(i:ℝ)-c| |(j:ℝ)-c| with hij|hji
    · exact hpair i hi j hj hij
    · have h := hpair j hj i hi hji
      nlinarith only [h])
  have href (f : ℕ → ℝ) : (∑ n ∈ S,f (2*C-n))=∑ n ∈ S,f n := by
    have h := sum_Ico_reflect f (C-s) (m:=C+s+1) (n:=2*C) (by omega)
    rw [show 2*C+1-(C+s+1)=C-s by omega,
      show 2*C+1-(C-s)=C+s+1 by omega] at h
    simpa only [← ha,← hb,S] using h
  have ht : ∑ n ∈ S,clock n=1 := by
    have htel (N : ℕ) : (∑ n ∈ range N,clock n)=Real.sqrt N := by
      simpa only [clock,Nat.cast_zero,Real.sqrt_zero,sub_zero] using Finset.sum_range_sub (fun n : ℕ => Real.sqrt n) N
    dsimp [S]
    rw [sum_Ico_eq_sub _ (show s*s ≤ (s+1)*(s+1) by nlinarith),htel,htel]
    push_cast
    rw [← pow_two,← pow_two,Real.sqrt_sq (by positivity),Real.sqrt_sq (by positivity)]
    ring
  have hW : ∑ n ∈ S,W n=1 := by
    dsimp [W]
    rw [← sum_div,sum_add_distrib,href,ht]
    norm_num
  have hqref (n : ℕ) (hnS : n ∈ S) : q (2*C-n)=q n := by
    dsimp [q]
    rw [Nat.cast_sub (hn n hnS).1]
    push_cast
    change (2*c-(n:ℝ)-c)^(2 : ℕ)=((n:ℝ)-c)^(2 : ℕ)
    ring
  have hqW : (∑ n ∈ S,q n*W n)=∑ n ∈ S,q n*clock n := by
    have hswap : (∑ n ∈ S,q n*clock (2*C-n))=∑ n ∈ S,q n*clock n := by
      rw [← href (fun n => q n*clock n)]
      exact sum_congr rfl (fun n hnS => by rw [hqref n hnS])
    dsimp [W]
    simp_rw [← mul_div_assoc,mul_add]
    rw [← sum_div,sum_add_distrib,hswap]
    ring
  have hcard : S.card=2*s+1 := by
    dsimp [S]
    rw [Nat.card_Ico]
    omega
  have hq : (∑ n ∈ S,q n)=c*(2*s+1)/3 := by
    simpa only [q,c,C,S,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using (sum_block_moments s).1
  have hq2 : (∑ n ∈ S,(q n)^(2 : ℕ))=c*(2*s+1)*(3*c-1)/15 := by
    have hpow (x : ℝ) : (x^(2 : ℕ))^(2 : ℕ)=x^(4 : ℕ) := by ring
    simpa only [q,hpow,c,C,S,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using (sum_block_moments s).2
  rw [hW,hqW,hcard,hq,hq2] at hcov
  push_cast at hcov
  have hvar : (2*(s:ℝ)+1)*(c*(2*s+1)*(3*c-1)/15)-(c*(2*s+1)/3)^(2 : ℕ)=
      (2*s+1)^(2 : ℕ)*(4*c^(2 : ℕ)/45-c/15) := by ring
  rw [hvar] at hcov
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hmean : (∑ n ∈ S,q n*clock n) ≤ c/3+L*(2*s+1)*(4*c^(2 : ℕ)/45-c/15) := by
    nlinarith only [hcov,show (0:ℝ)<2*s+1 by positivity]
  have hcroot : (s:ℝ) ≤ Real.sqrt c := by
    have hsq := Real.sq_sqrt hc.le
    have hpos := Real.sqrt_nonneg c
    have hsc : (s:ℝ)^(2 : ℕ) ≤ c := by dsimp [c,C]; push_cast; nlinarith
    nlinarith only [hsq,hpos,hsc,hsR]
  have hpow : c^(-(5:ℝ)/2)=1/(c^(2 : ℕ)*Real.sqrt c) := by
    rw [show (-(5:ℝ)/2)=-((2:ℝ)+1/2) by ring,Real.rpow_neg hc.le,
      Real.rpow_add hc,Real.rpow_two,← Real.sqrt_eq_rpow]
    rw [one_div]
  have hmajor : L*(2*s+1)*(4*c^(2 : ℕ)/45-c/15) ≤ (2*s+1)/(45*Real.sqrt c) := by
    have h0 := mul_nonneg (mul_nonneg hL (show (0:ℝ) ≤ 2*s+1 by positivity)) (show 0 ≤ c/15 by positivity)
    have he : L*(2*s+1)*(4*c^(2 : ℕ)/45)=(2*s+1)/(45*Real.sqrt c) := by
      dsimp [L]
      rw [hpow]
      field_simp
    linarith only [h0,he]
  have hlast : (2*(s:ℝ)+1)/(45*Real.sqrt c) ≤ 1/18 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hcroot,hsR]
  have hres := hmean.trans (add_le_add_right (hmajor.trans hlast) (c/3))
  simpa only [S,q,clock,c,C,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hres

end RHTower
