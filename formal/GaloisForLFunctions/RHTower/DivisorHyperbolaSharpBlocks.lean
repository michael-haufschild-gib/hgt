import GaloisForLFunctions.RHTower.HarmonicGeometricBounds
import GaloisForLFunctions.RHTower.DivisorHyperbolaAbelBound
/-!
# Sharp positivity of smooth divisor square blocks

Geometric harmonic centering locates the discrete minimum at `s*(s+1)`.
Stirling makes that minimum nonnegative for `s ≥ 5`; paired factorial
increments cover the exact growth of the centered-prefix allowance.
-/

noncomputable section
open Finset
namespace RHTower
private def smoothBlock (s k : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 k, Real.log m)-(2*(k:ℝ)+1)*((harmonic s:ℚ):ℝ)+
    (s:ℝ)^(2 : ℕ)+s+2*Real.eulerMascheroniConstant*k
private theorem smoothBlock_eq {s k : ℕ} (h : Nat.sqrt k=s) :
    smoothBlock s k=divisorHyperbolaSmoothRemainder k := by
  simp only [smoothBlock,divisorHyperbolaSmoothRemainder,h]
private theorem smoothBlock_succ (s k : ℕ) :
    smoothBlock s (k+1)-smoothBlock s k =
      Real.log (k+1:ℕ)-2*(((harmonic s:ℚ):ℝ)-Real.eulerMascheroniConstant) := by
  unfold smoothBlock
  rw [sum_Icc_succ_top (by omega : 1 ≤ k+1)]
  push_cast
  ring
/-- The centered harmonic slope lies between the two logarithms surrounding s(s+1). -/
theorem harmonic_geometric_slope_bounds {s : ℕ} (hs : 1 ≤ s) :
    Real.log ((s:ℝ)*(s+1)) ≤ 2*(((harmonic s:ℚ):ℝ)-Real.eulerMascheroniConstant) ∧
    2*(((harmonic s:ℚ):ℝ)-Real.eulerMascheroniConstant) ≤ Real.log ((s:ℝ)*(s+1)+1) := by
  have hg := harmonic_mascheroni_geometric_bounds hs
  have hs0 : (0:ℝ)<s := by positivity
  have hc : (2:ℝ) ≤ (s:ℝ)*(s+1) := by
    have : (1:ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  rw [← Real.log_mul hs0.ne' (by positivity)] at hg
  have hlog := Real.log_le_sub_one_of_pos (x := ((s:ℝ)*(s+1))/((s:ℝ)*(s+1)+1)) (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  have hfrac : ((s:ℝ)*(s+1))/((s:ℝ)*(s+1)+1)-1 = -1/((s:ℝ)*(s+1)+1) := by field_simp; ring
  rw [hfrac] at hlog
  have hcomp : 2*(1/(6*(s:ℝ)*(s+1))) ≤ 1/((s:ℝ)*(s+1)+1) := by
    field_simp
    nlinarith only [hc]
  simp only [neg_div] at hlog
  constructor <;> linarith only [hg.1,hg.2,hlog,hcomp]

private theorem smoothBlock_center_nonneg {s : ℕ} (hs : 5 ≤ s) :
    0 ≤ smoothBlock s (s*(s+1)) := by
  have hs1 : 1 ≤ s := by omega
  have hc1 : 1 ≤ s*(s+1) := by nlinarith
  have hc30 : (30:ℝ) ≤ (s:ℝ)*(s+1) := by
    have hsR : (5:ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  have hf := sum_log_Icc_ge_half_log_stirling hc1
  have hg := (harmonic_mascheroni_geometric_bounds hs1).2
  rw [← Real.log_mul (by positivity) (by positivity)] at hg
  have hmul := mul_le_mul_of_nonneg_left hg (show (0:ℝ) ≤ 2*((s:ℝ)*(s+1))+1 by positivity)
  have herr : (2*((s:ℝ)*(s+1))+1)*(1/(6*(s:ℝ)*(s+1))) ≤ 1/3+1/180 := by
    field_simp
    nlinarith only [hc30]
  have hgamma := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  push_cast at hf
  unfold smoothBlock
  push_cast
  nlinarith only [hf,hmul,herr,hgamma]

private theorem smoothBlock_min {s k : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k) :
    smoothBlock s (s*(s+1)) ≤ smoothBlock s k := by
  let c := s*(s+1)
  have hc : 1 ≤ c := by dsimp [c]; nlinarith
  have hslope := harmonic_geometric_slope_bounds hs
  have hslope' : Real.log (c:ℝ) ≤ 2*(((harmonic s:ℚ):ℝ)-Real.eulerMascheroniConstant) ∧
      2*(((harmonic s:ℚ):ℝ)-Real.eulerMascheroniConstant) ≤ Real.log ((c:ℝ)+1) := by
    simpa only [c,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hslope
  have hdown : AntitoneOn (smoothBlock s) (Set.Icc 1 c) := by
    apply antitoneOn_of_succ_le (Set.ordConnected_Icc)
    intro n _ hn hns
    have hn' : n+1 ≤ c := hns.2
    have hl := Real.log_le_log (by positivity : (0:ℝ)<(n+1:ℕ)) (show ((n+1:ℕ):ℝ) ≤ (c:ℝ) by exact_mod_cast hn')
    have hstep := smoothBlock_succ s n
    change smoothBlock s (n+1) ≤ smoothBlock s n
    linarith only [hl,hslope'.1,hstep]
  have hup : MonotoneOn (smoothBlock s) (Set.Ici c) := by
    apply monotoneOn_nat_Ici_of_le_succ
    intro n hn
    have hl := Real.log_le_log (by positivity : (0:ℝ)<(c:ℝ)+1)
      (show (c:ℝ)+1 ≤ (n+1:ℕ) by exact_mod_cast Nat.add_le_add_right hn 1)
    have hstep := smoothBlock_succ s n
    linarith only [hl,hslope'.2,hstep]
  rcases le_total k c with hkc|hck
  · exact hdown ⟨hk,hkc⟩ ⟨hc,le_rfl⟩ hkc
  · exact hup (a := c) (b := k) (show c ∈ Set.Ici c by simp only [Set.mem_Ici]; exact le_rfl) hck hck

/-- The geometric center is a minimum of the actual smooth square block. -/
theorem divisorHyperbolaSmoothRemainder_center_le {N : ℕ} (hN : 1 ≤ N) :
    divisorHyperbolaSmoothRemainder (Nat.sqrt N*(Nat.sqrt N+1)) ≤
      divisorHyperbolaSmoothRemainder N := by
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hc : Nat.sqrt (s*(s+1))=s :=
    (Nat.eq_sqrt.mpr ⟨by nlinarith,by nlinarith⟩).symm
  have h := smoothBlock_min hs hN
  rw [smoothBlock_eq hc,smoothBlock_eq (show Nat.sqrt N=s from rfl)] at h
  exact h

/-- Every smooth hyperbola remainder from the fifth square block onward is nonnegative. -/
theorem divisorHyperbolaSmoothRemainder_nonneg_of_twentyFive {N : ℕ} (hN : 25 ≤ N) :
    0 ≤ divisorHyperbolaSmoothRemainder N := by
  have hs : 5 ≤ Nat.sqrt N := Nat.le_sqrt.mpr hN
  have h := (smoothBlock_center_nonneg hs).trans (smoothBlock_min (by omega) (by omega : 1 ≤ N))
  rwa [smoothBlock_eq rfl] at h

private theorem smoothBlock_pair {s j : ℕ} (hs : 1 ≤ s) (hj : j ≤ s) :
    (j:ℝ)^(2 : ℕ)/((s:ℝ)+1)^(2 : ℕ) ≤
      smoothBlock s (s*(s+1)-j)+smoothBlock s (s*(s+1)+j)-2*smoothBlock s (s*(s+1)) := by
  let c := s*(s+1)
  induction j with
  | zero => simp; ring_nf; exact le_rfl
  | succ j ih =>
    have ih' := ih (by omega)
    have hjc : j+1 ≤ c := by dsimp [c]; nlinarith
    have hsub : c-(j+1)+1=c-j := by omega
    have hleft := smoothBlock_succ s (c-(j+1))
    have hright := smoothBlock_succ s (c+j)
    rw [hsub] at hleft
    have hpos : (0:ℝ)<(c-j:ℕ) := by exact_mod_cast (show 0<c-j by omega)
    have hlog := Real.log_le_sub_one_of_pos (x := ((c-j:ℕ):ℝ)/(c+j+1:ℕ)) (by positivity)
    rw [Real.log_div hpos.ne' (by positivity)] at hlog
    have hratio : (1:ℝ)-((c-j:ℕ):ℝ)/(c+j+1:ℕ)=(2*(j:ℝ)+1)/(c+j+1:ℕ) := by
      rw [Nat.cast_sub (by omega : j ≤ c)]
      push_cast
      field_simp
      ring
    have hlog' : (2*(j:ℝ)+1)/(c+j+1:ℕ) ≤ Real.log (c+j+1:ℕ)-Real.log (c-j:ℕ) := by
      rw [← hratio]
      linarith only [hlog]
    have hden : ((c+j+1:ℕ):ℝ) ≤ ((s:ℝ)+1)^(2 : ℕ) := by
      have hjR : (j:ℝ)+1 ≤ s := by exact_mod_cast hj
      dsimp [c]
      push_cast
      nlinarith only [hjR]
    have hfrac := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 2*j+1 by positivity)
      (show (0:ℝ)<(c+j+1:ℕ) by positivity) hden
    have hpoly : ((j+1:ℕ):ℝ)^(2 : ℕ)/((s:ℝ)+1)^(2 : ℕ) =
        (j:ℝ)^(2 : ℕ)/((s:ℝ)+1)^(2 : ℕ)+(2*(j:ℝ)+1)/((s:ℝ)+1)^(2 : ℕ) := by push_cast; ring
    change _ ≤ smoothBlock s (c-(j+1))+smoothBlock s (c+(j+1))-2*smoothBlock s c
    rw [hpoly]
    change (j:ℝ)^(2 : ℕ)/((s:ℝ)+1)^(2 : ℕ) ≤ smoothBlock s (c-j)+smoothBlock s (c+j)-2*smoothBlock s c at ih'
    rw [show c+(j+1)=c+j+1 by omega]
    linarith only [ih',hleft,hright,hlog',hfrac]

private theorem sum_symmetric_interval (f : ℕ → ℝ) {c s : ℕ} (hs : s ≤ c) :
    (∑ k ∈ Ico (c-s) (c+s+1), f k) =
      f c+∑ j ∈ Icc 1 s, (f (c-j)+f (c+j)) := by
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

private theorem sum_sq_Icc (s : ℕ) :
    (∑ j ∈ Icc 1 s, (j:ℝ)^(2 : ℕ)) = (s:ℝ)*(s+1)*(2*s+1)/6 := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_Icc_succ_top (by omega : 1 ≤ s+1),ih]; push_cast; ring

/-- A complete square block covers the increment in the exact centered-prefix allowance. -/
theorem sum_divisorHyperbolaSmoothRemainder_square_block_ge_sharp {s : ℕ} (hs : 5 ≤ s) :
    ((s:ℝ)+1)/4 ≤ ∑ k ∈ Ico (s*s) ((s+1)*(s+1)), divisorHyperbolaSmoothRemainder k := by
  let c := s*(s+1)
  have hc : 0 ≤ smoothBlock s c := smoothBlock_center_nonneg hs
  have hpoint (j : ℕ) (hj : j ∈ Icc 1 s) :
      (j:ℝ)^(2 : ℕ)/((s:ℝ)+1)^(2 : ℕ) ≤ smoothBlock s (c-j)+smoothBlock s (c+j) := by
    have h := smoothBlock_pair (by omega : 1 ≤ s) (mem_Icc.mp hj).2
    change _ ≤ smoothBlock s (c-j)+smoothBlock s (c+j)-2*smoothBlock s c at h
    linarith only [h,hc]
  have hsum := sum_le_sum hpoint
  rw [← sum_div,sum_sq_Icc] at hsum
  have heq : (∑ k ∈ Ico (s*s) ((s+1)*(s+1)), divisorHyperbolaSmoothRemainder k) =
      smoothBlock s c+∑ j ∈ Icc 1 s, (smoothBlock s (c-j)+smoothBlock s (c+j)) := by
    have he1 : c-s=s*s := by
      dsimp [c]
      rw [show s*(s+1)=s*s+s by ring]
      omega
    have he2 : c+s+1=(s+1)*(s+1) := by dsimp [c]; ring
    rw [← sum_symmetric_interval (smoothBlock s) (show s ≤ c by dsimp [c]; nlinarith),he1,he2]
    apply sum_congr rfl
    intro k hk
    exact (smoothBlock_eq (Nat.eq_sqrt.mpr (mem_Ico.mp hk)).symm).symm
  have hpoly : ((s:ℝ)+1)/4 ≤ ((s:ℝ)*(s+1)*(2*s+1)/6)/((s:ℝ)+1)^(2 : ℕ) := by
    have hsR : (5:ℝ) ≤ s := by exact_mod_cast hs
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ (s:ℝ)-5 by linarith) (show 0 ≤ (s:ℝ)+1 by positivity)]
  rw [heq]
  linarith only [hpoly,hsum,hc]

end RHTower
