import GaloisForLFunctions.RHTower.MobiusDivisorHeadNeutralization
import GaloisForLFunctions.RHTower.HarmonicSecondErrorBounds

/-!
# Uniform square-root bounds for the literal unsigned channels

The half-logarithmic Stirling endpoint cancels the harmonic logarithm in the
smooth hyperbola boundary. The centered signed Abel term is nonpositive, so
all unsigned channels have one uniform square-root ceiling. Exact clipped
clock interpolation retains that ceiling without an endpoint loss. The initial
head square and the total release from a balanced initial late block are
therefore only linear in the cutoff.
-/
noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private theorem log_factorial_sum (N : ℕ) :
    (∑ k ∈ Icc 1 N,Real.log k)=Real.log (N.factorial:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N+1),ih,Nat.factorial_succ,Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- The global Stirling ceiling retains the half-logarithmic endpoint with rational constant one. -/
theorem sum_log_Icc_le_half_log_stirling {N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Icc 1 N,Real.log k) ≤ (N:ℝ)*Real.log N-N+Real.log N/2+1 := by
  have hseq : Real.log (Stirling.stirlingSeq N) ≤ Real.log (Stirling.stirlingSeq 1) := by
    have h := Stirling.log_stirlingSeq'_antitone (show 0 ≤ N-1 by omega)
    simpa only [Function.comp_apply,Nat.succ_eq_add_one,Nat.sub_add_cancel hN,Nat.zero_add] using h
  have hone : Real.log (Stirling.stirlingSeq 1)=1-Real.log 2/2 := by
    rw [Stirling.stirlingSeq_one,Real.log_div (by positivity) (by positivity),
      Real.log_exp,Real.log_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [hone,Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num) (by positivity),Real.log_div (by positivity) (by positivity),Real.log_exp] at hseq
  rw [log_factorial_sum]
  linarith only [hseq]

private theorem hyperbola_boundary_upper {x s : ℝ} (hs : 0 < s)
    (hlo : s^(2 : ℕ) ≤ x) (hhi : x ≤ s^(2 : ℕ)+2*s) :
    x*(Real.log x-2*Real.log s)-x+s^(2 : ℕ) ≤ 4 := by
  have hx : 0 < x := lt_of_lt_of_le (sq_pos_of_pos hs) hlo
  have hs2 : 0 < s^(2 : ℕ) := sq_pos_of_pos hs
  have hupper := Real.log_le_sub_one_of_pos (x := x/s^(2 : ℕ)) (by positivity)
  rw [Real.log_div hx.ne' (ne_of_gt hs2),Real.log_pow] at hupper
  push_cast at hupper
  have hhi' := mul_le_mul_of_nonneg_left hupper hs2.le
  have hcancel : s^(2 : ℕ)*(x/s^(2 : ℕ)-1)=x-s^(2 : ℕ) := by field_simp
  rw [hcancel] at hhi'
  have hlog : Real.log x-2*Real.log s ≤ 2/s := by
    apply le_of_mul_le_mul_left (a := s^(2 : ℕ)) ?_ hs2
    have he : s^(2 : ℕ)*(2/s)=2*s := by field_simp
    rw [he]
    linarith only [hhi',hhi]
  have hdelta := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hlo)
  have hprod : (x-s^(2 : ℕ))*(2/s) ≤ 4 := by
    rw [← mul_div_assoc,div_le_iff₀ hs]
    nlinarith only [hhi]
  nlinarith only [hdelta,hprod,hhi']

/-- Retaining the Stirling endpoint removes the apparent logarithmic growth of the smooth source boundary. -/
theorem divisorHyperbolaSmoothRemainder_le_seven (N : ℕ) :
    divisorHyperbolaSmoothRemainder N ≤ 7 := by
  by_cases hz : N=0
  · subst N
    norm_num [divisorHyperbolaSmoothRemainder]
  have hN : 1 ≤ N := by omega
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by positivity
  have hNp : (0:ℝ) < N := by positivity
  have hlo : (s:ℝ)^(2 : ℕ) ≤ N := by
    rw [pow_two]
    exact_mod_cast Nat.sqrt_le N
  have hhi : (N:ℝ) ≤ (s:ℝ)^(2 : ℕ)+2*s := by
    have h := Nat.lt_succ_sqrt N
    change N < (s+1)*(s+1) at h
    have h' : N ≤ s*s+2*s := by nlinarith
    rw [pow_two]
    exact_mod_cast h'
  have hboundary := hyperbola_boundary_upper hs0 hlo hhi
  have hH := harmonic_mascheroni_half_bounds hs
  have hHmul := mul_le_mul_of_nonneg_left hH.1 (show (0:ℝ)≤2*N by positivity)
  have he : (2*(N:ℝ))*(1/(2*((s:ℝ)+1)))=(N:ℝ)/((s:ℝ)+1) := by field_simp
  rw [he] at hHmul
  have hquot : (s:ℝ)-1 ≤ (N:ℝ)/((s:ℝ)+1) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hlo]
  have hcorrection : (s:ℝ)-2*N*(((harmonic s:ℚ):ℝ)-Real.log s-Real.eulerMascheroniConstant) ≤ 1 := by
    linarith only [hHmul,hquot]
  have hratio : (N:ℝ)/(s:ℝ)^(2 : ℕ) ≤ 3 := by
    rw [div_le_iff₀ (sq_pos_of_pos hs0)]
    nlinarith only [hhi,hs1]
  have hlog := Real.log_le_sub_one_of_pos (x := (N:ℝ)/(s:ℝ)^(2 : ℕ)) (by positivity)
  rw [Real.log_div hNp.ne' (ne_of_gt (sq_pos_of_pos hs0)),Real.log_pow] at hlog
  push_cast at hlog
  have hloghalf : Real.log N/2-Real.log s ≤ 1 := by linarith only [hlog,hratio]
  have hHfloor : Real.log s+Real.eulerMascheroniConstant ≤ ((harmonic s:ℚ):ℝ) := by
    have hp : (0:ℝ) ≤ 1/(2*((s:ℝ)+1)) := by positivity
    linarith only [hH.1,hp]
  have hfact := sum_log_Icc_le_half_log_stirling hN
  have hfactharm : (∑ k ∈ Icc 1 N,Real.log k)-(N:ℝ)*Real.log N+N-
      ((harmonic s:ℚ):ℝ) ≤ 2 := by
    have hg := Real.one_half_lt_eulerMascheroniConstant
    linarith only [hfact,hHfloor,hloghalf,hg]
  have hid : divisorHyperbolaSmoothRemainder N =
      ((∑ k ∈ Icc 1 N,Real.log k)-(N:ℝ)*Real.log N+N-((harmonic s:ℚ):ℝ))+
      ((N:ℝ)*(Real.log N-2*Real.log s)-N+(s:ℝ)^(2 : ℕ))+
      ((s:ℝ)-2*N*(((harmonic s:ℚ):ℝ)-Real.log s-Real.eulerMascheroniConstant)) := by
    dsimp [divisorHyperbolaSmoothRemainder,s]
    ring
  rw [hid]
  linarith only [hfactharm,hboundary,hcorrection]

/-- The smooth half-order contribution has a uniform square-root ceiling. -/
theorem divisorHyperbolaSmoothAbel_le_seven_sqrt (M : ℕ) :
    divisorHyperbolaSmoothAbel M ≤ 7*Real.sqrt M := by
  have htel : (∑ k ∈ range M,halfOrderAbelStep 0 k)=Real.sqrt M := by
    simpa only [halfOrderAbelStep,Nat.zero_add,Nat.cast_zero,Real.sqrt_zero,sub_zero]
      using Finset.sum_range_sub (fun k : ℕ => Real.sqrt k) M
  unfold divisorHyperbolaSmoothAbel
  calc
    _ ≤ ∑ k ∈ range M,7*halfOrderAbelStep 0 k :=
      sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
        (divisorHyperbolaSmoothRemainder_le_seven k) (halfOrderAbelStep_nonneg 0 k))
    _ = _ := by rw [← mul_sum,htel]

/-- Signed centered time cancellation gives the undilated channel a square-root ceiling without logarithmic loss. -/
theorem divisorUnsignedDilationChannel_one_le_seven_sqrt (M : ℕ) :
    divisorUnsignedDilationChannel M 1 ≤ 7*Real.sqrt M := by
  have hid := mobiusDivisorDilationChannel_one_eq_hyperbola M
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at hid
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at hid
  have hs := divisorHyperbolaSmoothAbel_le_seven_sqrt M
  have hc := (centeredDivisorHyperbolaAbel_bounds M).2
  linarith only [hid,hs,hc]

/-- Every unsigned dilation shares the same square-root ceiling; the exact clock absorbs the clipped block. -/
theorem divisorUnsignedDilationChannel_le_seven_sqrt (M d : ℕ) :
    divisorUnsignedDilationChannel M d ≤ 7*Real.sqrt M := by
  by_cases hd : d=0
  · subst d
    simp [divisorUnsignedDilationChannel,primeFreeDivisorDefect,Real.sqrt_nonneg]
  have hd0 : 0 < d := by omega
  have hw0 := divisorPrimeClipWeight_nonneg M d hd0
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M d := by
    have h := divisorPrimeClipWeight_lt_one M d hd0
    linarith
  have hA := mul_le_mul_of_nonneg_left (divisorUnsignedDilationChannel_one_le_seven_sqrt (M/d)) hw1
  have hB := mul_le_mul_of_nonneg_left (divisorUnsignedDilationChannel_one_le_seven_sqrt (M/d+1)) hw0
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hA hB) (Real.sqrt_nonneg (d:ℝ))
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd0
  simp only [Nat.mul_one] at hc
  have hclock := divisorPrimeClipWeight_mul_step M d hd0
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hclock
  rw [hc]
  push_cast at hsum ⊢
  nlinarith only [hsum,hclock]

/-- The entire initial head-square reserve is at most linear in the cutoff. -/
theorem mobiusDivisorSelectionHead_empty_sq_le_linear (M : ℕ) :
    (mobiusDivisorSelectionFibre M ∅ ∅)^(2 : ℕ) ≤ 49*M := by
  have hlo := mobiusDivisorSelectionHead_empty_nonneg M
  have hhi := divisorUnsignedDilationChannel_one_le_seven_sqrt M
  rw [← mobiusDivisorSelectionHead_empty_eq_unit_channel] at hhi
  have hp := mul_nonneg (sub_nonneg.mpr hhi)
    (show 0 ≤ 7*Real.sqrt M+mobiusDivisorSelectionFibre M ∅ ∅ by positivity)
  nlinarith only [hp,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)]

/-- Initial head balancing releases a subquadratic reserve, below every positive quadratic multiple eventually. -/
theorem eventually_mobiusDivisorInitialHeadSquare_le_quadratic_multiple (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,(mobiusDivisorSelectionFibre M ∅ ∅)^(2 : ℕ) ≤ ε*(M:ℝ)^(2 : ℕ) := by
  have ht : ∀ᶠ M : ℕ in atTop,(49:ℝ)/ε ≤ M :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (49/ε)
  filter_upwards [ht] with M hM
  have he : (49:ℝ) ≤ ε*M := by
    have h := (div_le_iff₀ hε).mp hM
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) M)
  have hhead := mobiusDivisorSelectionHead_empty_sq_le_linear M
  nlinarith only [hm,hhead]

/-- Every initial late block that does not overshoot below minus square-root cutoff releases at most linear energy in total. -/
theorem mobiusDivisorInitialLateBlock_release_le_linear (M : ℕ) (L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p)
    (hhead : -Real.sqrt M ≤ mobiusDivisorSelectionFibre M L ∅) :
    mobiusDivisorSelectionEnergy M ∅-mobiusDivisorSelectionEnergy M L ≤ 57*M := by
  have hc (p : ℕ) (hp : p ∈ L) : mobiusDivisorDilationChannel M p =
      -divisorUnsignedDilationChannel M p := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime (hL p hp).1]
    push_cast
    ring
  have hsum : (∑ p ∈ L,mobiusDivisorDilationChannel M p) =
      -(∑ p ∈ L,divisorUnsignedDilationChannel M p) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl hc
  have hheadL := mobiusDivisorSelectionHead_union_late_primes M ∅ L hL (by simp)
  simp only [empty_union] at hheadL
  rw [hsum] at hheadL
  have hunit := divisorUnsignedDilationChannel_one_le_seven_sqrt M
  rw [← mobiusDivisorSelectionHead_empty_eq_unit_channel] at hunit
  have hmass : (∑ p ∈ L,divisorUnsignedDilationChannel M p) ≤ 8*Real.sqrt M := by
    linarith only [hheadL,hunit,hhead]
  have hsquares : (∑ p ∈ L,(mobiusDivisorDilationChannel M p)^(2 : ℕ)) ≤
      Real.sqrt M*(∑ p ∈ L,divisorUnsignedDilationChannel M p) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    rw [hc p hp,neg_sq]
    have hlo := divisorUnsignedDilationChannel_nonneg M p
    have hhi := divisorUnsignedDilationChannel_late_le_sqrt (hL p hp).1.pos (hL p hp).2.1 (hL p hp).2.2
    have hprod := mul_nonneg (sub_nonneg.mpr hhi) hlo
    nlinarith only [hprod]
  have hscaled := mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg (M:ℝ))
  have hsq : (∑ p ∈ L,(mobiusDivisorDilationChannel M p)^(2 : ℕ)) ≤ 8*M := by
    nlinarith only [hsquares,hscaled,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)]
  have hV := mobiusDivisorNonemptyEnergy_union_late_primes M ∅ L hL (by simp)
  simp only [empty_union] at hV
  unfold mobiusDivisorNonemptyEnergy at hV
  have hHsq := mobiusDivisorSelectionHead_empty_sq_le_linear M
  linarith only [hV,hHsq,hsq,sq_nonneg (mobiusDivisorSelectionFibre M L ∅)]

/-- The total energy released by a balanced initial late block is uniformly subquadratic over all choices of that block. -/
theorem eventually_mobiusDivisorInitialLateBlock_release_le_quadratic_multiple (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,∀ L : Finset ℕ,
      (∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p) →
      -Real.sqrt M ≤ mobiusDivisorSelectionFibre M L ∅ →
      mobiusDivisorSelectionEnergy M ∅-mobiusDivisorSelectionEnergy M L ≤ ε*(M:ℝ)^(2 : ℕ) := by
  have ht : ∀ᶠ M : ℕ in atTop,(57:ℝ)/ε ≤ M :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (57/ε)
  filter_upwards [ht] with M hM
  intro L hL hhead
  have he : (57:ℝ) ≤ ε*M := by
    have h := (div_le_iff₀ hε).mp hM
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) M)
  have hrelease := mobiusDivisorInitialLateBlock_release_le_linear M L hL hhead
  nlinarith only [hm,hrelease]

end RHTower
