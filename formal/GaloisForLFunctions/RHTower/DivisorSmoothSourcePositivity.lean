import GaloisForLFunctions.RHTower.DivisorHyperbolaSharpBlocks

/-!
# Nonnegativity of the complete smooth divisor source

Geometric harmonic centering gives an analytic lower bound for Euler's
constant. Exact factorial products and analytic logarithm lower bounds settle
the four initial block minima. The existing minimum law and positive tail
then prove nonnegativity at every cutoff.
-/

noncomputable section
open Finset
namespace RHTower

private lemma gamma_lower : (5772/10000:ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := (harmonic_mascheroni_geometric_bounds (n:=16) (by norm_num)).2
  have hl := log_le_geometric_cubic (x:=(17/16:ℝ)) (by norm_num)
  have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    norm_num
  rw [Real.log_div (by norm_num) (by norm_num),h16] at hl
  norm_num [harmonic,Finset.sum_range_succ,h16] at h hl
  linarith only [h,hl,Real.log_two_lt_d9]

private lemma prime_log_lower :
    (1.9455:ℝ) ≤ Real.log 7 ∧ (2.3977:ℝ) ≤ Real.log 11 ∧
    (2.5649:ℝ) ≤ Real.log 13 ∧ (2.8331:ℝ) ≤ Real.log 17 ∧
    (2.9444:ℝ) ≤ Real.log 19 := by
  have h7 := log_le_half_sub_inv (x := (8:ℝ)/7) (by norm_num)
  have h11 := log_le_half_sub_inv (x := (12:ℝ)/11) (by norm_num)
  have h13 := (Real.lt_log_one_add_of_pos (x := (1:ℝ)/12) (by norm_num)).le
  have h17 := (Real.lt_log_one_add_of_pos (x := (1:ℝ)/16) (by norm_num)).le
  have h19 := log_le_half_sub_inv (x := (20:ℝ)/19) (by norm_num)
  have l8 : Real.log 8=3*Real.log 2 := by rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]; norm_num
  have l12 : Real.log 12=2*Real.log 2+Real.log 3 := by
    rw [show (12:ℝ)=4*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq]
  have l16 : Real.log 16=4*Real.log 2 := by rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]; norm_num
  have l20 : Real.log 20=2*Real.log 2+Real.log 5 := by
    rw [show (20:ℝ)=4*5 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq]
  rw [show (1:ℝ)+1/12=13/12 by norm_num] at h13
  rw [show (1:ℝ)+1/16=17/16 by norm_num] at h17
  rw [Real.log_div (by norm_num) (by norm_num),l8] at h7
  rw [Real.log_div (by norm_num) (by norm_num),l12] at h11 h13
  rw [Real.log_div (by norm_num) (by norm_num),l16] at h17
  rw [Real.log_div (by norm_num) (by norm_num),l20] at h19
  norm_num at h7 h11 h13 h17 h19
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_gt_d9
  refine ⟨?_,?_,?_,?_,?_⟩
  · linarith only [h7,h2]
  · linarith only [h11,h2,h3]
  · linarith only [h13,h2,h3]
  · linarith only [h17,h2]
  · linarith only [h19,h2,h5]

private lemma log_factorial_sum (N : ℕ) :
    (∑ k ∈ Icc 1 N,Real.log k)=Real.log (N.factorial:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N+1),ih,Nat.factorial_succ,Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

private lemma small_centers_nonneg {s : ℕ} (hs : 1 ≤ s) (hs4 : s ≤ 4) :
    0 ≤ divisorHyperbolaSmoothRemainder (s*(s+1)) := by
  obtain ⟨h7,h11,h13,h17,h19⟩ := prime_log_lower
  have hg := gamma_lower
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_gt_d9
  have f2 : Real.log ((2:ℕ).factorial:ℝ)=Real.log 2 := by norm_num
  have f6 : Real.log ((6:ℕ).factorial:ℝ)=4*Real.log 2+2*Real.log 3+Real.log 5 := by
    rw [show (((6:ℕ).factorial:ℕ):ℝ)=2^4*3^2*5 by norm_num]
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    norm_num
  have f12 : Real.log ((12:ℕ).factorial:ℝ)=
      10*Real.log 2+5*Real.log 3+2*Real.log 5+Real.log 7+Real.log 11 := by
    rw [show (((12:ℕ).factorial:ℕ):ℝ)=2^10*3^5*5^2*7*11 by norm_num]
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    norm_num
  have f20 : Real.log ((20:ℕ).factorial:ℝ)=
      18*Real.log 2+8*Real.log 3+4*Real.log 5+2*Real.log 7+
        Real.log 11+Real.log 13+Real.log 17+Real.log 19 := by
    rw [show (((20:ℕ).factorial:ℕ):ℝ)=2^18*3^8*5^4*7^2*11*13*17*19 by norm_num]
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    norm_num
  interval_cases s <;> norm_num only [Nat.reduceAdd,Nat.reduceMul]
  all_goals unfold divisorHyperbolaSmoothRemainder
  all_goals rw [log_factorial_sum]
  all_goals simp only [f2,f6,f12,f20]
  all_goals norm_num [harmonic,Finset.sum_range_succ]
  all_goals linarith only [hg,h2,h3,h5,h7,h11,h13,h17,h19]

/-- The literal smooth divisor-hyperbola source is nonnegative at every
cutoff, including the four initial blocks. -/
theorem divisorHyperbolaSmoothRemainder_nonneg (N : ℕ) :
    0 ≤ divisorHyperbolaSmoothRemainder N := by
  by_cases hN : N=0
  · subst N; norm_num [divisorHyperbolaSmoothRemainder]
  by_cases h25 : 25 ≤ N
  · exact divisorHyperbolaSmoothRemainder_nonneg_of_twentyFive h25
  have hN1 : 1 ≤ N := by omega
  have hs : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by simpa using hN1)
  have hs4 : Nat.sqrt N ≤ 4 := by
    have hh := Nat.sqrt_le N
    nlinarith
  exact (small_centers_nonneg hs hs4).trans (divisorHyperbolaSmoothRemainder_center_le hN1)

end RHTower
