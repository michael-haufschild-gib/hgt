import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels
import GaloisForLFunctions.ExceptionalLayerTheory.DiscreteFirstMeansContinueTheirDirichletSeries
import GaloisForLFunctions.ExceptionalLayerTheory.FirstMeansOfBoundedQuotientClasses

/-!
# Adjacent denominators in a discrete quotient mean

Refine two consecutive denominator grids to their common product. The
difference of the rescaled sums is then a terminal block of exactly X
entries. For a profile between zero and one this bounds the unscaled
difference by X/(m+1), including the endpoints of the finite sum.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Sum of a quotient profile over all base cutoffs below X. -/
def discreteQuotientMean (A : ℕ → ℝ) (m X : ℕ) : ℝ := ∑ k ∈ range X, A (k/m)

private theorem repeated_quotient_sum {r : ℕ} (hr : 0<r) (X : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ range (r*X), f (k/r)) = r*∑ j ∈ range X, f j := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ f X,mul_add]
    congr 1
    have h (k : ℕ) (hk : k∈range r) : (r*X+k)/r=X := by
      rw [Nat.mul_add_div hr,Nat.div_eq_of_lt (mem_range.mp hk),add_zero]
    simp only [sum_congr rfl (fun k hk => congrArg f (h k hk)),sum_const,card_range,nsmul_eq_mul]

/-- Refining both grids leaves exactly the X cells between the two terminal cutoffs. -/
theorem discreteQuotientMean_consecutive {m : ℕ} (hm : 0<m) (A : ℕ → ℝ) (X : ℕ) :
    ((m:ℝ)+1)*discreteQuotientMean A m X-(m:ℝ)*discreteQuotientMean A (m+1) X =
      ∑ k ∈ Ico (m*X) ((m+1)*X), A (k/(m*(m+1))) := by
  have hupper := repeated_quotient_sum (Nat.succ_pos m) X (fun k => A (k/m))
  have hlower := repeated_quotient_sum hm X (fun k => A (k/(m+1)))
  simp only [Nat.div_div_eq_div_mul,Nat.cast_succ,mul_comm (m+1) m] at hupper
  simp only [Nat.div_div_eq_div_mul] at hlower
  rw [discreteQuotientMean,discreteQuotientMean,← hupper,← hlower,
    ← sum_range_add_sum_Ico _ (Nat.mul_le_mul_right X (Nat.le_succ m)),add_sub_cancel_left]

/-- The finite first mean of any profile in the unit interval changes by
at most X/(m+1) when the denominator is incremented. -/
theorem discreteQuotientMean_lipschitz (A : ℕ → ℝ) (ha : ∀ n, 0≤A n ∧ A n≤1)
    {m : ℕ} (hm : 0<m) (X : ℕ) :
    |discreteQuotientMean A m X-discreteQuotientMean A (m+1) X| ≤ (X:ℝ)/(m+1) := by
  let S := Ico (m*X) ((m+1)*X)
  have hcard : S.card=X := by simp [S,Nat.card_Ico,Nat.succ_mul]
  have ht := discreteQuotientMean_consecutive hm A X
  have hl : 0≤∑ k ∈ S, A (k/(m*(m+1))) := sum_nonneg fun k _ => (ha _).1
  have hu : (∑ k ∈ S, A (k/(m*(m+1)))) ≤ X := by
    exact (sum_le_sum (s := S) (fun k _ => (ha (k/(m*(m+1)))).2)).trans_eq (by simp [hcard])
  have hl' : 0≤discreteQuotientMean A (m+1) X := sum_nonneg fun k _ => (ha _).1
  have hu' : discreteQuotientMean A (m+1) X≤X :=
    (sum_le_sum (s := range X) (fun k _ => (ha (k/(m+1))).2)).trans_eq (by simp)
  have hp : 0<(m:ℝ)+1 := by positivity
  apply (le_div_iff₀ hp).mpr
  have hprod : |(discreteQuotientMean A m X-discreteQuotientMean A (m+1) X)*((m:ℝ)+1)| ≤ X := by
    rw [abs_le]
    dsimp only [S] at hl hu
    constructor <;> linarith only [ht,hl,hu,hl',hu']
  simpa only [abs_mul,abs_of_pos hp] using hprod

/-- Abel summation converts the adjacent-denominator estimate into a
first-mean bound for every signed arithmetic weight. -/
theorem abs_discreteQuotientMean_weighted (c A : ℕ → ℝ) (h0 : A 0=0) (ha : ∀ n, 0≤A n ∧ A n≤1)
    (X : ℕ) :
    |∑ m ∈ Icc 1 X, c m*discreteQuotientMean A m X| ≤
      X*∑ n ∈ Icc 1 X, |∑ k ∈ Icc 1 n, c k|/((n:ℝ)+1) := by
  have hz : discreteQuotientMean A (X+1) X=0 := by
    apply sum_eq_zero
    intro k hk
    rw [Nat.div_eq_of_lt ((mem_range.mp hk).trans (Nat.lt_succ_self X)),h0]
  have he := sum_smul_eq_prefix_differences c (fun m => discreteQuotientMean A m X) X
  simp only [smul_eq_mul,hz,mul_zero,zero_add] at he
  rw [he,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  refine sum_le_sum fun n hn => ?_
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (discreteQuotientMean_lipschitz A ha (mem_Icc.mp hn).1 X)
    (abs_nonneg _)).trans_eq (by ring)

/-- At inverse integer arguments the triangular profile is the cumulative
sum of all prefixes, divided by the outer cutoff. -/
theorem triangularPrimeProfile_sample (c : ℕ → ℝ) (N : ℕ) :
    (N:ℝ)*triangularPrimeProfile c (N:ℝ)⁻¹=∑ k ∈ range N, ∑ d ∈ Icc 1 k, c d := by
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · simp
  have hp : 0<(N:ℝ) := by exact_mod_cast hn
  have hcut : 1≤((N:ℝ)+1)*(N:ℝ)⁻¹ := by
    rw [add_mul,mul_inv_cancel₀ hp.ne',one_mul]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hp.le)
  rw [triangularPrimeProfile_eq_sum c (inv_nonneg.mpr hp.le) N hcut,mul_sum,
    ← triangular_weighted_sum_eq_sum_prefix,← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine sum_congr rfl fun n hn' => ?_
  have hle : (n:ℝ)+1≤N := by exact_mod_cast mem_range.mp hn'
  have hh := mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hp.le)
  rw [mul_inv_cancel₀ hp.ne'] at hh
  rw [max_eq_left (sub_nonneg.mpr hh),add_comm 1 n,Nat.cast_add,Nat.cast_one]
  field_simp

#print axioms discreteQuotientMean_consecutive
#print axioms abs_discreteQuotientMean_weighted

end GaloisForLFunctions.ExceptionalLayerTheory
