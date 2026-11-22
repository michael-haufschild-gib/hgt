import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedVariance.AffineJet
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.PrimaryResidues

/-!
# Absolute trace of the affine Taylor remainder

For centered parent labels, the degree m polynomial leaves a holomorphic
trace to the right of 1/2 − (m+1).
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance

open BalancedContinuation BalancedShift Metric Set

abbrev parent {t : ExceptionalTime} {j : ℕ} (x : Label t j) := labelValue x+center t j

theorem parent_ge_one {t : ExceptionalTime} {j : ℕ} (x : Label t j) : 1 ≤ parent x :=
  (label_one_le x).trans (le_add_of_nonneg_right (center_pos t j).le)

def error (b a n : ℝ) (s : ℂ) (m : ℕ) := weight n s *
  (weight (b+a*n⁻¹) s-poly b a s m n⁻¹)

def errorTrace (t : ExceptionalTime) (j m : ℕ) (b a : ℝ) (s : ℂ) :=
  ∑' x : Label t j, error b a (parent x) s m

private theorem shift_weight {n : ℝ} (hn : 0 < n) (s : ℂ) (k : ℕ) :
    weight n s*((n⁻¹:ℝ):ℂ)^k = weight n (s+(k:ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,← mul_assoc,ih,Nat.cast_succ,← add_assoc,weight_succ hn,Complex.ofReal_inv]

/-- Each derivative of the normalized entry produces a shifted physical heat entry. -/
theorem child_expansion {b a n : ℝ} (hb : 0 < b) (he : 0 < b+a) (hn : 1 ≤ n) (s : ℂ) (m : ℕ) :
    weight (b*n+a) s = error b a n s m +
      ∑ k ∈ Finset.range (m+1), term b a s k * weight n (s+(k:ℂ)) := by
  have hn₀ := zero_lt_one.trans_le hn
  have hh : b*n+a = n*(b+a*n⁻¹) := by field_simp [hn₀.ne']
  rw [hh,weight_mul hn₀.le (affine_pos hb he (inverse_unit hn)).le,error,mul_sub,poly,Finset.mul_sum]
  have hf (k : ℕ) : weight n s*(term b a s k*((n⁻¹:ℝ):ℂ)^k) =
      term b a s k * weight n (s+(k:ℂ)) := by rw [mul_left_comm,shift_weight hn₀]
  simp only [hf,sub_add_cancel]

private theorem error_entire {b a n : ℝ} (hb : 0 < b) (he : 0 < b+a) (hn : 1 ≤ n) (m : ℕ) :
    Differentiable ℂ (fun s => error b a n s m) := by
  apply (weight_entire (zero_lt_one.trans_le hn)).mul
  apply (weight_entire (affine_pos hb he (inverse_unit hn))).sub
  apply Differentiable.fun_sum
  intro k _
  have hw := (weight_entire hb).comp (differentiable_id.add_const (k:ℂ))
  exact (((differentiable_const _).mul (falling_entire k)).mul hw).mul_const _

private theorem disk_bound (t : ExceptionalTime) (j m : ℕ) {b a : ℝ} (hb : 0 < b) (he : 0 < b+a)
    (w : ℂ) (hw : 1/2-((m:ℝ)+1) < w.re) :
    ∃ R : ℝ, 0 < R ∧ ∃ g : Label t j → ℝ, Summable g ∧
      ∀ x s, s ∈ ball w R → ‖error b a (parent x) s m‖ ≤ g x := by
  let R := (w.re+((m:ℝ)+1)-1/2)/2
  let p := w.re+((m:ℝ)+1)-R
  have hR : 0 < R := by dsimp only [R]; linarith only [hw]
  have hp : 1/2 < p := by dsimp only [p,R]; linarith only [hw]
  obtain ⟨K,hK,h⟩ := normalized_bound hb he w R m
  have hsum := (shifted_heat_summable_iff t j ⟨center t j,by linarith only [center_pos t j]⟩ (p:ℂ)).mpr hp
  refine ⟨R,hR,fun x => K*‖weight (parent x) (p:ℂ)‖,hsum.mul_left K,?_⟩
  intro x s hs
  let n := parent x
  have hn : 1 ≤ n := parent_ge_one x
  have hn₀ := zero_lt_one.trans_le hn
  have hr := (Complex.abs_re_le_norm (s-w)).trans (mem_ball_iff_norm.mp hs).le
  rw [Complex.sub_re,abs_le] at hr
  have hsp : p ≤ s.re+((m:ℝ)+1) := by dsimp only [p]; linarith only [hr.1]
  rw [error,norm_mul]
  refine (mul_le_mul_of_nonneg_left (h s (ball_subset_closedBall hs) n⁻¹ (inverse_unit hn)) (norm_nonneg _)).trans ?_
  change ‖weight n s‖*(K*(n⁻¹)^(m+1)) ≤ K*‖weight n (p:ℂ)‖
  have hi : (n⁻¹)^(m+1) = n^(-((m:ℝ)+1)) := by
    rw [← Nat.cast_succ,Real.rpow_neg hn₀.le,Real.rpow_natCast,inv_pow]
  rw [weight,weight,Complex.norm_cpow_eq_rpow_re_of_pos hn₀,
    Complex.norm_cpow_eq_rpow_re_of_pos hn₀,Complex.neg_re,Complex.neg_re,Complex.ofReal_re,
    hi,mul_left_comm,← Real.rpow_add hn₀]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hsp])) hK

theorem error_summable (t : ExceptionalTime) (j m : ℕ) {b a : ℝ} (hb : 0 < b) (he : 0 < b+a)
    (w : {s : ℂ // 1/2-((m:ℝ)+1) < s.re}) :
    Summable (fun x : Label t j => error b a (parent x) w.val m) := by
  obtain ⟨R,hR,g,hg,h⟩ := disk_bound t j m hb he w.val w.property
  exact (hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => h x _ (mem_ball_self hR))).of_norm

theorem trace_analytic (t : ExceptionalTime) (j m : ℕ) {b a : ℝ} (hb : 0 < b) (he : 0 < b+a)
    (w : {s : ℂ // 1/2-((m:ℝ)+1) < s.re}) : AnalyticAt ℂ (errorTrace t j m b a) w.val := by
  let U := {s : ℂ | 1/2-((m:ℝ)+1) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticAt (s := U) _ (hU.mem_nhds w.property)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R,hR,g,hg,h⟩ := disk_bound t j m hb he s hs
  exact HTGeometry.differentiableAt_tsum_of_cauchy_dominated hR
    (fun x => (error_entire hb he (parent_ge_one x) m).differentiableOn) h hg

#print axioms child_expansion
#print axioms trace_analytic

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance
