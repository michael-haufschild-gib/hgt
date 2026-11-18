import GaloisForLFunctions.RHTower.RVCumulantAverage

/-!
# Logarithmic moments of prime coefficients

On a dyadic prime window every power of log p can be removed from a
nonnegative weight after normalizing by the same power of log X. This
identifies the additional prime estimate needed in the proof of (2.6)
of arXiv:2610.18928. The Chebyshev weight realizes the full loss.
-/

noncomputable section
open Filter Topology Finset RHTower
namespace GaloisForLFunctions.PrimeExponentialSums.PrimeMoments

/-- Absolute prime mass on (X,2X] with k extra prime logarithms. -/
def moment (w : ℝ → ℝ) (k : ℕ) (X : ℝ) :=
  primeCountSum (fun t => |w t| * Real.log t ^ k) X (2*X)

theorem window_bounds (w : ℝ → ℝ) (k : ℕ) {X : ℝ} (hX : 1<X) :
    moment w 0 X * Real.log X ^ k ≤ moment w k X ∧
    moment w k X ≤ moment w 0 X * Real.log (2*X) ^ k := by
  have hx := one_pos.trans hX
  simp only [moment,primeCountSum,pow_zero,mul_one,sum_mul]
  constructor
  · refine sum_le_sum fun p hp => ?_
    obtain ⟨_,h₁,_⟩ := mem_shell_of_mem_filter hx.le hp
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_pos hX).le
      (Real.log_le_log hx h₁.le) k) (abs_nonneg _)
  · refine sum_le_sum fun p hp => ?_
    obtain ⟨_,h₁,h₂⟩ := mem_shell_of_mem_filter hx.le hp
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (Real.log_nonneg (hX.trans h₁).le) (Real.log_le_log (hx.trans h₁) h₂) k) (abs_nonneg _)

private theorem log_ratio :
    Tendsto (fun X : ℝ => Real.log (2*X) / Real.log X) atTop (𝓝 1) := by
  have h := (tendsto_log_shift_ratio (Real.log 2)).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [inv_div,Real.log_mul two_ne_zero hX.ne',add_comm]

private theorem divided_bounds (w : ℝ → ℝ) (k : ℕ) {X : ℝ} (hX : 1<X) :
    moment w 0 X ≤ moment w k X / Real.log X ^ k ∧
    moment w k X / Real.log X ^ k ≤ moment w 0 X * (Real.log (2*X) / Real.log X)^k := by
  obtain ⟨lo,hi⟩ := window_bounds w k hX
  have hp := pow_pos (Real.log_pos hX) k
  refine ⟨(le_div_iff₀ hp).2 lo,?_⟩
  rw [div_pow,← mul_div_assoc]
  exact div_le_div_of_nonneg_right hi hp.le

/-- Log reweighting preserves every finite normalized limit, including zero,
for any nonnegative scale and arbitrary absolute prime coefficients. -/
theorem transfer_limit (w : ℝ → ℝ) (k : ℕ) (scale : ℝ → NNReal) (c : ℝ) :
    Tendsto (fun X => (scale X : ℝ) * (moment w k X / Real.log X ^ k)) atTop (𝓝 c) ↔
    Tendsto (fun X => (scale X : ℝ) * moment w 0 X) atTop (𝓝 c) := by
  have hr := log_ratio.pow k
  rw [one_pow] at hr
  constructor
  · intro ht
    have hl := ht.div hr one_ne_zero
    rw [div_one] at hl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl ht ?_ ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      have hX₂ : 1 < 2*X := by linarith only [hX]
      apply (div_le_iff₀ (pow_pos (div_pos (Real.log_pos hX₂) (Real.log_pos hX)) k)).2
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (divided_bounds w k hX).2 (scale X).property
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      exact mul_le_mul_of_nonneg_left (divided_bounds w k hX).1 (scale X).property
  · intro ht
    have hu := ht.mul hr
    rw [mul_one] at hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ht hu ?_ ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      exact mul_le_mul_of_nonneg_left (divided_bounds w k hX).1 (scale X).property
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      change _ ≤ (scale X : ℝ) * moment w 0 X * _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (divided_bounds w k hX).2 (scale X).property

private theorem log_mass {X : ℝ} (hX : 1<X) :
    moment Real.log 0 X = Chebyshev.theta (2*X)-Chebyshev.theta X := by
  rw [chebyshevTheta_sub_eq_shellSum (Nat.floor_mono (by linarith only [hX] : X ≤ 2*X))]
  unfold moment primeCountSum
  apply sum_congr rfl
  intro p hp
  obtain ⟨_,h₁,_⟩ := mem_shell_of_mem_filter (one_pos.trans hX).le hp
  simp only [pow_zero,mul_one,abs_of_nonneg (Real.log_nonneg (hX.trans h₁).le)]

/-- With prime coefficient b(p)=log p, the unweighted dyadic mass is
asymptotic to X and its k-th log moment is asymptotic to X(log X)^k. -/
theorem log_moment_asymptotic (k : ℕ) :
    Tendsto (fun X => moment Real.log k X / (X*Real.log X^k)) atTop (𝓝 1) := by
  let scale (X : ℝ) : NNReal := (Real.toNNReal X)⁻¹
  have h₀ := (tendsto_chebyshevTheta_div (c := 2) two_pos).sub
    (tendsto_chebyshevTheta_div (c := 1) one_pos)
  norm_num only [one_mul,show (2:ℝ)-1=1 by norm_num] at h₀
  have ht : Tendsto (fun X => (scale X : ℝ)*moment Real.log 0 X) atTop (𝓝 1) := by
    refine h₀.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hx := one_pos.trans hX
    simp only [scale,NNReal.coe_inv,Real.coe_toNNReal _ hx.le,log_mass hX]
    ring
  apply ((transfer_limit Real.log k scale 1).2 ht).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  simp only [scale,NNReal.coe_inv,Real.coe_toNNReal _ (one_pos.trans hX).le]
  ring

/-- The unweighted O(X) prime estimate alone can lose a whole logarithm
in the proposed X log X bound for a second logarithmic moment. -/
theorem second_moment_excess :
    Tendsto (fun X => moment Real.log 2 X / (X*Real.log X)) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop one_pos (log_moment_asymptotic 2) Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hl := (Real.log_pos hX).ne'
  field_simp

end GaloisForLFunctions.PrimeExponentialSums.PrimeMoments

#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.window_bounds
#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.transfer_limit
#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.log_moment_asymptotic
#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.second_moment_excess
