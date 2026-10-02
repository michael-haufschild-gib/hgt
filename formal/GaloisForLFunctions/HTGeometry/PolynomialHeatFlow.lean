import GaloisForLFunctions.HTGeometry.LaguerreShiftRealRootCount
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Algebra.Polynomial

/-!
# The heat flow of a real polynomial as a limit of heat steps

For a real polynomial `p` and `τ ∈ ℝ`, the heat flow is the finite sum
`e^{−τD²}p = Σ_k (−τ)^k/k! · p^{(2k)}` (`polyHeat`).  It is the limit of `n` heat steps of size
`τ/n`: by the binomial theorem for the commuting operators `1` and `D²`,
`(1 − (τ/n)D²)ⁿ p = Σ_k C(n,k)(−τ/n)^k p^{(2k)}` (`heatStepOp_pow_apply`), and
`C(n,k)/n^k → 1/k!`.  The convergence holds for the evaluations on `ℂ`, locally uniformly
(`tendstoLocallyUniformly_eval_heatStepOp_pow`).
-/

open Polynomial Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The operator `D²` on real polynomials. -/
def derivSq : Module.End ℝ ℝ[X] := (derivative : ℝ[X] →ₗ[ℝ] ℝ[X]) ^ 2

theorem derivSq_pow_apply (k : ℕ) (p : ℝ[X]) : (derivSq ^ k) p = derivative^[2 * k] p := by
  rw [derivSq, ← pow_mul, Module.End.pow_apply]

/-- The heat step `1 − aD²`. -/
def heatStepOp (a : ℝ) : Module.End ℝ ℝ[X] := 1 - a • derivSq

theorem heatStepOp_apply (a : ℝ) (p : ℝ[X]) :
    heatStepOp a p = p - C a * derivative (derivative p) := by
  have h := derivSq_pow_apply 1 p
  rw [pow_one] at h
  simp only [heatStepOp, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, h,
    smul_eq_C_mul]
  rfl

/-- **Binomial expansion of `n` heat steps.** -/
theorem heatStepOp_pow_apply (a : ℝ) (n : ℕ) (p : ℝ[X]) :
    (heatStepOp a ^ n) p =
      ∑ k ∈ range (n + 1), C ((n.choose k : ℝ) * (-a) ^ k) * derivative^[2 * k] p := by
  have hc : Commute ((-a) • derivSq) (1 : Module.End ℝ ℝ[X]) := Commute.one_right _
  have e : heatStepOp a = (-a) • derivSq + 1 := by
    rw [heatStepOp]
    module
  rw [e, hc.add_pow n, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, _root_.smul_pow, Module.End.mul_apply, LinearMap.smul_apply]
  rw [show ((n.choose k : Module.End ℝ ℝ[X])) p = (n.choose k : ℝ) • p by
    rw [_root_.Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]]
  rw [map_smul, smul_smul, derivSq_pow_apply, smul_eq_C_mul, mul_comm ((-a) ^ k)]

/-- The heat flow `e^{−τD²}p = Σ_k (−τ)^k/k! · p^{(2k)}`. -/
def polyHeat (τ : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree + 1), C ((-τ) ^ k / (k.factorial : ℝ)) * derivative^[2 * k] p

/-- The `n`-step approximant, written over the fixed range `k ≤ deg p`. -/
theorem heatStepOp_pow_apply_eq (a : ℝ) (n : ℕ) (p : ℝ[X]) :
    (heatStepOp a ^ n) p =
      ∑ k ∈ range (p.natDegree + 1), C ((n.choose k : ℝ) * (-a) ^ k) * derivative^[2 * k] p := by
  rw [heatStepOp_pow_apply]
  set M := max n p.natDegree + 1
  have h1 : range (n + 1) ⊆ range M := range_subset_range.mpr (by omega)
  have h2 : range (p.natDegree + 1) ⊆ range M := range_subset_range.mpr (by omega)
  rw [Finset.sum_subset h1 (fun k hk hk' => ?_), Finset.sum_subset h2 (fun k hk hk' => ?_)]
  · simp only [mem_range, not_lt] at hk'
    rw [iterate_derivative_eq_zero (by omega), mul_zero]
  · simp only [mem_range, not_lt] at hk'
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, C_0, zero_mul]

/-! ## The scalar limit -/

theorem tendsto_descFactorial_div_pow (k : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial k : ℝ) / (n : ℝ) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : Tendsto (fun n : ℕ => 1 - (k : ℝ) / n) atTop (𝓝 1) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)).const_sub 1
      simpa using this
    have h := h1.mul ih
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop k] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      exact this.ne'
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hn.le, pow_succ]
    field_simp

theorem tendsto_choose_mul_pow (τ : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) * (-(τ / n)) ^ k) atTop
      (𝓝 ((-τ) ^ k / (k.factorial : ℝ))) := by
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h := (tendsto_descFactorial_div_pow k).const_mul ((-τ) ^ k / (k.factorial : ℝ))
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, neg_div', div_pow]
  field_simp

/-! ## Locally uniform convergence of the evaluations -/

theorem eval_map_sum_C_mul (c : ℕ → ℝ) (q : ℕ → ℝ[X]) (N : ℕ) (z : ℂ) :
    ((∑ k ∈ range N, C (c k) * q k).map Complex.ofRealHom).eval z =
      ∑ k ∈ range N, (c k : ℂ) * ((q k).map Complex.ofRealHom).eval z := by
  simp [Polynomial.map_sum, Polynomial.eval_finsetSum, Polynomial.map_mul]

/-- **The heat steps converge to the heat flow**, locally uniformly on `ℂ`. -/
theorem tendstoLocallyUniformly_eval_heatStepOp_pow (τ : ℝ) (p : ℝ[X]) :
    TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) => (((heatStepOp (τ / n) ^ n) p).map Complex.ofRealHom).eval z)
      (fun z => ((polyHeat τ p).map Complex.ofRealHom).eval z) atTop := by
  set N := p.natDegree + 1
  set q : ℕ → ℝ[X] := fun k => derivative^[2 * k] p
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- a bound for the fixed polynomials on `K`
  have hbound : ∀ k, ∃ B, 0 ≤ B ∧ ∀ z ∈ K, ‖((q k).map Complex.ofRealHom).eval z‖ ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      ((q k).map Complex.ofRealHom).continuous.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun z hz => (hB z hz).trans (le_max_left _ _)⟩
  choose B hB0 hB using hbound
  set Bs := ∑ k ∈ range N, B k + 1
  have hBs : 0 < Bs := by have := Finset.sum_nonneg (fun k (_ : k ∈ range N) => hB0 k); linarith
  have hev : ∀ k ∈ range N, ∀ᶠ n : ℕ in atTop,
      |(n.choose k : ℝ) * (-(τ / n)) ^ k - (-τ) ^ k / (k.factorial : ℝ)| < ε / Bs := by
    intro k _
    have h := (tendsto_choose_mul_pow τ k)
    rw [Metric.tendsto_nhds] at h
    filter_upwards [h (ε / Bs) (by positivity)] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [(Filter.eventually_all_finset (range N)).mpr hev] with n hn z hz
  rw [heatStepOp_pow_apply_eq, polyHeat, dist_eq_norm, eval_map_sum_C_mul, eval_map_sum_C_mul,
    ← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ range N, (((-τ) ^ k / (k.factorial : ℝ) : ℝ) * ((q k).map Complex.ofRealHom).eval z -
        (((n.choose k : ℝ) * (-(τ / n)) ^ k : ℝ) : ℂ) * ((q k).map Complex.ofRealHom).eval z)‖
      ≤ ∑ k ∈ range N, ε / Bs * B k := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_sub_comm]
        exact mul_le_mul (hn k hk).le (hB k z hz) (norm_nonneg _) (by positivity)
    _ = ε / Bs * ∑ k ∈ range N, B k := by rw [Finset.mul_sum]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hBs]
        nlinarith

end

end GaloisForLFunctions.HTGeometry
