import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Tactic

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry.TwoMarkPolynomialApproximation

noncomputable def approximant (n : ℕ) (z : ℂ) : ℂ :=
  (z - 1) * (1 + z / (n + 1 : ℂ)) ^ (n + 1)

noncomputable def approximantPolynomial (n : ℕ) : ℂ[X] :=
  (X - 1) * (1 + X * C ((n + 1 : ℂ)⁻¹)) ^ (n + 1)

@[simp] theorem eval_approximantPolynomial (n : ℕ) (z : ℂ) :
    (approximantPolynomial n).eval z = approximant n z := by
  simp only [approximantPolynomial, eval_mul, eval_sub, eval_X, eval_one, eval_pow,
    eval_add, eval_C, approximant, div_eq_mul_inv]

private theorem successor_ne_zero (n : ℕ) : (n + 1 : ℂ) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

theorem hasDerivAt_approximant (n : ℕ) (z : ℂ) :
    HasDerivAt (approximant n)
      (((n + 2 : ℂ) / (n + 1 : ℂ)) * z * (1 + z / (n + 1 : ℂ)) ^ n) z := by
  have h := ((hasDerivAt_id z).sub_const 1).mul
    (((hasDerivAt_id z).div_const (n + 1 : ℂ)).const_add 1 |>.pow (n + 1))
  apply h.congr_deriv
  dsimp
  simp only [Nat.cast_add, Nat.cast_one, one_mul, pow_succ]
  field_simp [successor_ne_zero n]
  ring

theorem approximant_eq_zero_iff (n : ℕ) (z : ℂ) :
    approximant n z = 0 ↔ z = 1 ∨ z = -(n + 1 : ℂ) := by
  have hb : 1 + z / (n + 1 : ℂ) = 0 ↔ z = -(n + 1 : ℂ) := by
    constructor
    · intro h
      field_simp [successor_ne_zero n] at h
      linear_combination h
    · intro h
      rw [h]
      field_simp [successor_ne_zero n]
      ring
  simp only [approximant, mul_eq_zero, pow_eq_zero_iff (Nat.succ_ne_zero n), sub_eq_zero, hb]

@[simp] theorem approximant_zero (n : ℕ) : approximant n 0 = -1 := by
  simp [approximant]

theorem critical_value_mem_marks (n : ℕ) (z : ℂ)
    (hz : deriv (approximant n) z = 0) :
    approximant n z = 0 ∨ approximant n z = -1 := by
  rw [(hasDerivAt_approximant n z).deriv] at hz
  have hc : ((n + 2 : ℂ) / (n + 1 : ℂ)) ≠ 0 := by
    apply div_ne_zero _ (successor_ne_zero n)
    exact_mod_cast (by omega : n + 2 ≠ 0)
  rcases mul_eq_zero.mp hz with h | h
  · have hz0 : z = 0 := (mul_eq_zero.mp h).resolve_left hc
    exact Or.inr (hz0 ▸ approximant_zero n)
  · have hb := eq_zero_of_pow_eq_zero h
    exact Or.inl (by simp [approximant, hb])

theorem isCoveringMapOn_approximant (n : ℕ) :
    IsCoveringMapOn (approximant n) {z : ℂ | z ≠ 0 ∧ z ≠ -1} := by
  have h := (approximantPolynomial n).isCoveringMapOn_eval
  simp only [eval_approximantPolynomial] at h
  apply h.mono
  intro w hw
  rintro ⟨z, hz, rfl⟩
  have hd : deriv (approximant n) z = 0 := by
    have hh := (approximantPolynomial n).hasDerivAt z
    simp only [eval_approximantPolynomial] at hh
    exact hh.deriv.trans hz
  rcases critical_value_mem_marks n z hd with h0 | h1
  · exact hw.1 h0
  · exact hw.2 h1

/-- Quantitative uniform control of the binomial approximation on a disk. -/
theorem norm_binomial_sub_exp_le (m : ℕ) (hm : 0 < m) {R : ℝ}
    (hlarge : 2 * R ≤ (m : ℝ)) (hsq : R ^ 2 ≤ (m : ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(1 + z / (m : ℂ)) ^ m - Complex.exp z‖ ≤ 2 * Real.exp R * R ^ 2 / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  let w : ℂ := z / m
  have hwR : ‖w‖ ≤ R / m := by
    dsimp [w]
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right hz hmR.le
  have hw : ‖w‖ ≤ 1 / 2 := hwR.trans ((div_le_iff₀ hmR).mpr (by linarith))
  have hi : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖w‖) (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith
  have hl : ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 :=
        Complex.norm_log_one_add_sub_self_le (by linarith)
      _ ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖w‖ ^ 2 := by ring
  let δ : ℂ := (m : ℂ) * (Complex.log (1 + w) - w)
  have hd : ‖δ‖ ≤ R ^ 2 / m := by
    calc
      ‖δ‖ = (m : ℝ) * ‖Complex.log (1 + w) - w‖ := by simp [δ]
      _ ≤ (m : ℝ) * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_left hl hmR.le
      _ ≤ (m : ℝ) * (R / m) ^ 2 := by gcongr
      _ = R ^ 2 / m := by field_simp
  have hd1 : ‖δ‖ ≤ 1 := hd.trans ((div_le_iff₀ hmR).mpr (by simpa using hsq))
  have hb : 1 + w ≠ 0 := by
    intro h
    have hh : w = -1 := by linear_combination h
    rw [hh, norm_neg, norm_one] at hw
    norm_num at hw
  have hexp : (1 + w) ^ m = Complex.exp z * Complex.exp δ := by
    calc
      _ = Complex.exp ((m : ℂ) * Complex.log (1 + w)) := by
        rw [Complex.exp_nat_mul, Complex.exp_log hb]
      _ = Complex.exp (z + δ) := by
        congr 1
        dsimp [δ, w]
        field_simp [hmC]
        ring
      _ = _ := Complex.exp_add _ _
  calc
    _ = ‖Complex.exp z * (Complex.exp δ - 1)‖ := by
      change ‖(1 + w) ^ m - Complex.exp z‖ = _
      rw [hexp]
      congr 1
      ring
    _ = ‖Complex.exp z‖ * ‖Complex.exp δ - 1‖ := norm_mul _ _
    _ ≤ Real.exp R * (2 * (R ^ 2 / m)) := by
      gcongr
      · exact (Complex.norm_exp_le_exp_norm z).trans (Real.exp_le_exp.mpr hz)
      · exact (Complex.norm_exp_sub_one_le hd1).trans (mul_le_mul_of_nonneg_left hd (by norm_num))
    _ = _ := by ring

/-- The limiting entire end model. -/
noncomputable def limitMap (z : ℂ) : ℂ := (z - 1) * Complex.exp z

/-- An explicit common error bound on each fixed disk. -/
theorem norm_approximant_sub_limit_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hlarge : 2 * R ≤ (n : ℝ) + 1) (hsq : R ^ 2 ≤ (n : ℝ) + 1)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖approximant n z - limitMap z‖ ≤ 2 * (R + 1) * Real.exp R * R ^ 2 / (n + 1) := by
  have hb := norm_binomial_sub_exp_le (n + 1) (Nat.succ_pos n)
    (by exact_mod_cast hlarge) (by exact_mod_cast hsq) hz
  have hz1 : ‖z - 1‖ ≤ R + 1 := by
    calc
      _ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 1 := by simpa using add_le_add_right hz 1
  calc
    _ = ‖z - 1‖ * ‖(1 + z / (n + 1 : ℂ)) ^ (n + 1) - Complex.exp z‖ := by
      rw [← norm_mul]
      congr 1
      simp only [approximant, limitMap]
      ring
    _ ≤ (R + 1) * (2 * Real.exp R * R ^ 2 / (n + 1)) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using hb
    _ = _ := by ring

/-- Uniform convergence holds on every disk, not merely pointwise. -/
theorem tendstoUniformlyOn_approximant_closedBall {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn approximant limitMap atTop (Metric.closedBall (0 : ℂ) R) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun n : ℕ =>
      2 * (R + 1) * Real.exp R * R ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2 * (R + 1) * Real.exp R * R ^ 2)
  filter_upwards [hlim.eventually (gt_mem_nhds hε),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * R),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (R ^ 2)] with n hn hn₁ hn₂
  intro z hz
  have hzR : ‖z‖ ≤ R := by simpa using hz
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_approximant_sub_limit_le n hR (by linarith) (by linarith) hzR).trans_lt hn

/-- The finite two-mark coverings converge locally uniformly on the whole plane. -/
theorem tendstoLocallyUniformly_approximant :
    TendstoLocallyUniformly approximant limitMap atTop := by
  intro u hu z
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨Metric.closedBall (0 : ℂ) R, ?_,
    tendstoUniformlyOn_approximant_closedBall hR u hu⟩
  apply mem_of_superset (Metric.closedBall_mem_nhds z (by norm_num : (0 : ℝ) < 1))
  intro y hy
  have hyz : ‖y - z‖ ≤ 1 := by simpa [dist_eq_norm] using hy
  have hh : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
    simpa using norm_add_le (y - z) z
  simpa [R] using (show ‖y‖ ≤ ‖z‖ + 1 by linarith)

end GaloisForLFunctions.HTGeometry.TwoMarkPolynomialApproximation
