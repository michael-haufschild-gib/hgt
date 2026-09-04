import GaloisForLFunctions.HTGeometry.StrelitzMaximumSlopeTouching
import GaloisForLFunctions.HTGeometry.StrelitzMaximumSlopeGrowth

/-!
# Strelitz's enlarged maximum-modulus set

For an entire coefficient sum, the enlarged set uses the source's large-value threshold and its
two broad logarithmic-derivative bounds.  The right logarithmic maximum slope is the source's
`K(r)` and the left slope is `K(r-0)`, after changing from radius `r` to logarithmic radius.

Infinite coefficient support makes both one-sided slopes and the maximum norm exceed one
eventually.  The touching-slope sandwich then puts every sufficiently large circle's genuine
maximum point in the enlarged set.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Set

noncomputable section

/-- Infinite coefficient support forces the exact left logarithmic maximum slope to diverge. -/
theorem tendsto_strelitzMaximumLeftSlope_atTop
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    Tendsto (strelitzMaximumLeftSlope a) atTop atTop := by
  obtain ⟨n₀, _, hn₀⟩ := htrans 0
  have hK := tendsto_strelitzMaximumSlope_atTop ha htrans
  rw [tendsto_atTop] at hK ⊢
  intro B
  obtain ⟨X, hX⟩ := (eventually_atTop.1 (hK B))
  filter_upwards [eventually_ge_atTop (X + 1)] with x hx
  calc
    B ≤ strelitzMaximumSlope a (x - 1) := hX (x - 1) (by linarith)
    _ ≤ slope (strelitzLogMaximum a) (x - 1) x :=
      strelitzMaximumSlope_le_slope ha hn₀ (by linarith)
    _ = slope (strelitzLogMaximum a) x (x - 1) := slope_comm _ _ _
    _ ≤ strelitzMaximumLeftSlope a x :=
      slope_le_convexLeftSlope (convexOn_strelitzLogMaximum ha hn₀) (by linarith)

/-- Infinite coefficient support forces the exact circle maximum above one at every sufficiently
large logarithmic radius. -/
theorem eventually_one_lt_coeffCircleMaximumNorm_exp
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 1 < coeffCircleMaximumNorm a (Real.exp x) := by
  obtain ⟨n, hn, han⟩ := htrans 1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have harg : Tendsto (fun x : ℝ => (n : ℝ) * x) atTop atTop :=
    tendsto_id.const_mul_atTop hnR
  have hexp : Tendsto (fun x : ℝ => Real.exp ((n : ℝ) * x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp harg
  have hterm : Tendsto (fun x : ℝ => ‖a n‖ * Real.exp ((n : ℝ) * x)) atTop atTop :=
    hexp.const_mul_atTop (norm_pos_iff.mpr han)
  filter_upwards [hterm.eventually_gt_atTop 1] with x hx
  have hmax := term_le_maxTerm ha (Real.exp_pos x) n
  have hcircle := maxTerm_le_coeffCircleMaximumNorm ha (Real.exp_pos x)
  have heq : Real.exp x ^ n = Real.exp ((n : ℝ) * x) := by
    rw [← Real.exp_nat_mul]
  rw [heq] at hmax
  exact hx.trans_le (hmax.trans hcircle)

/-- Strelitz's enlarged set in logarithmic-radius coordinates.  Its three strict inequalities are
the large-value condition and the `K(r-0)^(-1/3)`, `K(r)^(5/3)` logarithmic-derivative bounds. -/
def strelitzEnlargedSet (a : ℕ → ℂ) (s : ℕ) : Set ℂ :=
  {z | 0 < ‖z‖ ∧
    coeffCircleMaximumNorm a ‖z‖ ^ (1 - 1 / (4 * (s : ℝ))) < ‖coeffFun a z‖ ∧
    strelitzMaximumLeftSlope a (Real.log ‖z‖) ^ (-(1 : ℝ) / 3) <
      ‖eulerLogDeriv (coeffFun a) z‖ ∧
    ‖eulerLogDeriv (coeffFun a) z‖ <
      strelitzMaximumSlope a (Real.log ‖z‖) ^ ((5 : ℝ) / 3)}

/-- Every sufficiently large circle has a maximum-modulus point in Strelitz's enlarged set. -/
theorem eventually_exists_maximumPoint_mem_strelitzEnlargedSet
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {s : ℕ} (hs : 1 ≤ s) :
    ∀ᶠ x : ℝ in atTop, ∃ z ∈ strelitzEnlargedSet a s,
      z ∈ circleMaximumSet (coeffFun a) ∧ ‖z‖ = Real.exp x := by
  obtain ⟨n₀, _, hn₀⟩ := htrans 0
  have hKL := tendsto_strelitzMaximumLeftSlope_atTop ha htrans
  have hKR := tendsto_strelitzMaximumSlope_atTop ha htrans
  filter_upwards [eventually_one_lt_coeffCircleMaximumNorm_exp ha htrans,
      hKL.eventually_gt_atTop 1, hKR.eventually_gt_atTop 1] with x hM hKL1 hKR1
  obtain ⟨z, hmax, hnorm⟩ := exists_mem_circleMaximumSet_of_pos ha (Real.exp_pos x)
  have hz : 0 < ‖z‖ := by rw [hnorm]; exact Real.exp_pos x
  have hnormeq :=
    (mem_circleMaximumSet_iff_norm_eq_coeffCircleMaximumNorm ha hz).mp hmax
  have hfz : coeffFun a z ≠ 0 := by
    rw [← norm_ne_zero_iff, hnormeq]
    exact ne_of_gt (coeffCircleMaximumNorm_pos ha hn₀ hz)
  have huim := eulerLogDeriv_im_eq_zero_of_mem_circleMaximumSet
    ha (norm_ne_zero_iff.mp (ne_of_gt hz)) hfz hmax
  have hsand := strelitzMaximumSlope_sandwich_of_mem_circleMaximumSet ha hn₀ hz hmax
  have hlognorm : Real.log ‖z‖ = x := by rw [hnorm, Real.log_exp]
  rw [hlognorm] at hsand
  have hurepos : 0 < (eulerLogDeriv (coeffFun a) z).re :=
    zero_lt_one.trans (hKL1.trans_le hsand.1)
  have hunorm : ‖eulerLogDeriv (coeffFun a) z‖ =
      (eulerLogDeriv (coeffFun a) z).re := by
    rw [Complex.norm_def, Complex.normSq_apply, huim]
    norm_num
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hurepos]
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  have hexpM : 1 - 1 / (4 * (s : ℝ)) < (1 : ℝ) := by
    have : 0 < 1 / (4 * (s : ℝ)) := by positivity
    linarith
  have hlarge : coeffCircleMaximumNorm a ‖z‖ ^ (1 - 1 / (4 * (s : ℝ))) <
      ‖coeffFun a z‖ := by
    rw [hnorm] at hnormeq
    rw [hnorm, hnormeq]
    simpa using Real.rpow_lt_rpow_of_exponent_lt hM hexpM
  have hlower : strelitzMaximumLeftSlope a (Real.log ‖z‖) ^ (-(1 : ℝ) / 3) <
      ‖eulerLogDeriv (coeffFun a) z‖ := by
    rw [hlognorm, hunorm]
    have hp : (-(1 : ℝ) / 3) < 1 := by norm_num
    have hpow : strelitzMaximumLeftSlope a x ^ (-(1 : ℝ) / 3) <
        strelitzMaximumLeftSlope a x := by
      simpa using Real.rpow_lt_rpow_of_exponent_lt hKL1 hp
    exact hpow.trans_le hsand.1
  have hupper : ‖eulerLogDeriv (coeffFun a) z‖ <
      strelitzMaximumSlope a (Real.log ‖z‖) ^ ((5 : ℝ) / 3) := by
    rw [hlognorm, hunorm]
    have hp : (1 : ℝ) < 5 / 3 := by norm_num
    have hpow : strelitzMaximumSlope a x <
        strelitzMaximumSlope a x ^ ((5 : ℝ) / 3) := by
      simpa using Real.rpow_lt_rpow_of_exponent_lt hKR1 hp
    exact hsand.2.trans_lt hpow
  exact ⟨z, ⟨hz, hlarge, hlower, hupper⟩, hmax, hnorm⟩

/-- In ordinary radius coordinates, every sufficiently large circle meets Strelitz's enlarged
set at a genuine maximum-modulus point. -/
theorem eventually_exists_maximumPoint_mem_strelitzEnlargedSet_of_radius
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {s : ℕ} (hs : 1 ≤ s) :
    ∀ᶠ r : ℝ in atTop, ∃ z ∈ strelitzEnlargedSet a s,
      z ∈ circleMaximumSet (coeffFun a) ∧ ‖z‖ = r := by
  have hx := eventually_exists_maximumPoint_mem_strelitzEnlargedSet ha htrans hs
  have hr := Real.tendsto_log_atTop.eventually hx
  filter_upwards [hr, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  obtain ⟨z, hzH, hzmax, hznorm⟩ := hr
  refine ⟨z, hzH, hzmax, ?_⟩
  simpa [Real.exp_log hrpos] using hznorm

end

end GaloisForLFunctions.HTGeometry
