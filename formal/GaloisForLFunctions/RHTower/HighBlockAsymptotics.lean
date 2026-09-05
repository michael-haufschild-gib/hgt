import GaloisForLFunctions.RHTower.HighBlockBlockCore

/-!
# High-block law: the elementary asymptotics of the error terms

`K U^{−κ} (log U)^n → 0` for `κ > 0` (via `log U ≤ U^e/e`), and
`U^{1/10} e^{−2U^{1/4}} → 0` (via `e^y ≥ y⁴/4!`). These discharge every error term of the block
estimate for large `U`.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem tendsto_const_mul_rpow_neg_mul_log_pow (K κ : ℝ) (hκ : 0 < κ) (n : ℕ) :
    Tendsto (fun U : ℝ => K * (U ^ (-κ) * Real.log U ^ n)) atTop (𝓝 0) := by
  set e : ℝ := κ / (2 * ((n : ℝ) + 1)) with he
  have he0 : 0 < e := by positivity
  have hmajor : Tendsto (fun U : ℝ => (|K| / e ^ n) * U ^ (-(κ / 2))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < κ / 2)).const_mul (|K| / e ^ n)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [Filter.eventually_ge_atTop 1] with U hU
  have hU0 : 0 < U := by linarith
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hlog : Real.log U ≤ U ^ e / e := Real.log_le_rpow_div hU0.le he0
  have hlog0 : 0 ≤ Real.log U := Real.log_nonneg hU
  have hen : e * n ≤ κ / 2 := by
    rw [he]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hlogn : |Real.log U ^ n| ≤ U ^ (κ / 2) / e ^ n := by
    rw [abs_of_nonneg (pow_nonneg hlog0 n)]
    calc Real.log U ^ n ≤ (U ^ e / e) ^ n := pow_le_pow_left₀ hlog0 hlog n
      _ = (U ^ e) ^ n / e ^ n := div_pow _ _ _
      _ = U ^ (e * n) / e ^ n := by rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      _ ≤ U ^ (κ / 2) / e ^ n := by
          gcongr
          all_goals exact Real.rpow_le_rpow_of_exponent_le hU hen
  have hUκ : 0 ≤ U ^ (-κ) := by positivity
  calc |K| * (|U ^ (-κ)| * |Real.log U ^ n|)
      ≤ |K| * (U ^ (-κ) * (U ^ (κ / 2) / e ^ n)) := by
        rw [abs_of_nonneg hUκ]
        gcongr
    _ = (|K| / e ^ n) * U ^ (-(κ / 2)) := by
        rw [show U ^ (-κ) * (U ^ (κ / 2) / e ^ n) = (U ^ (-κ) * U ^ (κ / 2)) / e ^ n by ring,
          ← Real.rpow_add hU0, show -κ + κ / 2 = -(κ / 2) by ring]
        ring

theorem eventually_const_mul_rpow_neg_mul_log_pow_le (K κ : ℝ) (hκ : 0 < κ) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ U in atTop, K * (U ^ (-κ) * Real.log U ^ n) ≤ ε :=
  (tendsto_const_mul_rpow_neg_mul_log_pow K κ hκ n).eventually_le_const hε

theorem eventually_const_mul_rpow_neg_le (K κ : ℝ) (hκ : 0 < κ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U in atTop, K * U ^ (-κ) ≤ ε := by
  have := eventually_const_mul_rpow_neg_mul_log_pow_le K κ hκ 0 hε
  filter_upwards [this] with U hU
  simpa using hU

/-- `U^{1/10} e^{−2U^{1/4}} ≤ (3/2) U^{−9/10}` for `U > 0`. -/
theorem hb_rpow_mul_exp_neg_le {U : ℝ} (hU : 0 < U) :
    U ^ ((1 : ℝ) / 10) * Real.exp (-(2 * U ^ ((1 : ℝ) / 4))) ≤ (3 / 2) * U ^ (-((9 : ℝ) / 10)) := by
  set y : ℝ := 2 * U ^ ((1 : ℝ) / 4) with hy
  have hy0 : 0 ≤ y := by positivity
  have hexp := Real.pow_div_factorial_le_exp y hy0 4
  have hy4 : y ^ 4 = 16 * U := by
    have h1 : (U ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = U := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU.le]
      norm_num
    rw [hy, mul_pow, h1]
    norm_num
  have hfac : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac, hy4] at hexp
  -- exp(−y) ≤ 24/(16 U)
  have hpos : 0 < Real.exp y := Real.exp_pos y
  have hneg : Real.exp (-y) ≤ 24 / (16 * U) := by
    rw [Real.exp_neg, inv_le_comm₀ hpos (by positivity), inv_div]
    have h16 : 16 * U / 24 ≤ Real.exp y := by linarith
    exact h16
  calc U ^ ((1 : ℝ) / 10) * Real.exp (-y) ≤ U ^ ((1 : ℝ) / 10) * (24 / (16 * U)) :=
        mul_le_mul_of_nonneg_left hneg (by positivity)
    _ = (3 / 2) * (U ^ ((1 : ℝ) / 10) * U ^ (-(1 : ℝ))) := by
        rw [Real.rpow_neg_one]
        field_simp
        ring
    _ = (3 / 2) * U ^ (-((9 : ℝ) / 10)) := by
        rw [← Real.rpow_add hU]
        norm_num

theorem eventually_rpow_mul_exp_neg_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U in atTop, U ^ ((1 : ℝ) / 10) * Real.exp (-(2 * U ^ ((1 : ℝ) / 4))) ≤ ε := by
  filter_upwards [eventually_const_mul_rpow_neg_le (3 / 2) ((9 : ℝ) / 10) (by norm_num) hε,
    Filter.eventually_gt_atTop 0] with U hU hU0
  exact (hb_rpow_mul_exp_neg_le hU0).trans hU

end

end RHTower
