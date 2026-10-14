import GaloisForLFunctions.RHTower.ModularArcDyadicCriticalLineQuadraticCoercivity

/-!
# All-orders logarithmic energy moment hierarchy, Turán–Hankel log-convexity, and all-orders polynomial coercivity across `(−1/2, 1/2)` for the infinite-horizon dyadic modular arc tower

In `ModularArcDyadicOriginInfinityTransversality` and
`ModularArcDyadicCriticalLineQuadraticCoercivity`, we studied the first and second logarithmic
energy moments `M₁ = ∫_{v > 0} v (Φ_k(v))² dv` and `M₂ = ∫_{v > 0} v² (Φ_k(v))² dv` of the
infinite-horizon dyadic profile `Φ_k = arcLineInfiniteDyadicProfile k ν` and line vector
`V_k = arcLineInfiniteDyadicVector k ν`.

In this module we establish the complete **all-orders logarithmic energy moment hierarchy**
`M_n(k, ν) = ∫_{v > 0} v^n (Φ_k(v))² dv` (`n ∈ ℕ`), proving its factorial-exponential regularity,
strict positivity, origin–infinity equipartition, universal **Turán–Hankel log-convexity**, and
**all-orders polynomial coercivity lower bounds** on the strip-weighted Hilbert energy across the
entire open critical strip `|l| < 1/2`:

1. **Elementary factorial-exponential envelopes and hyperbolic lower bounds
   (`pow_le_factorial_mul_exp_nonneg`, `abs_pow_le_factorial_mul_four_pow_mul_exp_quarter`,
   `pow_div_factorial_le_exp_sub_one`, `exp_sub_one_div_two_le_sinh`,
   `pow_div_two_mul_factorial_le_sinh`, `abs_pow_div_two_mul_factorial_le_abs_sinh`,
   `pow_two_mul_div_two_mul_factorial_sq_le_two_mul_sinh_sq`):**
   - For all `n ∈ ℕ` and `v ∈ ℝ`, `|v|^n ≤ n! · 4^n · exp((1/4) |v|)`.
   - For all `n ≥ 1` and `u ≥ 0`, `u^n / n! ≤ exp u − 1` and `u^n / (2 · n!) ≤ sinh u`.
   - For all `m ≥ 1` and `u ∈ ℝ`, `u^{2m} / (2 · (m!)²) ≤ 2 (sinh u)²`.
2. **All-orders integrability, origin–infinity equipartition, factorial upper bounds, and strict
   positivity (`abs_pow_mul_sq_arcLineInfiniteDyadicProfile_le`,
   `integrable_abs_pow_mul_sq_arcLineInfiniteDyadicProfile`,
   `integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi`,
   `integral_pow_two_mul_add_one_mul_sq_arcLineInfiniteDyadicProfile_eq_zero`,
   `setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_le_factorial`,
   `setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_pos`):**
   - For every `n ∈ ℕ`,
     `∫_{x > 0} |log x|^n (V_k(x))² dx = ∫_ℝ |v|^n (Φ_k(v))² dv = 2 ∫_{v > 0} v^n (Φ_k(v))² dv`,
     `∫_{x > 1} (log x)^n (V_k(x))² dx = ∫_{x ∈ (0, 1]} |log x|^n (V_k(x))² dx = ∫_{v > 0} v^n (Φ_k(v))² dv`,
     and for every odd order `2m + 1`, `∫_ℝ v^{2m+1} (Φ_k(v))² dv = 0`.
   - For every `n ∈ ℕ`, `0 < ∫_{v > 0} v^n (Φ_k(v))² dv ≤ 2722500 · (ν.real univ)² · n! · 4^n`.
3. **Universal Turán–Hankel log-convexity across all orders `n ∈ ℕ`
   (`sq_setIntegral_Ioi_zero_pow_succ_mul_sq_le`,
   `sq_setIntegral_Ioi_abs_log_pow_succ_mul_sq_le`):**
   - For every `n ∈ ℕ`,
     `(∫_{v > 0} v^{n+1} (Φ_k(v))² dv)² ≤ (∫_{v > 0} v^n (Φ_k(v))² dv) · (∫_{v > 0} v^{n+2} (Φ_k(v))² dv)`
     and
     `(∫_{x > 0} |log x|^{n+1} (V_k(x))² dx)² ≤ (∫_{x > 0} |log x|^n (V_k(x))² dx) · (∫_{x > 0} |log x|^{n+2} (V_k(x))² dx)`.
4. **All-orders polynomial coercivity lower bounds across the open critical strip `|l| < 1/2`
   (`pow_mul_div_factorial_le_sub_Ioi_one`,
   `abs_pow_mul_div_factorial_le_abs_imbalance`,
   `pow_two_mul_div_two_mul_factorial_sq_le_excess`,
   `exists_dyadic_logarithmicMoment_hierarchy_arcWitness`):**
   - For every `n ≥ 1` and `|l| < 1/2`,
     `((2|l|)^n / n!) · ∫_{v > 0} v^n (Φ_k(v))² dv ≤ |E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)|`.
   - For every `m ≥ 1` and `|l| < 1/2`,
     `(l^{2m} / (2 · (m!)²)) · ∫_ℝ v^{2m} (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Elementary factorial-exponential envelopes and hyperbolic lower bounds -/

/-- **Factorial-exponential upper bound:** for every `y ≥ 0` and `n ∈ ℕ`, `y^n ≤ n! · exp y`. -/
theorem pow_le_factorial_mul_exp_nonneg {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    y ^ n ≤ (n.factorial : ℝ) * Real.exp y := by
  have hn_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hterm : y ^ n / (n.factorial : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), y ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => y ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.self_mem_range_succ n)
  exact (div_le_iff₀' hn_pos).mp (hterm.trans (Real.sum_le_exp_of_nonneg hy (n + 1)))

/-- **Quarter-rate factorial-exponential envelope:** for all `n ∈ ℕ` and `v ∈ ℝ`,
`|v|^n ≤ n! · 4^n · exp((1/4) |v|)`. -/
theorem abs_pow_le_factorial_mul_four_pow_mul_exp_quarter (n : ℕ) (v : ℝ) :
    |v| ^ n ≤ (n.factorial : ℝ) * (4 : ℝ) ^ n * Real.exp ((1 / 4 : ℝ) * |v|) := by
  have h := pow_le_factorial_mul_exp_nonneg (by positivity : 0 ≤ (1 / 4 : ℝ) * |v|) n
  have hmul := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (4 : ℝ) ^ n)
  calc |v| ^ n
      = ((1 / 4 : ℝ) * |v|) ^ n * (4 : ℝ) ^ n := by rw [← mul_pow]; ring
    _ ≤ ((n.factorial : ℝ) * Real.exp ((1 / 4 : ℝ) * |v|)) * (4 : ℝ) ^ n := hmul
    _ = (n.factorial : ℝ) * (4 : ℝ) ^ n * Real.exp ((1 / 4 : ℝ) * |v|) := by ring

/-- **All-orders Taylor lower bound for `exp y − 1`:** for all `y ≥ 0` and `n ≥ 1`,
`y^n / n! ≤ exp y − 1`. -/
theorem pow_div_factorial_le_exp_sub_one {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : 1 ≤ n) :
    y ^ n / (n.factorial : ℝ) ≤ Real.exp y - 1 := by
  have hsum := Real.sum_le_exp_of_nonneg hy (n + 1)
  rw [Finset.sum_range_succ'] at hsum
  have h0 : y ^ 0 / (Nat.factorial 0 : ℝ) = 1 := by norm_num
  rw [h0] at hsum
  have hmem : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hsingle : y ^ ((n - 1) + 1) / (Nat.factorial ((n - 1) + 1) : ℝ) ≤
      ∑ k ∈ Finset.range n, y ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) :=
    Finset.single_le_sum (f := fun k => y ^ (k + 1) / (Nat.factorial (k + 1) : ℝ))
      (fun k _ => by positivity) hmem
  rw [Nat.sub_add_cancel hn] at hsingle
  linarith

/-- Elementary inequality `(exp u − 1) / 2 ≤ sinh u` for all `u ≥ 0`. -/
theorem exp_sub_one_div_two_le_sinh {u : ℝ} (hu : 0 ≤ u) :
    (Real.exp u - 1) / 2 ≤ Real.sinh u := by
  rw [Real.sinh_eq]
  have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- **All-orders monomial lower bound for `sinh u`:** for all `u ≥ 0` and `n ≥ 1`,
`u^n / (2 · n!) ≤ sinh u`. -/
theorem pow_div_two_mul_factorial_le_sinh {u : ℝ} (hu : 0 ≤ u) {n : ℕ} (hn : 1 ≤ n) :
    u ^ n / (2 * (n.factorial : ℝ)) ≤ Real.sinh u := by
  have h1 := pow_div_factorial_le_exp_sub_one hu hn
  have h2 := exp_sub_one_div_two_le_sinh hu
  have h3 : u ^ n / (2 * (n.factorial : ℝ)) = (u ^ n / (n.factorial : ℝ)) / 2 := by ring
  linarith

/-- **All-orders absolute monomial lower bound for `|sinh u|`:** for all `u ∈ ℝ` and `n ≥ 1`,
`|u|^n / (2 · n!) ≤ |sinh u|`. -/
theorem abs_pow_div_two_mul_factorial_le_abs_sinh (u : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |u| ^ n / (2 * (n.factorial : ℝ)) ≤ |Real.sinh u| := by
  rw [Real.abs_sinh]
  exact pow_div_two_mul_factorial_le_sinh (abs_nonneg u) hn

/-- **All-even-orders monomial lower bound for `2 (sinh u)²`:** for all `u ∈ ℝ` and `m ≥ 1`,
`u^{2m} / (2 · (m!)²) ≤ 2 (sinh u)²`. -/
theorem pow_two_mul_div_two_mul_factorial_sq_le_two_mul_sinh_sq (u : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    u ^ (2 * m) / (2 * (m.factorial : ℝ) ^ 2) ≤ 2 * (Real.sinh u) ^ 2 := by
  have h := abs_pow_div_two_mul_factorial_le_abs_sinh u hm
  have hnn : 0 ≤ |u| ^ m / (2 * (m.factorial : ℝ)) := by positivity
  have hsq := mul_le_mul h h hnn (abs_nonneg _)
  have h_lhs : (|u| ^ m / (2 * (m.factorial : ℝ))) * (|u| ^ m / (2 * (m.factorial : ℝ))) =
      u ^ (2 * m) / (4 * (m.factorial : ℝ) ^ 2) := by
    have hpow : |u| ^ m * |u| ^ m = u ^ (2 * m) := by
      rw [← mul_pow, ← sq, sq_abs, ← pow_mul]
    calc (|u| ^ m / (2 * (m.factorial : ℝ))) * (|u| ^ m / (2 * (m.factorial : ℝ)))
        = (|u| ^ m * |u| ^ m) / (4 * (m.factorial : ℝ) ^ 2) := by ring
      _ = u ^ (2 * m) / (4 * (m.factorial : ℝ) ^ 2) := by rw [hpow]
  have h_rhs : |Real.sinh u| * |Real.sinh u| = (Real.sinh u) ^ 2 := by
    rw [← sq, sq_abs]
  rw [h_lhs, h_rhs] at hsq
  calc u ^ (2 * m) / (2 * (m.factorial : ℝ) ^ 2)
      = 2 * (u ^ (2 * m) / (4 * (m.factorial : ℝ) ^ 2)) := by ring
    _ ≤ 2 * (Real.sinh u) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)

/-! ### All-orders integrability, origin–infinity equipartition, factorial upper bounds, and strict positivity -/

/-- **Pointwise factorial-exponential envelope for `|v|^n (Φ_k(v))²` (`k ≥ 2`, `n ∈ ℕ`):**
For all `v ∈ ℝ`,
`|v|^n · (arcLineInfiniteDyadicProfile k ν v)² ≤ 680625 · (ν.real univ)² · n! · 4^n · exp(−(1/4)|v|)`. -/
theorem abs_pow_mul_sq_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (v : ℝ) :
    |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 ≤
      680625 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have hv := abs_pow_le_factorial_mul_four_pow_mul_exp_quarter n v
  have hprof := sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v
  calc |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2
      ≤ ((n.factorial : ℝ) * (4 : ℝ) ^ n * Real.exp ((1 / 4 : ℝ) * |v|)) *
          (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
        mul_le_mul hv hprof (sq_nonneg _) (by positivity)
    _ = 680625 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n *
          (Real.exp ((1 / 4 : ℝ) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
    _ = 680625 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n *
          Real.exp (-((1 / 4 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **All-orders integrability of `v ↦ |v|^n · (arcLineInfiniteDyadicProfile k ν v)²` on `ℝ` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_abs_pow_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    Integrable (fun v : ℝ => |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  set B := 680625 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul B).mono'
    ((continuous_abs.pow n).mul
      ((continuous_arcLineInfiniteDyadicProfile hk ν).pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hnn : 0 ≤ |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
    mul_nonneg (pow_nonneg (abs_nonneg v) n) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact abs_pow_mul_sq_arcLineInfiniteDyadicProfile_le hk hν n v

/-- **All-orders integrability of `v ↦ v^n · (arcLineInfiniteDyadicProfile k ν v)²` on `ℝ` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_pow_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    Integrable (fun v : ℝ => v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  refine (integrable_abs_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n).mono'
    ((continuous_id.pow n).mul
      ((continuous_arcLineInfiniteDyadicProfile hk ν).pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (sq_nonneg (arcLineInfiniteDyadicProfile k ν v))]

/-- **All-orders half-line integrability of `v ↦ v^n · (arcLineInfiniteDyadicProfile k ν v)²` on `(0, ∞)` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) (Ioi (0 : ℝ)) :=
  (integrable_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n).integrableOn

/-- **Multiplicative `(0, ∞)` vs additive `ℝ` bridge for the `n`-th absolute logarithmic energy moment (`k ≥ 1`, `n ∈ ℕ`):**
`∫_{x > 0} |log x|^n (V_k(x))² dx = ∫_ℝ |v|^n (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), |Real.log x| ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v : ℝ, |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.log_exp, ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (|v| ^ n * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2)
      = |v| ^ n * (Real.exp v * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
    _ = |v| ^ n * ((Real.exp (v / 2)) ^ 2 *
          (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by rw [hexp]
    _ = |v| ^ n * (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2 := by ring

/-- **Infinity-sector (`x > 1`) log-scale bridge for the `n`-th logarithmic energy moment (`k ≥ 1`, `n ∈ ℕ`):**
`∫_{x > 1} |log x|^n (V_k(x))² dx = ∫_{v > 0} v^n (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_one_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) :
    (∫ x in Ioi (1 : ℝ), |Real.log x| ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [Real.log_exp, abs_of_pos hv, ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (v ^ n * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2)
      = v ^ n * (Real.exp v * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
    _ = v ^ n * ((Real.exp (v / 2)) ^ 2 *
          (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by rw [hexp]
    _ = v ^ n * (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2 := by ring

/-- **Infinity-sector (`x > 1`) signed log-scale bridge for the `n`-th logarithmic energy moment (`k ≥ 1`, `n ∈ ℕ`):**
`∫_{x > 1} (log x)^n (V_k(x))² dx = ∫_{v > 0} v^n (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_one_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) :
    (∫ x in Ioi (1 : ℝ), (Real.log x) ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [← setIntegral_Ioi_one_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk ν n]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [abs_of_pos (Real.log_pos hx)]

/-- **Origin-sector (`x ∈ (0, 1]`) log-scale bridge for the `n`-th logarithmic energy moment (`k ≥ 1`, `n ∈ ℕ`):**
`∫_{x ∈ (0, 1]} |log x|^n (V_k(x))² dx = ∫_{v > 0} v^n (Φ_k(v))² dv`. -/
theorem setIntegral_Ioc_zero_one_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) :
    (∫ x in Ioc (0 : ℝ) 1, |Real.log x| ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [Real.log_exp, abs_neg, abs_of_pos hv]
  have hprof : Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v)) =
      arcLineInfiniteDyadicProfile k ν v := by
    rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν (-v), arcLineInfiniteDyadicProfile_neg]
  have hexp : Real.exp (-v) = (Real.exp ((-v) / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc Real.exp (-v) * (v ^ n * (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2)
      = v ^ n * (Real.exp (-v) * (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2) := by ring
    _ = v ^ n * ((Real.exp ((-v) / 2)) ^ 2 *
          (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2) := by rw [hexp]
    _ = v ^ n * (Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2 := by
          ring
    _ = v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by rw [hprof]

/-- **All-orders full-line vs half-line logarithmic moment identity (`k ≥ 2`, `n ∈ ℕ`):**
`∫_ℝ |v|^n (arcLineInfiniteDyadicProfile k ν v)² dv = 2 ∫_{v > 0} v^n (arcLineInfiniteDyadicProfile k ν v)² dv`. -/
theorem integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    (∫ v : ℝ, |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      2 * ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hg : IntegrableOn
      (fun x : ℝ => |Real.log x| ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2)
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_iff_integrable_exp_mul]
    refine (integrable_abs_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n).congr
      (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.log_exp, ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc |v| ^ n * (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2
        = |v| ^ n * ((Real.exp (v / 2)) ^ 2 *
            (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
      _ = |v| ^ n * (Real.exp v * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by
          rw [← hexp]
      _ = Real.exp v * (|v| ^ n * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
  have hsum := setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one hg
  rw [setIntegral_Ioc_zero_one_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν n,
    setIntegral_Ioi_one_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν n,
    setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν n] at hsum
  linarith

/-- **Odd-order full-line logarithmic moment cancellation (`k ≥ 2`, `m ∈ ℕ`):**
For every odd power `2m + 1`,
`∫_ℝ v^{2m+1} (arcLineInfiniteDyadicProfile k ν v)² dv = 0`. -/
theorem integral_pow_two_mul_add_one_mul_sq_arcLineInfiniteDyadicProfile_eq_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (m : ℕ) :
    (∫ v : ℝ, v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hg : IntegrableOn
      (fun x : ℝ => (Real.log x) ^ (2 * m + 1) * (arcLineInfiniteDyadicVector k ν x) ^ 2)
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_iff_integrable_exp_mul]
    refine (integrable_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m + 1)).congr
      (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.log_exp, ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc v ^ (2 * m + 1) * (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2
        = v ^ (2 * m + 1) * ((Real.exp (v / 2)) ^ 2 *
            (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
      _ = v ^ (2 * m + 1) * (Real.exp v *
            (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by rw [← hexp]
      _ = Real.exp v * (v ^ (2 * m + 1) *
            (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
  have hfull : (∫ x in Ioi (0 : ℝ),
        (Real.log x) ^ (2 * m + 1) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v : ℝ, v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
    rw [setIntegral_Ioi_eq_integral_exp_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.log_exp, ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc Real.exp v * (v ^ (2 * m + 1) * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2)
        = v ^ (2 * m + 1) * (Real.exp v *
            (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
      _ = v ^ (2 * m + 1) * ((Real.exp (v / 2)) ^ 2 *
            (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by rw [hexp]
      _ = v ^ (2 * m + 1) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2 := by ring
  have horig : (∫ x in Ioc (0 : ℝ) 1,
        (Real.log x) ^ (2 * m + 1) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      -(∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [Real.log_exp, Odd.neg_pow ⟨m, rfl⟩]
    have hprof : Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v)) =
        arcLineInfiniteDyadicProfile k ν v := by
      rw [exp_half_mul_arcLineInfiniteDyadicVector hk1 ν (-v), arcLineInfiniteDyadicProfile_neg]
    have hexp : Real.exp (-v) = (Real.exp ((-v) / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-v) * (-(v ^ (2 * m + 1)) *
            (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2)
        = -(v ^ (2 * m + 1) * (Real.exp (-v) *
            (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2)) := by ring
      _ = -(v ^ (2 * m + 1) * ((Real.exp ((-v) / 2)) ^ 2 *
            (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2)) := by rw [hexp]
      _ = -(v ^ (2 * m + 1) *
            (Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2) := by
            ring
      _ = -(v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by rw [hprof]
  have hsum := setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one hg
  rw [horig, setIntegral_Ioi_one_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν (2 * m + 1),
    hfull] at hsum
  linarith

/-- **Scale-independent factorial upper bound on the full-line `n`-th logarithmic energy moment (`k ≥ 2`, `n ∈ ℕ`):**
`∫_ℝ |v|^n (Φ_k(v))² dv ≤ 5445000 · (ν.real univ)² · n! · 4^n`. -/
theorem integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_le_factorial
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    (∫ v : ℝ, |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      5445000 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n := by
  set B := 680625 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul B
  calc (∫ v : ℝ, |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      ≤ ∫ v : ℝ, B * Real.exp (-((1 / 4 : ℝ) * |v|)) :=
        integral_mono (integrable_abs_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n) hdom
          (fun v => abs_pow_mul_sq_arcLineInfiniteDyadicProfile_le hk hν n v)
    _ = B * ∫ v : ℝ, Real.exp (-((1 / 4 : ℝ) * |v|)) := integral_const_mul _ _
    _ = 5445000 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n := by
        rw [integral_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)]
        dsimp [B]; ring

/-- **Scale-independent factorial upper bound on the half-line `n`-th logarithmic energy moment (`k ≥ 2`, `n ∈ ℕ`):**
`∫_{v > 0} v^n (Φ_k(v))² dv ≤ 2722500 · (ν.real univ)² · n! · 4^n`. -/
theorem setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_le_factorial
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      2722500 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n := by
  have h := integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_le_factorial hk hν n
  rw [integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hν n] at h
  linarith

/-- **Strict positivity of the half-line `n`-th logarithmic energy moment (`k ≥ 2`, `n ∈ ℕ`):**
`0 < ∫_{v > 0} v^n (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (n : ℕ) :
    0 < ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  refine setIntegral_Ioi_pos_of_pos_mul
    (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn
    (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n)
    (fun _ _ => sq_nonneg _)
    (fun v hv => pow_pos hv n)
    (setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos)

/-- **Strict positivity of the full-line `n`-th logarithmic energy moment (`k ≥ 2`, `n ∈ ℕ`):**
`0 < ∫_ℝ |v|^n (Φ_k(v))² dv`. -/
theorem integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (n : ℕ) :
    0 < ∫ v : ℝ, |v| ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hν n]
  exact mul_pos (by norm_num)
    (setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos n)

/-- **Strict positivity of the multiplicative `(0, ∞)` `n`-th logarithmic energy moment (`k ≥ 2`, `n ∈ ℕ`):**
`0 < ∫_{x > 0} |log x|^n (V_k(x))² dx`. -/
theorem setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (n : ℕ) :
    0 < ∫ x in Ioi (0 : ℝ), |Real.log x| ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν n]
  exact integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos n

/-! ### Universal Turán–Hankel log-convexity across all orders `n ∈ ℕ` -/

/-- **Universal Turán–Hankel log-convexity of the half-line logarithmic energy moments (`k ≥ 2`, `n ∈ ℕ`):**
For every integer `n ∈ ℕ`,
`(∫_{v > 0} v^{n+1} (Φ_k(v))² dv)² ≤ (∫_{v > 0} v^n (Φ_k(v))² dv) · (∫_{v > 0} v^{n+2} (Φ_k(v))² dv)`. -/
theorem sq_setIntegral_Ioi_zero_pow_succ_mul_sq_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    (∫ v in Ioi (0 : ℝ), v ^ (n + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ^ 2 ≤
      (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) *
        (∫ v in Ioi (0 : ℝ), v ^ (n + 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  set M0 := ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2
  set M1 := ∫ v in Ioi (0 : ℝ), v ^ (n + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2
  set M2 := ∫ v in Ioi (0 : ℝ), v ^ (n + 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2
  have hI0 := integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n
  have hI1 := integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (n + 1)
  have hI2 := integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (n + 2)
  have hexpand : ∀ t : ℝ,
      (∫ v in Ioi (0 : ℝ),
        (t * v - M1) ^ 2 * (v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) =
        t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    have hfun : (fun v : ℝ =>
        (t * v - M1) ^ 2 * (v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) =
        fun v : ℝ =>
          (t ^ 2 * (v ^ (n + 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
            (2 * t * M1) * (v ^ (n + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) +
            M1 ^ 2 * (v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      funext v; ring
    have hsub : IntegrableOn
        (fun v : ℝ => t ^ 2 * (v ^ (n + 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
          (2 * t * M1) * (v ^ (n + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
        (Ioi (0 : ℝ)) volume :=
      (hI2.const_mul (t ^ 2)).sub (hI1.const_mul (2 * t * M1))
    rw [hfun, integral_add hsub (hI0.const_mul (M1 ^ 2)),
      integral_sub (hI2.const_mul (t ^ 2)) (hI1.const_mul (2 * t * M1)),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have h_any_t : ∀ t : ℝ, 0 ≤ t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    rw [← hexpand t]
    exact setIntegral_nonneg measurableSet_Ioi fun v hv =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hv) n) (sq_nonneg _))
  have hM0_nn : 0 ≤ M0 :=
    setIntegral_nonneg measurableSet_Ioi fun v hv =>
      mul_nonneg (pow_nonneg (le_of_lt hv) n) (sq_nonneg _)
  rcases eq_or_lt_of_le hM0_nn with hM0_zero | hM0_pos
  · have hM1_zero : M1 = 0 := by
      by_contra hne
      have ht := h_any_t (M1 ^ 2 / (M2 + 1))
      rw [← hM0_zero, mul_zero, add_zero] at ht
      have hM2_nn : 0 ≤ M2 :=
        setIntegral_nonneg measurableSet_Ioi fun v hv =>
          mul_nonneg (pow_nonneg (le_of_lt hv) (n + 2)) (sq_nonneg _)
      have hden_pos : 0 < M2 + 1 := by linarith
      have hprod := mul_le_mul_of_nonneg_left ht (sq_nonneg (M2 + 1))
      have hident : (M2 + 1) ^ 2 *
          ((M1 ^ 2 / (M2 + 1)) ^ 2 * M2 - 2 * (M1 ^ 2 / (M2 + 1)) * M1 * M1) =
          -(M1 ^ 4 * (M2 + 2)) := by
        have hne_den : M2 + 1 ≠ 0 := ne_of_gt hden_pos
        field_simp; ring
      rw [hident] at hprod
      have : 0 < M1 ^ 4 * (M2 + 2) := by positivity
      linarith
    rw [hM1_zero, ← hM0_zero]
    simp
  · have hnn := h_any_t M0
    have hfactor : M0 ^ 2 * M2 - 2 * M0 * M1 * M1 + M1 ^ 2 * M0 =
        M0 * (M0 * M2 - M1 ^ 2) := by ring
    rw [hfactor] at hnn
    have hsub : 0 ≤ M0 * M2 - M1 ^ 2 := nonneg_of_mul_nonneg_right hnn hM0_pos
    linarith

/-- **Universal Turán–Hankel log-convexity of the multiplicative `(0, ∞)` logarithmic energy moments (`k ≥ 2`, `n ∈ ℕ`):**
For every integer `n ∈ ℕ`,
`(∫_{x > 0} |log x|^{n+1} (V_k(x))² dx)² ≤ (∫_{x > 0} |log x|^n (V_k(x))² dx) · (∫_{x > 0} |log x|^{n+2} (V_k(x))² dx)`. -/
theorem sq_setIntegral_Ioi_abs_log_pow_succ_mul_sq_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), |Real.log x| ^ (n + 1) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ^ 2 ≤
      (∫ x in Ioi (0 : ℝ), |Real.log x| ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2) *
        (∫ x in Ioi (0 : ℝ), |Real.log x| ^ (n + 2) * (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν n,
    setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν (n + 1),
    setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν (n + 2),
    integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hν n,
    integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hν (n + 1),
    integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hν (n + 2)]
  have h := sq_setIntegral_Ioi_zero_pow_succ_mul_sq_le hk hν n
  nlinarith

/-! ### All-orders polynomial coercivity lower bounds across the open critical strip `|l| < 1/2` -/

/-- **All-orders polynomial lower bound on the infinity-sector energy growth (`0 ≤ l < 1/2`, `n ≥ 1`):**
For every `k ≥ 2`, `n ≥ 1`, and `l ∈ [0, 1/2)`,
`((2l)^n / n!) · ∫_{v > 0} v^n (Φ_k(v))² dv ≤ E_k^{(1, ∞)}(l) − E_k^{(1, ∞)}(0)`. -/
theorem pow_mul_div_factorial_le_sub_Ioi_one
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {n : ℕ} (hn : 1 ≤ n)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ((2 * l) ^ n / (n.factorial : ℝ)) *
        (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have hl_abs : |l| < 1 / 2 := by rw [abs_of_nonneg hl0]; exact hl
  have h1 := setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l
  have h0 := setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν 0
  simp only [mul_zero, Real.rpow_zero, one_mul, zero_mul, Real.exp_zero] at h0
  rw [h1, h0, ← integral_sub
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_abs).integrableOn
    (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn]
  rw [← integral_const_mul]
  refine setIntegral_mono_on
    ((integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n).const_mul _)
    ((integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_abs).integrableOn.sub
      (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn)
    measurableSet_Ioi fun v hv => ?_
  have hv_pos : 0 < v := hv
  have h2lv : 0 ≤ 2 * l * v := by positivity
  have htaylor := pow_div_factorial_le_exp_sub_one h2lv hn
  calc ((2 * l) ^ n / (n.factorial : ℝ)) * (v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      = ((2 * l * v) ^ n / (n.factorial : ℝ)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
          rw [mul_pow]; ring
    _ ≤ (Real.exp (2 * l * v) - 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
        mul_le_mul_of_nonneg_right htaylor (sq_nonneg _)
    _ = Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
          (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by ring

/-- **All-orders polynomial coercivity lower bound on the origin–infinity energy imbalance (`|l| < 1/2`, `n ≥ 1`):**
For every `k ≥ 2`, `n ≥ 1`, and `|l| < 1/2`,
`((2|l|)^n / n!) · ∫_{v > 0} v^n (Φ_k(v))² dv ≤ |E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)|`. -/
theorem abs_pow_mul_div_factorial_le_abs_imbalance
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {n : ℕ} (hn : 1 ≤ n) {l : ℝ} (hl : |l| < 1 / 2) :
    ((2 * |l|) ^ n / (n.factorial : ℝ)) *
        (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)| := by
  have hk1 : 1 ≤ k := by omega
  rw [abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hν hl]
  have h_inf := pow_mul_div_factorial_le_sub_Ioi_one hk hν hn (abs_nonneg l) hl
  have h_orig : (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * |l|) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
      (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
    rw [setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν |l|, ← sub_nonneg]
    have h0 : (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) =
        ∫ x in Ioi (1 : ℝ), x ^ (2 * (0 : ℝ)) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
      simp
    rw [h0, setIntegral_Ioi_one_rpow_two_mul_sq_sub_eq hk hν (by simpa using hl) (by norm_num)]
    refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
    have hv_pos : 0 < v := hv
    have hexp : Real.exp (2 * -|l| * v) ≤ Real.exp (2 * 0 * v) := by
      rw [Real.exp_le_exp]
      nlinarith [abs_nonneg l]
    exact mul_nonneg (sub_nonneg.mpr hexp) (sq_nonneg _)
  linarith

/-- **All-even-orders polynomial coercivity lower bound on the critical-line excess energy (`|l| < 1/2`, `m ≥ 1`):**
For every `k ≥ 2`, `m ≥ 1`, and `|l| < 1/2`,
`(l^{2m} / (2 · (m!)²)) · ∫_ℝ v^{2m} (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`. -/
theorem pow_two_mul_div_two_mul_factorial_sq_le_excess
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {m : ℕ} (hm : 1 ≤ m) {l : ℝ} (hl : |l| < 1 / 2) :
    (l ^ (2 * m) / (2 * (m.factorial : ℝ) ^ 2)) *
        (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_eq hk hν hl,
    ← integral_const_mul]
  have hInt : Integrable (fun v : ℝ =>
      2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    have heq : (fun v : ℝ =>
        2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ =>
          (1 / 2 : ℝ) * (Real.exp (l * v) - Real.exp ((-l) * v)) ^ 2 *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; rw [two_mul_sq_sinh_eq_half_sq_exp_sub]
    rw [heq]
    exact integrable_half_sq_exp_sub_exp_mul_sq_arcLineInfiniteDyadicProfile
      hk hν hl (by simpa using hl)
  refine integral_mono
    ((integrable_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m)).const_mul _)
    hInt fun v => ?_
  have hsinh := pow_two_mul_div_two_mul_factorial_sq_le_two_mul_sinh_sq (l * v) hm
  calc (l ^ (2 * m) / (2 * (m.factorial : ℝ) ^ 2)) *
          (v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      = ((l * v) ^ (2 * m) / (2 * (m.factorial : ℝ) ^ 2)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by rw [mul_pow]; ring
    _ ≤ (2 * (Real.sinh (l * v)) ^ 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
        mul_le_mul_of_nonneg_right hsinh (sq_nonneg _)
    _ = 2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by ring

/-- **Master theorem for the all-orders logarithmic energy moment hierarchy, Turán–Hankel
log-convexity, and all-orders polynomial coercivity:**
There exists a concrete non-zero finite Borel measure `ν` on `ArcParam` such that for every integer
`k ≥ 2`, `V_k = arcLineInfiniteDyadicVector k ν` and `Φ_k = arcLineInfiniteDyadicProfile k ν`
satisfy for every `n ∈ ℕ`:
1. **Strict positivity, origin–infinity equipartition, and scale-independent factorial upper bound:**
   `0 < ∫_{v > 0} v^n (Φ_k(v))² dv ≤ 2722500 · (ν.real univ)² · n! · 4^n` and
   `∫_{x > 0} |log x|^n (V_k(x))² dx = ∫_ℝ |v|^n (Φ_k(v))² dv = 2 ∫_{v > 0} v^n (Φ_k(v))² dv`.
2. **Odd-order full-line cancellation:**
   `∫_ℝ v^{2n+1} (Φ_k(v))² dv = 0`.
3. **Universal Turán–Hankel log-convexity:**
   `(∫_{v > 0} v^{n+1} (Φ_k(v))² dv)² ≤ (∫_{v > 0} v^n (Φ_k(v))² dv) · (∫_{v > 0} v^{n+2} (Φ_k(v))² dv)`.
4. **All-orders polynomial coercivity across `|l| < 1/2` (`1 ≤ n`):**
   `((2|l|)^n / n!) · ∫_{v > 0} v^n (Φ_k(v))² dv ≤ |E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)|` and
   `(l^{2n} / (2 · (n!)²)) · ∫_ℝ v^{2n} (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`. -/
theorem exists_dyadic_logarithmicMoment_hierarchy_arcWitness :
    ∃ (ν : Measure ArcParam) (_ : IsFiniteMeasure ν),
      ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ m : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m * t) = 0) ∧
      (∀ ⦃k : ℕ⦄, 2 ≤ k → ∀ n : ℕ,
        0 < (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
          2722500 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * (4 : ℝ) ^ n ∧
        (∫ x in Ioi (0 : ℝ), |Real.log x| ^ n * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
          2 * (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        (∫ v : ℝ, v ^ (2 * n + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) = 0 ∧
        (∫ v in Ioi (0 : ℝ), v ^ (n + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ^ 2 ≤
          (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) *
            (∫ v in Ioi (0 : ℝ), v ^ (n + 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        (1 ≤ n → ∀ ⦃l : ℝ⦄, |l| < 1 / 2 →
          ((2 * |l|) ^ n / (n.factorial : ℝ)) *
              (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)| ∧
          (l ^ (2 * n) / (2 * (n.factorial : ℝ) ^ 2)) *
              (∫ v : ℝ, v ^ (2 * n) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2))) := by
  obtain ⟨ν, hfin, hne, hsymm, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ m : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m * t) = 0 := fun m => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker m).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsymm, hblind, fun k hk n => ?_⟩
  have hk1 : 1 ≤ k := by omega
  refine ⟨setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_pos hk hsymm hpd n,
    setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_le_factorial hk hsymm n,
    by rw [setIntegral_Ioi_abs_log_pow_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν n,
        integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hsymm n],
    integral_pow_two_mul_add_one_mul_sq_arcLineInfiniteDyadicProfile_eq_zero hk hsymm n,
    sq_setIntegral_Ioi_zero_pow_succ_mul_sq_le hk hsymm n,
    fun hn l hl =>
      ⟨abs_pow_mul_div_factorial_le_abs_imbalance hk hsymm hn hl,
       pow_two_mul_div_two_mul_factorial_sq_le_excess hk hsymm hn hl⟩⟩

end

end RHTower
