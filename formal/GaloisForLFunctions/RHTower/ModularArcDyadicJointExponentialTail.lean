import GaloisForLFunctions.RHTower.ModularArcDyadicStripOscillatoryMellin

/-!
# Joint exponential-doubly-exponential tail laws for the dyadic modular arc tower

In `ModularArcDyadicTailApproximation`, we proved the `L^∞(ℝ)` tail bound
`|arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k r₀ ν v| ≤ 288 · ν.real univ · (k^{2^{r₀}})⁻¹`
(with no spatial decay in `v`), and in `ModularArcDyadicInfiniteProfileIntegral` we proved the
depth-and-scale-uniform spatial decay bound
`|arcLineDyadicTowerProfile k r ν v| ≤ 825 · ν.real univ · exp(−|v|/4)` (with no tail decay in `r`).

In this module we feed the `2^r`-free uniform bound `abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform`
back into the symmetric dilation operator `symScaleProfile (k^{2^r})` to prove **joint
exponential-doubly-exponential tail bounds** that simultaneously carry both `exp(−|v|/4)` spatial
decay and `(k^{2^{r₀}})⁻¹` doubly-exponential depth decay:

1. **Depth-uniform `symScaleProfile` bound free of the `2^r` factor
   (`abs_arcLineSymDyadicTowerProfile_le_exp_quarter_uniform`,
   `cosh_quarter_div_cosh_log_pow_two_pow_succ_add_le`,
   `abs_arcLineDyadicTowerProfile_succ_sub_le_exp_quarter_pow`):**
   For every `k ≥ 2`, `r ∈ ℕ`, and `v ∈ ℝ`,
   `|arcLineSymDyadicTowerProfile k r ν v| ≤ (825 · ν.real univ) · cosh((1/4) · 2 log(k^{2^r})) · exp(−|v|/4)`.
   At shifted depth `r = (r₀ + 1) + s`, the dyadic squaring identity `(1/2) log(k^{2^{(r₀+s)+1}}) = log(k^{2^{r₀+s}})`
   gives `cosh((1/4) · 2 log(k^{2^{r₀+1+s}})) / cosh(log(k^{2^{r₀+1+s}})) ≤ 2 · (k^{2^{r₀}})⁻¹ · (1/2)^s`.
2. **Joint exponential-doubly-exponential profile tail bound
   (`abs_arcLineDyadicTowerProfile_add_sub_succ_le_exp_quarter`,
   `abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter`):**
   For every `k ≥ 2`, `r₀ ∈ ℕ`, and `v ∈ ℝ`,
   `|arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k (r₀ + 1) ν v| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · exp(−|v|/4)`.
3. **Joint two-sided power-law and doubly-exponential tail bounds on `ℝ \ {0}`
   (`abs_arcLineInfiniteDyadicVector_sub_succ_le_rpow_quarter_uniform`,
   `abs_arcLineInfiniteDyadicVector_sub_succ_le_rpow_quarter_near_zero`):**
   For `|x| ≥ 1`, `|arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · |x|^{−3/4}`,
   and for `0 < |x| ≤ 1`, `|arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · |x|^{−1/4}`.
4. **Height-uniform doubly-exponential `O((k^{2^{r₀}})⁻¹ / (1/4 − |l|))` two-variable oscillatory
   Mellin tail approximation across `(|l| < 1/4, τ ∈ ℝ)`
   (`abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_succ_le`,
   `exists_dyadic_jointExponentialTail_arcWitness`):**
   For all `|l| < 1/4` and `τ ∈ ℝ`,
   `|∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_{k, r₀ + 1}(x) dx| ≤ (6600 · ν.real univ / (1/4 − |l|)) · (k^{2^{r₀}})⁻¹`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Depth-uniform `symScaleProfile` bound free of the `2^r` factor -/

/-- **Depth-and-scale-uniform `symScaleProfile` exponential bound (`k ≥ 2`):**
Because `|arcLineDyadicTowerProfile k r ν v| ≤ 825 · ν.real univ · exp(−|v|/4)` holds without a
`2^r` factor, `arcLineSymDyadicTowerProfile k r ν` satisfies
`|arcLineSymDyadicTowerProfile k r ν v| ≤ (825 · ν.real univ) · cosh((1/4) · 2 log(k^{2^r})) · exp(−|v|/4)`
for all `r ∈ ℕ` and `v ∈ ℝ`. -/
theorem abs_arcLineSymDyadicTowerProfile_le_exp_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineSymDyadicTowerProfile k r ν v| ≤
      (825 * ν.real univ) *
        Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) *
          Real.exp (-((1 / 4 : ℝ) * |v|)) :=
  abs_symScaleProfile_le_exp_mul (k ^ (2 ^ r)) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk r hν) v

/-- **Shifted dyadic squaring `cosh` ratio bound (`k ≥ 2`):**
For every `r₀, s ∈ ℕ`, at shifted depth `r₀ + 1 + s = (r₀ + s) + 1`,
`cosh((1/4) · 2 log(k^{2^{r₀ + 1 + s}})) / cosh(log(k^{2^{r₀ + 1 + s}})) ≤ 2 · (k^{2^{r₀}})⁻¹ · (1/2)^s`. -/
theorem cosh_quarter_div_cosh_log_pow_two_pow_succ_add_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ s : ℕ) :
    Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ))) ≤
      2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s := by
  have hk1 : 1 ≤ k := by omega
  have hidx : r₀ + 1 + s = (r₀ + s) + 1 := by omega
  rw [hidx]
  have hm_succ : (1 : ℝ) ≤ (k ^ (2 ^ ((r₀ + s) + 1)) : ℕ) := by
    exact_mod_cast one_le_pow_two_pow hk1 ((r₀ + s) + 1)
  have hb0 : 0 ≤ Real.log ((k ^ (2 ^ ((r₀ + s) + 1)) : ℕ)) := Real.log_nonneg hm_succ
  have hstep1 := cosh_two_mul_div_cosh_le_two_mul_exp_neg hb0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hsq : ((k ^ (2 ^ ((r₀ + s) + 1)) : ℕ) : ℝ) = ((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast (pow_two_pow_sq k (r₀ + s)).symm
  have hms_pos : (0 : ℝ) < (k ^ (2 ^ (r₀ + s)) : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (one_le_pow_two_pow hk1 (r₀ + s)))
  have hexp_eq : Real.exp (-((1 - 2 * (1 / 4 : ℝ)) *
      Real.log ((k ^ (2 ^ ((r₀ + s) + 1)) : ℕ)))) =
      (((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ))⁻¹ := by
    rw [hsq, Real.log_pow, Nat.cast_ofNat,
      show -((1 - 2 * (1 / 4 : ℝ)) * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) =
        -Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)) by ring,
      Real.exp_neg, Real.exp_log hms_pos]
  rw [hexp_eq] at hstep1
  have hm0 : 1 ≤ k ^ (2 ^ r₀) := one_le_pow_two_pow hk1 r₀
  have hpos0 : (0 : ℝ) < (k ^ (2 ^ r₀) : ℕ) := by exact_mod_cast hm0
  have hpow : ((k ^ (2 ^ r₀) : ℕ) : ℝ) * (2 : ℝ) ^ s ≤ ((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ) := by
    exact_mod_cast pow_two_pow_mul_two_pow_le hk r₀ s
  have hinv : (((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ))⁻¹ ≤
      (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s := by
    have hmul_pos : (0 : ℝ) < ((k ^ (2 ^ r₀) : ℕ) : ℝ) * (2 : ℝ) ^ s := by positivity
    have h1 := inv_anti₀ hmul_pos hpow
    rw [mul_inv, ← inv_pow] at h1
    simpa only [one_div] using h1
  calc Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ ((r₀ + s) + 1)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ ((r₀ + s) + 1)) : ℕ)))
      ≤ 2 * (((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ))⁻¹ := hstep1
    _ ≤ 2 * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s := by ring

/-- **Joint exponential-doubly-exponential step bound at shifted depth `r₀ + 1 + s` (`k ≥ 2`):**
`|(1 / cosh(log(k^{2^{r₀ + 1 + s}}))) · arcLineSymDyadicTowerProfile k (r₀ + 1 + s) ν v| ≤ (1650 · ν.real univ · (k^{2^{r₀}})⁻¹ · exp(−|v|/4)) · (1/2)^s`. -/
theorem abs_inv_cosh_mul_arcLineSymDyadicTowerProfile_succ_add_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ s : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |(1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ)))) *
        arcLineSymDyadicTowerProfile k (r₀ + 1 + s) ν v| ≤
      (1650 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
        Real.exp (-((1 / 4 : ℝ) * |v|))) * (1 / 2 : ℝ) ^ s := by
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hS := abs_arcLineSymDyadicTowerProfile_le_exp_quarter_uniform hk (r₀ + 1 + s) hν v
  have hratio := cosh_quarter_div_cosh_log_pow_two_pow_succ_add_le hk r₀ s
  rw [abs_mul, abs_of_pos (by positivity)]
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ))) *
        |arcLineSymDyadicTowerProfile k (r₀ + 1 + s) ν v|
      ≤ 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ))) *
          ((825 * ν.real univ) *
            Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ)))) *
              Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ)))) *
          ((825 * ν.real univ) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ ≤ (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s) *
          ((825 * ν.real univ) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = (1650 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
          Real.exp (-((1 / 4 : ℝ) * |v|))) * (1 / 2 : ℝ) ^ s := by ring

/-! ### Joint exponential-doubly-exponential profile tail bounds -/

/-- **Finite-horizon joint exponential-doubly-exponential tail bound (`k ≥ 2`):**
For every `r₀, S ∈ ℕ` and `v ∈ ℝ`,
`|arcLineDyadicTowerProfile k (r₀ + 1 + S) ν v − arcLineDyadicTowerProfile k (r₀ + 1) ν v| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · exp(−|v|/4)`. -/
theorem abs_arcLineDyadicTowerProfile_add_sub_succ_le_exp_quarter
    {k : ℕ} (hk : 2 ≤ k) (r₀ S : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineDyadicTowerProfile k (r₀ + 1 + S) ν v -
        arcLineDyadicTowerProfile k (r₀ + 1) ν v| ≤
      3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  rw [arcLineDyadicTowerProfile_add_sub k (r₀ + 1) S ν v, abs_neg]
  set A := 1650 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
    Real.exp (-((1 / 4 : ℝ) * |v|))
  have hA0 : 0 ≤ A := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    dsimp [A]; positivity
  have hsum : |∑ s ∈ Finset.range S,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ)))) *
        arcLineSymDyadicTowerProfile k (r₀ + 1 + s) ν v| ≤
      A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    exact abs_inv_cosh_mul_arcLineSymDyadicTowerProfile_succ_add_le hk r₀ s hν v
  calc |∑ s ∈ Finset.range S,
        (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + 1 + s)) : ℕ)))) *
          arcLineSymDyadicTowerProfile k (r₀ + 1 + s) ν v|
      ≤ A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := hsum
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two S) hA0
    _ = 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
          Real.exp (-((1 / 4 : ℝ) * |v|)) := by dsimp [A]; ring

/-- **Infinite-horizon joint exponential-doubly-exponential profile tail bound (`k ≥ 2`):**
For every `r₀ ∈ ℕ` and `v ∈ ℝ`,
`|arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k (r₀ + 1) ν v| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · exp(−|v|/4)`. -/
theorem abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v| ≤
      3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have ht : Tendsto (fun S : ℕ =>
      |arcLineDyadicTowerProfile k (S + (r₀ + 1)) ν v -
        arcLineDyadicTowerProfile k (r₀ + 1) ν v|)
      atTop (𝓝 |arcLineInfiniteDyadicProfile k ν v -
        arcLineDyadicTowerProfile k (r₀ + 1) ν v|) :=
    continuous_abs.tendsto _ |>.comp
      (((tendsto_arcLineDyadicTowerProfile_atTop hk ν v).comp
        (tendsto_add_atTop_nat (r₀ + 1))).sub_const _)
  exact le_of_tendsto ht
    (Eventually.of_forall fun S => by
      simpa [Nat.add_comm S (r₀ + 1)] using
        abs_arcLineDyadicTowerProfile_add_sub_succ_le_exp_quarter hk r₀ S hν v)

/-! ### Joint two-sided power-law and doubly-exponential tail bounds on `ℝ \ {0}` -/

/-- **Joint `O(|x|^{−3/4} · (k^{2^{r₀}})⁻¹)` tail bound on `|x| ≥ 1` (`k ≥ 2`):**
For every `r₀ ∈ ℕ` and `1 ≤ |x|`,
`|arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · |x|^{−3/4}`. -/
theorem abs_arcLineInfiniteDyadicVector_sub_succ_le_rpow_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {x : ℝ} (hx : 1 ≤ |x|) :
    |arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤
      3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * |x| ^ (-(3 / 4 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hxne : x ≠ 0 := abs_pos.mp habs_pos
  have hlog0 : 0 ≤ Real.log |x| := Real.log_nonneg hx
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hxne,
    arcLineDyadicTowerVector_eq_exp_neg_half_mul_profile hk1 (r₀ + 1) hν hxne,
    ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk r₀ hν (Real.log |x|)
  rw [abs_of_nonneg hlog0] at hprof
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|) -
          arcLineDyadicTowerProfile k (r₀ + 1) ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          (3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
            Real.exp (-((1 / 4 : ℝ) * Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
          (Real.exp (-(Real.log |x| / 2)) * Real.exp (-((1 / 4 : ℝ) * Real.log |x|))) := by ring
    _ = 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
          Real.exp (Real.log |x| * (-(3 / 4 : ℝ))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * |x| ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-- **Joint `O(|x|^{−1/4} · (k^{2^{r₀}})⁻¹)` tail bound near the origin (`0 < |x| ≤ 1`, `k ≥ 2`):**
For every `r₀ ∈ ℕ` and `0 < |x| ≤ 1`,
`|arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · |x|^{−1/4}`. -/
theorem abs_arcLineInfiniteDyadicVector_sub_succ_le_rpow_quarter_near_zero
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤
      3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * |x| ^ (-(1 / 4 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := abs_pos.mpr hx0
  have hlog_nonpos : Real.log |x| ≤ 0 := Real.log_nonpos habs_pos.le hx1
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hx0,
    arcLineDyadicTowerVector_eq_exp_neg_half_mul_profile hk1 (r₀ + 1) hν hx0,
    ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk r₀ hν (Real.log |x|)
  rw [abs_of_nonpos hlog_nonpos] at hprof
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|) -
          arcLineDyadicTowerProfile k (r₀ + 1) ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          (3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
            Real.exp (-((1 / 4 : ℝ) * -Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
          (Real.exp (-(Real.log |x| / 2)) * Real.exp (-((1 / 4 : ℝ) * -Real.log |x|))) := by ring
    _ = 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
          Real.exp (Real.log |x| * (-(1 / 4 : ℝ))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * |x| ^ (-(1 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-! ### Height-uniform doubly-exponential two-variable oscillatory Mellin tail bound -/

/-- **Height-uniform doubly-exponential `O((k^{2^{r₀}})⁻¹ / (1/4 − |l|))` tail approximation for
the two-variable oscillatory Mellin transform across `(|l| < 1/4, τ ∈ ℝ)` (`k ≥ 2`):**
For every `r₀ ∈ ℕ`, `|l| < 1/4`, and `τ ∈ ℝ`,
`|∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_{k, r₀ + 1}(x) dx| ≤ (6600 · ν.real univ / (1/4 − |l|)) · (k^{2^{r₀}})⁻¹`. -/
theorem abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_succ_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 4) (τ : ℝ) :
    |(∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
          arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
          arcLineDyadicTowerVector k (r₀ + 1) ν x)| ≤
      (6600 * ν.real univ / (1 / 4 - |l|)) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith
  have hcl : 0 < 1 / 4 - |l| := sub_pos.mpr hl
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_eq_profile hk1 (r₀ + 1) ν l τ,
    ← integral_sub
      (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ)
      (integrable_exp_mul_cos_mul_arcLineDyadicTowerProfile hk (r₀ + 1) hν hl_half τ)]
  set B := 3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)
  have h1 := abs_integral_le_integral_abs
    (μ := volume)
    (f := fun v : ℝ =>
      Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.exp (l * v) * Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v)
  have h2 := integral_mono
    (((integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ).sub
      (integrable_exp_mul_cos_mul_arcLineDyadicTowerProfile hk (r₀ + 1) hν hl_half τ)).abs)
    ((integrable_rexp_neg_mul_abs hcl).const_mul B)
    (fun v => ?_)
  · dsimp only [Pi.sub_apply] at h2
    rw [integral_const_mul, integral_rexp_neg_mul_abs hcl] at h2
    calc |∫ v : ℝ,
            Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.exp (l * v) * Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v|
        ≤ ∫ v : ℝ,
            |Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.exp (l * v) * Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v| := h1
      _ ≤ B * (2 / (1 / 4 - |l|)) := h2
      _ = (6600 * ν.real univ / (1 / 4 - |l|)) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
          dsimp [B]; ring
  · dsimp only [Pi.sub_apply]
    rw [← mul_sub, abs_mul, abs_mul]
    have hcos : |Real.exp (l * v)| * |Real.cos (τ * v)| ≤ Real.exp (|l| * |v|) := by
      calc |Real.exp (l * v)| * |Real.cos (τ * v)|
          ≤ Real.exp (|l| * |v|) * 1 :=
            mul_le_mul (abs_exp_mul_le_exp_abs_mul l v) (Real.abs_cos_le_one _)
              (abs_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (|l| * |v|) := mul_one _
    calc |Real.exp (l * v)| * |Real.cos (τ * v)| *
          |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v|
        ≤ Real.exp (|l| * |v|) * (B * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul hcos
            (abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk r₀ hν v)
            (abs_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (-((1 / 4 - |l|) * |v|)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-! ### Master unconditional theorem for the joint exponential-doubly-exponential tail laws -/

/-- **Master unconditional theorem for the joint exponential-doubly-exponential tail laws of the
dyadic modular arc tower.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2` and every base depth `r₀ ∈ ℕ`:
1. Joint profile tail bound (`v ∈ ℝ`):
   `|arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k (r₀ + 1) ν v| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · exp(−|v|/4)`;
2. Joint near-infinity vector tail bound (`|x| ≥ 1`):
   `|arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · |x|^{−3/4}`;
3. Joint near-origin vector tail bound (`0 < |x| ≤ 1`):
   `|arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · |x|^{−1/4}`;
4. Height-uniform two-variable oscillatory Mellin tail bound (`|l| < 1/4`, `τ ∈ ℝ`):
   `|∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_{k, r₀ + 1}(x) dx| ≤ (6600 · ν.real univ / (1/4 − |l|)) · (k^{2^{r₀}})⁻¹`;
5. Full critical-strip (`|l| < 1/2`) strict interior positivity, two-sided infinite-order edge
   vanishing (`l → (1/2)⁻` and `l → (−1/2)⁺`), and `k → ∞` convergence across the strip, critical
   line, `L²((0, ∞))` Hilbert norm, and all integer frequencies `arcFreq n`. -/
theorem exists_dyadic_jointExponentialTail_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ r₀ : ℕ, ∀ v : ℝ,
          |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v| ≤
            3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
              Real.exp (-((1 / 4 : ℝ) * |v|))) ∧
        (∀ r₀ : ℕ, ∀ x : ℝ, 1 ≤ |x| →
          |arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤
            3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * |x| ^ (-(3 / 4 : ℝ))) ∧
        (∀ r₀ : ℕ, ∀ x : ℝ, x ≠ 0 → |x| ≤ 1 →
          |arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x| ≤
            3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * |x| ^ (-(1 / 4 : ℝ))) ∧
        (∀ r₀ : ℕ, ∀ l : ℝ, |l| < 1 / 4 → ∀ τ : ℝ,
          |(∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                arcLineDyadicTowerVector k (r₀ + 1) ν x)| ≤
            (6600 * ν.real univ / (1 / 4 - |l|)) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) ∧
        (∀ l : ℝ, |l| < 1 / 2 →
          0 < ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 + l) ^ N)
          (𝓝[>] (-1 / 2)) (𝓝 0))) ∧
      (∀ l : ℝ, |l| < 1 / 2 →
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x)
          atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v))) ∧
      (∀ τ : ℝ,
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
            arcLineInfiniteDyadicVector k ν x)
          atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v))) ∧
      Tendsto (fun k : ℕ =>
        ∫ x in Ioi 0,
          (arcLineInfiniteDyadicVector k ν x - arcLineAtomicVector (Real.log k) ν x) ^ 2)
        atTop (𝓝 0) ∧
      (∀ n : ℕ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicSineMoment k ν (arcFreq n))
        atTop (𝓝 0)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym,
    fun k hk => ?_,
    fun l hl => tendsto_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_atTop_of_abs_lt_half hsym hl,
    fun τ => ?_,
    tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atomic_atTop hsym,
    tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop hblind⟩
  · exact ⟨fun r₀ v => abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk r₀ hsym v,
      fun r₀ x hx => abs_arcLineInfiniteDyadicVector_sub_succ_le_rpow_quarter_uniform hk r₀ hsym hx,
      fun r₀ x hx0 hx1 =>
        abs_arcLineInfiniteDyadicVector_sub_succ_le_rpow_quarter_near_zero hk r₀ hsym hx0 hx1,
      fun r₀ l hl τ =>
        abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_succ_le
          hk r₀ hsym hl τ,
      fun l hl =>
        setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hsym hpd hl,
      fun N =>
        tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin hk N hsym,
      fun N =>
        tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin_neg_half
          hk N hsym⟩
  · refine (tendsto_arcLineInfiniteDyadicCosTransform_atTop ν τ).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq hk hsym τ).symm

end

end RHTower
