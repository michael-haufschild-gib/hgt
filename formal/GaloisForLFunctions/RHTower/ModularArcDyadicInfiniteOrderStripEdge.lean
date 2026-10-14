import GaloisForLFunctions.RHTower.ModularArcDyadicCriticalLinePositivity

/-!
# Monotone strip contraction and infinite-order (`O((1/2 − l)^N)` for all `N ∈ ℕ`) strip-edge vanishing for the infinite-horizon dyadic modular arc tower

In `ModularArcDyadicHyperbolicTower`, each finite dyadic level `R ∈ ℕ` was shown to satisfy
order-`(R + 1)` strip-edge vanishing `|∫ e^{lv} arcLineDyadicTowerProfile k R ν v| ≤ C_{k,R} (1/2 − l)^{R+1}`
for `l ∈ [0, 1/2)`, where the witness depended on the target order `R`.

In this module we prove that on the strip `l ∈ [0, 1/2)`, the dyadic hyperbolic tower is
**non-negative and monotonically decreasing (`Antitone`) in depth `R`**, so that its infinite-horizon
limit `arcLineInfiniteDyadicLaplaceTransform k ν` is a **single `R`-independent transform** that is
strictly positive at the strip center `l = 0` (`= arcLineInfiniteDyadicCosTransform k ν 0 > 0`)
while vanishing to **infinite order (`O((1/2 − l)^{N+1})` for EVERY `N ∈ ℕ`)** at the strip edge
`l → (1/2)⁻`:

1. **Pointwise and strip non-negativity (`arcPoissonProfile_nonneg`,
   `integral_exp_mul_arcPoissonProfile_nonneg`,
   `integral_exp_mul_arcLineDyadicTowerProfile_nonneg`):**
   Because `arcPoissonProfile ν v ≥ 0` for all `v ∈ ℝ`, at `R = 0` the squared factor
   `(1 − cosh(l log k) / cosh(½ log k))² ≥ 0` preserves non-negativity, and at every step `r`
   the multiplier `1 − cosh(2l log(k^{2^r})) / cosh(log(k^{2^r}))` lies in `[0, 1)` for all
   `l ∈ [0, 1/2)`.
2. **Monotone contraction (`Antitone`) across dyadic depth `R`
   (`integral_exp_mul_arcLineDyadicTowerProfile_succ_le`,
   `antitone_integral_exp_mul_arcLineDyadicTowerProfile`):**
   For every `k ≥ 1` and `l ∈ [0, 1/2)`,
   `0 ≤ ∫ e^{lv} arcLineDyadicTowerProfile k (R + 1) ν v ≤ ∫ e^{lv} arcLineDyadicTowerProfile k R ν v`.
3. **Unconditional `R → ∞` convergence and exact weld at `l = 0`
   (`tendsto_integral_exp_mul_arcLineDyadicTowerProfile_atTop`,
   `arcLineInfiniteDyadicLaplaceTransform_zero_eq_cosTransform`,
   `arcLineInfiniteDyadicLaplaceTransform_zero_pos`):**
   As `R → ∞`, the strip Laplace/Mellin transforms converge monotonically to
   `arcLineInfiniteDyadicLaplaceTransform k ν l ≥ 0`, which at `l = 0` coincides with
   `arcLineInfiniteDyadicCosTransform k ν 0 > 0`.
4. **Infinite-order (`C^∞`-flat) strip-edge vanishing as `l → (1/2)⁻`
   (`arcLineInfiniteDyadicLaplaceTransform_le_pow_sub_half`,
   `tendsto_div_pow_arcLineInfiniteDyadicLaplaceTransform_nhdsWithin`,
   `exists_dyadic_infiniteOrder_stripEdge_arcWitness`):**
   Because `0 ≤ arcLineInfiniteDyadicLaplaceTransform k ν l ≤ ∫ e^{lv} arcLineDyadicTowerProfile k N ν v`
   holds simultaneously for **every** `N ∈ ℕ`, for every `N ∈ ℕ` we have
   `arcLineInfiniteDyadicLaplaceTransform k ν l ≤ (10 · ν.real univ · dyadicStripConst k N) · (1/2 − l)^{N+1}`
   and `arcLineInfiniteDyadicLaplaceTransform k ν l / (1/2 − l)^N → 0` as `l → (1/2)⁻`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Non-negativity and monotone (`Antitone`) strip contraction across dyadic depth `R` -/

/-- Pointwise non-negativity of `arcPoissonProfile ν` on `ℝ`. -/
theorem arcPoissonProfile_nonneg (ν : Measure ArcParam) (v : ℝ) :
    0 ≤ arcPoissonProfile ν v := by
  unfold arcPoissonProfile
  refine integral_nonneg fun u => ?_
  have hp := cosh_sub_arc_pos u v
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hp.le _)

/-- Non-negativity of the Laplace/Mellin strip transform of `arcPoissonProfile ν` for all `l ∈ ℝ`. -/
theorem integral_exp_mul_arcPoissonProfile_nonneg (ν : Measure ArcParam) (l : ℝ) :
    0 ≤ ∫ v, Real.exp (l * v) * arcPoissonProfile ν v :=
  integral_nonneg fun v => mul_nonneg (Real.exp_pos _).le (arcPoissonProfile_nonneg ν v)

/-- One-step Laplace/Mellin strip recursion for `arcLineDyadicTowerProfile`. -/
theorem integral_exp_mul_arcLineDyadicTowerProfile_succ
    (k r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k (r + 1) ν v =
      (1 - Real.cosh (l * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v :=
  integral_exp_mul_hyperbolicFilterProfile (k ^ (2 ^ r))
    (integrable_exp_mul_arcLineDyadicTowerProfile k r hν hl0 hl)

/-- **Closed-form Euler-product factorization of the Laplace/Mellin strip transform at dyadic depth `R`.** -/
theorem integral_exp_mul_arcLineDyadicTowerProfile
    (k R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v =
      (∏ r ∈ Finset.range R,
        (1 - Real.cosh (l * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))) *
        (1 - Real.cosh (l * Real.log k) / Real.cosh (Real.log k / 2)) ^ 2 *
        ∫ v, Real.exp (l * v) * arcPoissonProfile ν v := by
  induction R with
  | zero =>
    rw [Finset.prod_range_zero, one_mul]
    exact integral_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl
  | succ R ih =>
    rw [integral_exp_mul_arcLineDyadicTowerProfile_succ k R hν hl0 hl, ih, Finset.prod_range_succ]
    ring

/-- On the strip `l ∈ [0, 1/2)`, for any `m ≥ 1`, the hyperbolic strip multiplier
`1 − cosh(l · 2 log m) / cosh(log m)` lies in `[0, 1)`. -/
theorem sub_cosh_div_cosh_log_mem_Icc
    {m : ℕ} (hm : 1 ≤ m) {l : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2) :
    0 ≤ 1 - Real.cosh (l * (2 * Real.log m)) / Real.cosh (Real.log m) ∧
      1 - Real.cosh (l * (2 * Real.log m)) / Real.cosh (Real.log m) ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hC := Real.cosh_pos (Real.log m)
  constructor
  · rw [sub_nonneg, div_le_one hC, Real.cosh_le_cosh]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg hlog]
    nlinarith
  · have hpos : 0 ≤ Real.cosh (l * (2 * Real.log m)) / Real.cosh (Real.log m) := by positivity
    linarith

/-- **Non-negativity of the Laplace/Mellin strip transform across all dyadic depths `r ∈ ℕ` (`l ∈ [0, 1/2)`).** -/
theorem integral_exp_mul_arcLineDyadicTowerProfile_nonneg
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 ≤ ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v := by
  induction r with
  | zero =>
    change 0 ≤ ∫ v, Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v
    rw [integral_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl]
    exact mul_nonneg (sq_nonneg _) (integral_exp_mul_arcPoissonProfile_nonneg ν l)
  | succ r ih =>
    rw [integral_exp_mul_arcLineDyadicTowerProfile_succ k r hν hl0 hl]
    exact mul_nonneg
      (sub_cosh_div_cosh_log_mem_Icc (one_le_pow_two_pow hk r) hl0 hl.le).1 ih

/-- **Monotone one-step contraction of the Laplace/Mellin strip transform (`l ∈ [0, 1/2)`).** -/
theorem integral_exp_mul_arcLineDyadicTowerProfile_succ_le
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k (r + 1) ν v ≤
      ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v := by
  rw [integral_exp_mul_arcLineDyadicTowerProfile_succ k r hν hl0 hl]
  have h1 := (sub_cosh_div_cosh_log_mem_Icc (one_le_pow_two_pow hk r) hl0 hl.le).2
  have h0 := integral_exp_mul_arcLineDyadicTowerProfile_nonneg hk r hν hl0 hl
  nlinarith

/-- **Monotone decreasing (`Antitone`) property of `R ↦ ∫ e^{lv} arcLineDyadicTowerProfile k R ν v` on `[0, 1/2)`.** -/
theorem antitone_integral_exp_mul_arcLineDyadicTowerProfile
    {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Antitone fun R : ℕ => ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v :=
  antitone_nat_of_succ_le fun R =>
    integral_exp_mul_arcLineDyadicTowerProfile_succ_le hk R hν hl0 hl

theorem bddBelow_range_integral_exp_mul_arcLineDyadicTowerProfile
    {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    BddBelow (range fun R : ℕ => ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v) :=
  ⟨0, by rintro _ ⟨R, rfl⟩; exact integral_exp_mul_arcLineDyadicTowerProfile_nonneg hk R hν hl0 hl⟩

/-! ### The infinite-horizon strip Laplace/Mellin transform, `l = 0` weld, and infinite-order edge vanishing -/

/-- The infinite-horizon dyadic Laplace/Mellin strip transform:
`L_{k,∞}(l) = ⨅ R : ℕ, ∫ e^{lv} arcLineDyadicTowerProfile k R ν v`. -/
def arcLineInfiniteDyadicLaplaceTransform (k : ℕ) (ν : Measure ArcParam) (l : ℝ) : ℝ :=
  ⨅ R : ℕ, ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v

/-- **Unconditional `R → ∞` convergence of the strip Laplace/Mellin transform on `[0, 1/2)`.** -/
theorem tendsto_integral_exp_mul_arcLineDyadicTowerProfile_atTop
    {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Tendsto (fun R : ℕ => ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v)
      atTop (𝓝 (arcLineInfiniteDyadicLaplaceTransform k ν l)) :=
  tendsto_atTop_ciInf
    (antitone_integral_exp_mul_arcLineDyadicTowerProfile hk hν hl0 hl)
    (bddBelow_range_integral_exp_mul_arcLineDyadicTowerProfile hk hν hl0 hl)

/-- Non-negativity of `arcLineInfiniteDyadicLaplaceTransform k ν l` on `[0, 1/2)`. -/
theorem arcLineInfiniteDyadicLaplaceTransform_nonneg
    {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 ≤ arcLineInfiniteDyadicLaplaceTransform k ν l :=
  le_ciInf fun R => integral_exp_mul_arcLineDyadicTowerProfile_nonneg hk R hν hl0 hl

/-- **Domination by every finite dyadic level `R ∈ ℕ` (`l ∈ [0, 1/2)`):**
For every `R ∈ ℕ`, `arcLineInfiniteDyadicLaplaceTransform k ν l ≤ ∫ e^{lv} arcLineDyadicTowerProfile k R ν v`. -/
theorem arcLineInfiniteDyadicLaplaceTransform_le
    {k : ℕ} (hk : 1 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    arcLineInfiniteDyadicLaplaceTransform k ν l ≤
      ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v :=
  ciInf_le (bddBelow_range_integral_exp_mul_arcLineDyadicTowerProfile hk hν hl0 hl) R

/-- **Exact weld at the strip center `l = 0` (`s = 1/2`, `τ = 0`):**
At `l = 0`, `arcLineInfiniteDyadicLaplaceTransform k ν 0` coincides with the infinite-horizon
critical-line cosine transform `arcLineInfiniteDyadicCosTransform k ν 0`. -/
theorem arcLineInfiniteDyadicLaplaceTransform_zero_eq_cosTransform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    arcLineInfiniteDyadicLaplaceTransform k ν 0 =
      arcLineInfiniteDyadicCosTransform k ν 0 := by
  have hk1 : 1 ≤ k := by omega
  have hL := tendsto_integral_exp_mul_arcLineDyadicTowerProfile_atTop hk1 hν
    le_rfl (by norm_num : (0 : ℝ) < 1 / 2)
  have hC := tendsto_integral_cos_mul_arcLineDyadicTowerProfile_atTop hk ν 0
  have heq : (fun R : ℕ => ∫ v, Real.exp (0 * v) * arcLineDyadicTowerProfile k R ν v) =
      fun R : ℕ => ∫ v, Real.cos (0 * v) * arcLineDyadicTowerProfile k R ν v := by
    funext R
    simp [Real.exp_zero, Real.cos_zero]
  rw [heq] at hL
  exact tendsto_nhds_unique hL hC

/-- **Strict positivity at the strip center `l = 0` (`k ≥ 2`).** -/
theorem arcLineInfiniteDyadicLaplaceTransform_zero_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    0 < arcLineInfiniteDyadicLaplaceTransform k ν 0 := by
  rw [arcLineInfiniteDyadicLaplaceTransform_zero_eq_cosTransform hk hν]
  exact arcLineInfiniteDyadicCosTransform_pos hk hpd 0

/-- **Infinite-order (`O((1/2 − l)^{N+1})` for EVERY `N ∈ ℕ`) strip-edge vanishing bound:**
Because `0 ≤ arcLineInfiniteDyadicLaplaceTransform k ν l ≤ ∫ e^{lv} arcLineDyadicTowerProfile k N ν v`
holds for **every** `N ∈ ℕ` simultaneously, the single infinite-horizon Laplace/Mellin transform
satisfies the order-`(N + 1)` strip-edge bound for **all** `N ∈ ℕ`. -/
theorem arcLineInfiniteDyadicLaplaceTransform_le_pow_sub_half
    {k : ℕ} (hk : 1 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |arcLineInfiniteDyadicLaplaceTransform k ν l| ≤
      (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - l) ^ (N + 1) := by
  rw [abs_of_nonneg (arcLineInfiniteDyadicLaplaceTransform_nonneg hk hν hl0 hl)]
  have hle := arcLineInfiniteDyadicLaplaceTransform_le hk N hν hl0 hl
  have hN := abs_integral_exp_mul_arcLineDyadicTowerProfile_le hk N hν hl0 hl
  exact hle.trans ((le_abs_self _).trans hN)

/-- **Infinite-order (`C^∞`-flat) divided-difference vanishing at `l → (1/2)⁻`:**
For every integer `k ≥ 1` and **every** order `N ∈ ℕ`,
`arcLineInfiniteDyadicLaplaceTransform k ν l / (1/2 − l)^N → 0` as `l → (1/2)⁻`. -/
theorem tendsto_div_pow_arcLineInfiniteDyadicLaplaceTransform_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      arcLineInfiniteDyadicLaplaceTransform k ν l / (1 / 2 - l) ^ N)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := 10 * ν.real univ * dyadicStripConst k N
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  have hκ : 0 < 1 / 2 - l := by linarith [hl.2]
  have hpow : 0 < (1 / 2 - l) ^ N := pow_pos hκ N
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  calc |arcLineInfiniteDyadicLaplaceTransform k ν l|
      ≤ D * (1 / 2 - l) ^ (N + 1) :=
        arcLineInfiniteDyadicLaplaceTransform_le_pow_sub_half hk N hν hl.1.le hl.2
    _ = D * (1 / 2 - l) * (1 / 2 - l) ^ N := by rw [pow_succ']; ring

/-! ### Master unconditional infinite-order strip-edge and critical-line positivity witness theorem -/

/-- **Master unconditional theorem for infinite-order strip-edge vanishing and critical-line positivity.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`:
1. On the strip `l ∈ [0, 1/2)`, `R ↦ ∫ e^{lv} arcLineDyadicTowerProfile k R ν v` is non-negative,
   monotonically decreasing (`Antitone`), and converges unconditionally as `R → ∞` to
   `arcLineInfiniteDyadicLaplaceTransform k ν l ≥ 0`;
2. At the strip center `l = 0` (`s = 1/2`), `arcLineInfiniteDyadicLaplaceTransform k ν 0` coincides
   with `arcLineInfiniteDyadicCosTransform k ν 0 > 0`, and on the entire critical line `τ ∈ ℝ`,
   `0 < arcLineInfiniteDyadicCosTransform k ν τ`;
3. At the strip edge `l → (1/2)⁻` (`s → 1⁻`), the **single `R`-independent transform**
   `arcLineInfiniteDyadicLaplaceTransform k ν` vanishes to **infinite order (`O((1/2 − l)^{N+1})`
   for EVERY `N ∈ ℕ`)**:
   `∀ N ∈ ℕ, lim_{l → (1/2)⁻} arcLineInfiniteDyadicLaplaceTransform k ν l / (1/2 − l)^N = 0`. -/
theorem exists_dyadic_infiniteOrder_stripEdge_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k →
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          Antitone (fun R : ℕ => ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v) ∧
          Tendsto (fun R : ℕ => ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v)
            atTop (𝓝 (arcLineInfiniteDyadicLaplaceTransform k ν l)) ∧
          0 ≤ arcLineInfiniteDyadicLaplaceTransform k ν l) ∧
        arcLineInfiniteDyadicLaplaceTransform k ν 0 = arcLineInfiniteDyadicCosTransform k ν 0 ∧
        0 < arcLineInfiniteDyadicLaplaceTransform k ν 0 ∧
        (∀ τ : ℝ, 0 < arcLineInfiniteDyadicCosTransform k ν τ) ∧
        (∀ N : ℕ, ∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |arcLineInfiniteDyadicLaplaceTransform k ν l| ≤
            (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - l) ^ (N + 1)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          arcLineInfiniteDyadicLaplaceTransform k ν l / (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0)) := by
  obtain ⟨ν, hfin, hne, hsym, _, hpd⟩ := exists_arcWitness
  refine ⟨ν, hfin, hne, hsym, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨fun l hl0 hl =>
      ⟨antitone_integral_exp_mul_arcLineDyadicTowerProfile hk1 hsym hl0 hl,
       tendsto_integral_exp_mul_arcLineDyadicTowerProfile_atTop hk1 hsym hl0 hl,
       arcLineInfiniteDyadicLaplaceTransform_nonneg hk1 hsym hl0 hl⟩,
    arcLineInfiniteDyadicLaplaceTransform_zero_eq_cosTransform hk hsym,
    arcLineInfiniteDyadicLaplaceTransform_zero_pos hk hsym hpd,
    fun τ => arcLineInfiniteDyadicCosTransform_pos hk hpd τ,
    fun N l hl0 hl => arcLineInfiniteDyadicLaplaceTransform_le_pow_sub_half hk1 N hsym hl0 hl,
    fun N => tendsto_div_pow_arcLineInfiniteDyadicLaplaceTransform_nhdsWithin hk1 N hsym⟩

end

end RHTower
