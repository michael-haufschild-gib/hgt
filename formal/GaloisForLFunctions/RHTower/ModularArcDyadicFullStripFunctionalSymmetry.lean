import GaloisForLFunctions.RHTower.ModularArcDyadicHilbertEnergyConvergence

/-!
# Functional equation reflection symmetry `l ↦ −l` (`s ↔ 1 − s`), full critical-strip (`|l| < 1/2`) interior positivity, and two-sided infinite-order edge vanishing

In `ModularArcDyadicInfiniteLineVector` and `ModularArcDyadicHilbertEnergyConvergence`, the
multiplicative Mellin transform
`M_k(l) = ∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx = ∫_ℝ e^{lv} · arcLineInfiniteDyadicProfile k ν v dv`
was analyzed on the right half-strip `l ∈ [0, 1/2)`.

In this module we extend the theory to the **entire open critical strip `l ∈ (−1/2, 1/2)`**
(`|l| < 1/2`, corresponding to `Re(s) = 1/2 + l ∈ (0, 1)`) via the **functional equation
reflection `l ↦ −l` (`s ↔ 1 − s`)**:

1. **Exact `l ↦ −l` reflection invariance and `cosh(lv)` representation
   (`integral_exp_neg_mul_arcLineInfiniteDyadicProfile`,
   `integral_exp_abs_mul_arcLineInfiniteDyadicProfile`,
   `setIntegral_Ioi_rpow_neg_sub_half_mul_arcLineInfiniteDyadicVector`,
   `setIntegral_Ioi_rpow_abs_sub_half_mul_arcLineInfiniteDyadicVector`,
   `integral_exp_mul_arcLineInfiniteDyadicProfile_eq_cosh`):**
   For every `l ∈ ℝ`,
   `∫_{x > 0} x^{−l − 1/2} · arcLineInfiniteDyadicVector k ν x dx = ∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx = ∫_{x > 0} x^{|l| − 1/2} · arcLineInfiniteDyadicVector k ν x dx`.
   For every `|l| < 1/2`, this integral equals `∫_ℝ cosh(lv) · arcLineInfiniteDyadicProfile k ν v dv = arcLineInfiniteDyadicLaplaceTransform k ν |l|`.
2. **Full critical-strip (`|l| < 1/2`) interior positivity and two-sided infinite-order edge
   vanishing (`setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half`,
   `abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_abs`,
   `tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin_neg_half`):**
   - For every `l ∈ (−1/2, 1/2)` (`|l| < 1/2`),
     `0 < ∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx`.
   - For every `N ∈ ℕ` and every `|l| < 1/2`,
     `|∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx| ≤ (10 · ν.real univ · dyadicStripConst k N) · (1/2 − |l|)^{N+1}`.
   - Both as `l → (1/2)⁻` (`Re(s) → 1⁻`) and as `l → (−1/2)⁺` (`Re(s) → 0⁺`), the Mellin transform
     vanishes to **infinite order (`O((1/2 ∓ l)^N)` for every `N ∈ ℕ`)**.
3. **Full critical-strip `k → ∞` convergence (`tendsto_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_atTop_of_abs_lt_half`,
   `exists_dyadic_fullStrip_functionalSymmetry_arcWitness`):**
   For every `l ∈ (−1/2, 1/2)`, as `k → ∞`,
   `∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx → ∫_ℝ e^{lv} · arcPoissonProfile ν v dv > 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Reflection symmetry `l ↦ −l` on the logarithmic axis `v ∈ ℝ` -/

/-- Reflection symmetry `l ↦ −l` for the Laplace transform of `arcPoissonProfile ν`:
`∫_ℝ e^{−lv} · arcPoissonProfile ν v dv = ∫_ℝ e^{lv} · arcPoissonProfile ν v dv`. -/
theorem integral_exp_neg_mul_arcPoissonProfile (ν : Measure ArcParam) (l : ℝ) :
    (∫ v : ℝ, Real.exp ((-l) * v) * arcPoissonProfile ν v) =
      ∫ v : ℝ, Real.exp (l * v) * arcPoissonProfile ν v := by
  have h := integral_neg_eq_self
    (fun v : ℝ => Real.exp (l * v) * arcPoissonProfile ν v) volume
  simpa [mul_neg, neg_mul, arcPoissonProfile_neg] using h

/-- Absolute-value reduction `l ↦ |l|` for the Laplace transform of `arcPoissonProfile ν`. -/
theorem integral_exp_abs_mul_arcPoissonProfile (ν : Measure ArcParam) (l : ℝ) :
    (∫ v : ℝ, Real.exp (|l| * v) * arcPoissonProfile ν v) =
      ∫ v : ℝ, Real.exp (l * v) * arcPoissonProfile ν v := by
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl]
  · rw [abs_of_nonpos hl, integral_exp_neg_mul_arcPoissonProfile]

/-- **Reflection symmetry `l ↦ −l` for the Laplace transform of `arcLineInfiniteDyadicProfile k ν`:**
For every `l ∈ ℝ`,
`∫_ℝ e^{−lv} · arcLineInfiniteDyadicProfile k ν v dv = ∫_ℝ e^{lv} · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem integral_exp_neg_mul_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ v : ℝ, Real.exp ((-l) * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v := by
  have h := integral_neg_eq_self
    (fun v : ℝ => Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) volume
  simpa [mul_neg, neg_mul, arcLineInfiniteDyadicProfile_neg] using h

/-- **Absolute-value reduction `l ↦ |l|` for the Laplace transform of `arcLineInfiniteDyadicProfile k ν`:**
For every `l ∈ ℝ`,
`∫_ℝ e^{|l|v} · arcLineInfiniteDyadicProfile k ν v dv = ∫_ℝ e^{lv} · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem integral_exp_abs_mul_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ v : ℝ, Real.exp (|l| * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v := by
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl]
  · rw [abs_of_nonpos hl, integral_exp_neg_mul_arcLineInfiniteDyadicProfile]

/-- Integrability of `e^{lv} · arcLineInfiniteDyadicProfile k ν v` across the full open critical
strip `|l| < 1/2` (`k ≥ 2`). -/
theorem integrable_exp_mul_arcLineInfiniteDyadicProfile_of_abs_lt_half
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    Integrable (fun v : ℝ => Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) := by
  rcases le_total 0 l with hl0 | hl0
  · rw [abs_of_nonneg hl0] at hl
    exact integrable_exp_mul_arcLineInfiniteDyadicProfile hk hν hl0 hl
  · rw [abs_of_nonpos hl0] at hl
    have hpos : Integrable (fun v : ℝ => Real.exp ((-l) * v) * arcLineInfiniteDyadicProfile k ν v) :=
      integrable_exp_mul_arcLineInfiniteDyadicProfile hk hν (by linarith) hl
    have heq : (fun v : ℝ => Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => Real.exp ((-l) * -v) * arcLineInfiniteDyadicProfile k ν (-v) := by
      funext v
      rw [arcLineInfiniteDyadicProfile_neg, mul_neg, neg_mul, neg_neg]
    rw [heq]
    exact hpos.comp_neg

/-- **Exact `cosh(lv)` representation of the Laplace transform of `arcLineInfiniteDyadicProfile k ν`
across the full open critical strip `|l| < 1/2` (`k ≥ 2`):**
`∫_ℝ e^{lv} · arcLineInfiniteDyadicProfile k ν v dv = ∫_ℝ cosh(lv) · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem integral_exp_mul_arcLineInfiniteDyadicProfile_eq_cosh
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ v : ℝ, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hIl : Integrable (fun v : ℝ => Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_exp_mul_arcLineInfiniteDyadicProfile_of_abs_lt_half hk hν hl
  have hIneg : Integrable (fun v : ℝ => Real.exp (-(l * v)) * arcLineInfiniteDyadicProfile k ν v) := by
    have heq : (fun v : ℝ => Real.exp (-(l * v)) * arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => Real.exp ((-l) * v) * arcLineInfiniteDyadicProfile k ν v := by
      funext v; rw [neg_mul]
    rw [heq]
    exact integrable_exp_mul_arcLineInfiniteDyadicProfile_of_abs_lt_half hk hν (by simpa using hl)
  have hneg_eq : (∫ v : ℝ, Real.exp (-(l * v)) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v := by
    have heq : (fun v : ℝ => Real.exp (-(l * v)) * arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => Real.exp ((-l) * v) * arcLineInfiniteDyadicProfile k ν v := by
      funext v; rw [neg_mul]
    rw [heq, integral_exp_neg_mul_arcLineInfiniteDyadicProfile]
  have e : (fun v : ℝ => Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => (1 / 2 : ℝ) * (Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v +
        Real.exp (-(l * v)) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v; rw [Real.cosh_eq]; ring
  rw [e, integral_const_mul, integral_add hIl hIneg, hneg_eq]
  ring

/-! ### Functional equation reflection `l ↦ −l` (`s ↔ 1 − s`) for the multiplicative Mellin integral on `(0, ∞)` -/

/-- **Functional equation reflection `l ↦ −l` (`s ↔ 1 − s`) for the multiplicative Mellin integral
of `arcLineInfiniteDyadicVector k ν` (`k ≥ 1`):**
For every `l ∈ ℝ`,
`∫_{x > 0} x^{−l − 1/2} · arcLineInfiniteDyadicVector k ν x dx = ∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx`. -/
theorem setIntegral_Ioi_rpow_neg_sub_half_mul_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (-l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
  rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk ν (-l),
    setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk ν l,
    integral_exp_neg_mul_arcLineInfiniteDyadicProfile]

/-- **Absolute-value reduction `l ↦ |l|` for the multiplicative Mellin integral of
`arcLineInfiniteDyadicVector k ν` (`k ≥ 1`):**
For every `l ∈ ℝ`,
`∫_{x > 0} x^{|l| − 1/2} · arcLineInfiniteDyadicVector k ν x dx = ∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx`. -/
theorem setIntegral_Ioi_rpow_abs_sub_half_mul_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (|l| - 1 / 2) * arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl]
  · rw [abs_of_nonpos hl, setIntegral_Ioi_rpow_neg_sub_half_mul_arcLineInfiniteDyadicVector hk ν l]

/-- **Full-strip identification with `arcLineInfiniteDyadicLaplaceTransform k ν |l|` (`k ≥ 2`, `|l| < 1/2`).** -/
theorem setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_of_abs_lt_half
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) =
      arcLineInfiniteDyadicLaplaceTransform k ν |l| := by
  have hk1 : 1 ≤ k := by omega
  rw [← setIntegral_Ioi_rpow_abs_sub_half_mul_arcLineInfiniteDyadicVector hk1 ν l,
    setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq hk hν (abs_nonneg l) hl]

/-! ### Full critical-strip (`|l| < 1/2`) interior positivity and two-sided infinite-order edge vanishing -/

/-- **Strict interior positivity across the entire open critical strip `l ∈ (−1/2, 1/2)` (`|l| < 1/2`, `k ≥ 2`).** -/
theorem setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    0 < ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
  have hk1 : 1 ≤ k := by omega
  rw [← setIntegral_Ioi_rpow_abs_sub_half_mul_arcLineInfiniteDyadicVector hk1 ν l]
  exact setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos hk hν hpd (abs_nonneg l) hl

/-- **Symmetric two-sided infinite-order (`O((1/2 − |l|)^{N+1})` for every `N ∈ ℕ`) strip-edge
bound across the entire open critical strip `|l| < 1/2` (`k ≥ 2`).** -/
theorem abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_abs
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    |∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x| ≤
      (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - |l|) ^ (N + 1) := by
  have hk1 : 1 ≤ k := by omega
  rw [← setIntegral_Ioi_rpow_abs_sub_half_mul_arcLineInfiniteDyadicVector hk1 ν l]
  exact abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_half
    hk N hν (abs_nonneg l) hl

/-- **Infinite-order divided-difference vanishing at the left strip edge `l → (−1/2)⁺` (`Re(s) → 0⁺`, `k ≥ 2`):**
For every `N ∈ ℕ`,
`(∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx) / (1/2 + l)^N → 0` as `l → (−1/2)⁺`. -/
theorem tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin_neg_half
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / (1 / 2 + l) ^ N)
      (𝓝[>] (-1 / 2)) (𝓝 0) := by
  have hk1 : 1 ≤ k := by omega
  have hmap : Tendsto (fun l : ℝ => -l) (𝓝[>] (-1 / 2)) (𝓝[<] (1 / 2)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · rw [show (1 / 2 : ℝ) = -(-1 / 2 : ℝ) by ring]
      exact continuous_neg.continuousWithinAt.tendsto
    · filter_upwards [self_mem_nhdsWithin] with l hl
      simp only [mem_Ioi] at hl
      simp only [mem_Iio]
      linarith
  have hright :=
    (tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin
      hk N hν).comp hmap
  refine hright.congr' (Eventually.of_forall fun l => ?_)
  dsimp only [Function.comp_apply]
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_arcLineInfiniteDyadicVector hk1 ν l, sub_neg_eq_add]

/-- **Full critical-strip (`|l| < 1/2`) `k → ∞` convergence of the multiplicative Mellin integral of
`arcLineInfiniteDyadicVector k ν` to `∫_ℝ e^{lv} · arcPoissonProfile ν v dv`.** -/
theorem tendsto_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_atTop_of_abs_lt_half
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 2) :
    Tendsto (fun k : ℕ =>
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x)
      atTop (𝓝 (∫ v : ℝ, Real.exp (l * v) * arcPoissonProfile ν v)) := by
  have hpos : Tendsto (fun k : ℕ =>
      ∫ x in Ioi 0, x ^ (|l| - 1 / 2) * arcLineInfiniteDyadicVector k ν x)
      atTop (𝓝 (∫ v : ℝ, Real.exp (|l| * v) * arcPoissonProfile ν v)) := by
    refine (tendsto_arcLineInfiniteDyadicLaplaceTransform_atTop hν (abs_nonneg l) hl).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq hk hν (abs_nonneg l) hl).symm
  rw [← integral_exp_abs_mul_arcPoissonProfile ν l]
  refine hpos.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk1
  exact setIntegral_Ioi_rpow_abs_sub_half_mul_arcLineInfiniteDyadicVector hk1 ν l

/-! ### Master unconditional theorem for the full critical strip `|l| < 1/2` -/

/-- **Master unconditional theorem for the functional equation reflection symmetry `l ↦ −l`
(`s ↔ 1 − s`), full critical-strip (`|l| < 1/2`) interior positivity, and two-sided infinite-order
strip-edge vanishing of `arcLineInfiniteDyadicVector k ν`.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, the single line-model vector
`V_k = arcLineInfiniteDyadicVector k ν : ℝ → ℝ` satisfies:
1. Exact functional equation reflection symmetry `l ↦ −l` (`s ↔ 1 − s`) on `(0, ∞)`:
   for all `l ∈ ℝ`,
   `∫_{x > 0} x^{−l − 1/2} V_k(x) dx = ∫_{x > 0} x^{l − 1/2} V_k(x) dx = ∫_{x > 0} x^{|l| − 1/2} V_k(x) dx`;
2. Strict interior positivity across the **entire open critical strip `l ∈ (−1/2, 1/2)`** (`|l| < 1/2`):
   `0 < ∫_{x > 0} x^{l − 1/2} V_k(x) dx`;
3. Symmetric two-sided infinite-order (`O((1/2 − |l|)^{N+1})` for every `N ∈ ℕ`) strip-edge bound
   across all `|l| < 1/2`:
   `|∫_{x > 0} x^{l − 1/2} V_k(x) dx| ≤ (10 · ν.real univ · dyadicStripConst k N) · (1/2 − |l|)^{N+1}`;
4. Infinite-order divided-difference vanishing at **both** strip edges `l → (1/2)⁻` (`Re(s) → 1⁻`)
   and `l → (−1/2)⁺` (`Re(s) → 0⁺`) for every `N ∈ ℕ`:
   `(∫_{x > 0} x^{l − 1/2} V_k(x) dx) / (1/2 − l)^N → 0` as `l → (1/2)⁻` and
   `(∫_{x > 0} x^{l − 1/2} V_k(x) dx) / (1/2 + l)^N → 0` as `l → (−1/2)⁺`;
5. Strict `L²((0, ∞))` Hilbert energy positivity and `k`-independent upper bound:
   `0 < ∫_{x > 0} (V_k(x))² dx ≤ 475200 · (ν.real univ)²`;
6. As `k → ∞`, simultaneously:
   - `∫_{x > 0} x^{l − 1/2} V_k(x) dx → ∫ e^{lv} arcPoissonProfile ν v > 0` for all `|l| < 1/2`,
   - `∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx → ∫ cos(τv) arcPoissonProfile ν v > 0` for all `τ ∈ ℝ`,
   - `∫_{x > 0} (V_k(x) − arcLineAtomicVector (log k) ν x)² dx → 0` (at rate `O(k⁻¹)`), and
   - `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` for all `n ∈ ℕ`. -/
theorem exists_dyadic_fullStrip_functionalSymmetry_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ l : ℝ,
          (∫ x in Ioi 0, x ^ (-l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) =
            ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ∧
        (∀ l : ℝ, |l| < 1 / 2 →
          0 < ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ∧
        (∀ N : ℕ, ∀ l : ℝ, |l| < 1 / 2 →
          |∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x| ≤
            (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - |l|) ^ (N + 1)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 + l) ^ N)
          (𝓝[>] (-1 / 2)) (𝓝 0)) ∧
        0 < (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤ 475200 * (ν.real univ) ^ 2) ∧
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
  · have hk1 : 1 ≤ k := by omega
    exact ⟨fun l => setIntegral_Ioi_rpow_neg_sub_half_mul_arcLineInfiniteDyadicVector hk1 ν l,
      fun l hl =>
        setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hsym hpd hl,
      fun N l hl =>
        abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_abs hk N hsym hl,
      fun N =>
        tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin hk N hsym,
      fun N =>
        tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin_neg_half
          hk N hsym,
      setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hsym hpd,
      setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_uniform hk hsym⟩
  · refine (tendsto_arcLineInfiniteDyadicCosTransform_atTop ν τ).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq hk hsym τ).symm

end

end RHTower
