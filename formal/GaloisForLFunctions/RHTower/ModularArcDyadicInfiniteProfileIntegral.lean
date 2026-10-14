import GaloisForLFunctions.RHTower.ModularArcDyadicStripInteriorPositivity

/-!
# Sub-critical exponential decay, `L¹(ℝ)` integrability, and exact integral representation of the infinite-horizon dyadic modular arc transforms

In `ModularArcDyadicInfiniteHorizonLimit`, `ModularArcDyadicCriticalLinePositivity`,
`ModularArcDyadicInfiniteOrderStripEdge`, and `ModularArcDyadicStripInteriorPositivity`, we
constructed the pointwise infinite-horizon profile `arcLineInfiniteDyadicProfile k ν : ℝ → ℝ` and
the limit transforms `arcLineInfiniteDyadicCosTransform k ν τ` (`τ ∈ ℝ`) and
`arcLineInfiniteDyadicLaplaceTransform k ν l` (`l ∈ [0, 1/2)`), defined as the `R → ∞` limits of
the finite-depth integrals `∫ cos(τv) arcLineDyadicTowerProfile k R ν v` and
`∫ e^{lv} arcLineDyadicTowerProfile k R ν v`.

In this module we prove that the infinite-horizon profile `arcLineInfiniteDyadicProfile k ν` itself
is a continuous, even, exponentially decaying function on `ℝ` whose **genuine Fourier-cosine and
Laplace/Mellin integrals** equal `arcLineInfiniteDyadicCosTransform k ν` and
`arcLineInfiniteDyadicLaplaceTransform k ν`:

1. **Universal symmetric shift inequality and scale-independent sub-critical exponential bound
   (`exp_neg_mul_abs_sub_add_le_two_cosh`, `abs_arcLineAtomicProfile_le_exp_mul`):**
   For all `c ≥ 0` and `v, w ∈ ℝ`,
   `(exp(−c|v − w|) + exp(−c|v + w|)) / 2 ≤ cosh(cw) · exp(−c|v|)`.
   Consequently, for every `b ∈ ℝ`, `c ∈ [0, 1/2]`, and `v ∈ ℝ`,
   `|arcLineAtomicProfile b ν v| ≤ 25 · ν.real univ · exp(−c|v|)` (completely independent of `b`).
2. **Depth-and-scale-uniform exponential decay `O(exp(−|v|/4))`
   (`two_pow_mul_cosh_quarter_div_cosh_log_pow_two_pow_le`,
   `abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform`,
   `abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform`):**
   Exploiting the dyadic squaring relation `k^{2^{s+1}} = (k^{2^s})²` at `c = 1/4`, we prove that
   for **every** `k ≥ 2`, **every** `R ∈ ℕ`, and **every** `v ∈ ℝ`,
   `|arcLineDyadicTowerProfile k R ν v| ≤ 825 · ν.real univ · exp(−|v| / 4)` and
   `|arcLineInfiniteDyadicProfile k ν v| ≤ 825 · ν.real univ · exp(−|v| / 4)`, with an absolute
   constant **completely independent of both `k` and `R`**.
3. **Depth-uniform sub-critical exponential decay across the entire strip `c ∈ [0, 1/2)`
   (`abs_arcLineDyadicTowerProfile_le_exp_subcritical`,
   `abs_arcLineInfiniteDyadicProfile_le_exp_subcritical`):**
   For every `c ∈ [0, 1/2)` and `k ≥ 2`, both `arcLineDyadicTowerProfile k R ν v` (for all `R ∈ ℕ`)
   and `arcLineInfiniteDyadicProfile k ν v` are bounded by
   `25 · ν.real univ · (1 + 16 / ((1 − 2c)² (log k)²)) · exp(−c|v|)`.
4. **Continuity, `L¹(ℝ)` integrability, and exact Dominated Convergence integral identification
   (`continuous_arcLineInfiniteDyadicProfile`,
   `integrable_arcLineInfiniteDyadicProfile`,
   `integrable_cos_mul_arcLineInfiniteDyadicProfile`,
   `integrable_exp_mul_arcLineInfiniteDyadicProfile`,
   `integral_cos_mul_arcLineInfiniteDyadicProfile_eq`,
   `integral_exp_mul_arcLineInfiniteDyadicProfile_eq`):**
   By Lebesgue's Dominated Convergence Theorem (`tendsto_integral_of_dominated_convergence`),
   `∫ cos(τv) arcLineInfiniteDyadicProfile k ν v = arcLineInfiniteDyadicCosTransform k ν τ` for all
   `τ ∈ ℝ` and `∫ e^{lv} arcLineInfiniteDyadicProfile k ν v = arcLineInfiniteDyadicLaplaceTransform k ν l`
   for all `l ∈ [0, 1/2)`.
5. **Single-profile critical-line positivity, strip interior positivity, and infinite-order edge
   vanishing (`integral_cos_mul_arcLineInfiniteDyadicProfile_pos`,
   `integral_exp_mul_arcLineInfiniteDyadicProfile_pos`,
   `abs_integral_exp_mul_arcLineInfiniteDyadicProfile_le_pow_sub_half`,
   `tendsto_div_pow_integral_exp_mul_arcLineInfiniteDyadicProfile_nhdsWithin`,
   `exists_dyadic_infiniteProfile_integral_arcWitness`):**
   For every `k ≥ 2`, the single continuous even profile `arcLineInfiniteDyadicProfile k ν` has
   strictly positive Fourier-cosine transform on `ℝ`, strictly positive Laplace/Mellin transform on
   `[0, 1/2)`, and vanishes to **infinite order `O((1/2 − l)^{N+1})` for every `N ∈ ℕ`** as `l → (1/2)⁻`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Symmetric shift inequality for `exp(−c|v|)` and scale-independent atomic profile decay -/

/-- Linear helper for `exp_neg_mul_abs_sub_add_le_two_cosh`: for `c ≥ 0` and `v, w ∈ ℝ`,
`(exp(−c|v − w|) + exp(−c|v + w|)) / 2 ≤ cosh(cw) · exp(−cv)`. -/
theorem exp_neg_mul_abs_sub_add_le_two_cosh_linear
    {c : ℝ} (hc : 0 ≤ c) (v w : ℝ) :
    (Real.exp (-(c * |v - w|)) + Real.exp (-(c * |v + w|))) / 2 ≤
      Real.cosh (c * w) * Real.exp (-(c * v)) := by
  have h1 : Real.exp (-(c * |v - w|)) ≤ Real.exp (c * w) * Real.exp (-(c * v)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self (v - w)])
  have h2 : Real.exp (-(c * |v + w|)) ≤ Real.exp (-(c * w)) * Real.exp (-(c * v)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self (v + w)])
  rw [Real.cosh_eq]
  linarith

/-- **Universal symmetric shift inequality for `exp(−c|v|)`:**
For all `c ≥ 0` and `v, w ∈ ℝ`,
`(exp(−c|v − w|) + exp(−c|v + w|)) / 2 ≤ cosh(cw) · exp(−c|v|)`. -/
theorem exp_neg_mul_abs_sub_add_le_two_cosh
    {c : ℝ} (hc : 0 ≤ c) (v w : ℝ) :
    (Real.exp (-(c * |v - w|)) + Real.exp (-(c * |v + w|))) / 2 ≤
      Real.cosh (c * w) * Real.exp (-(c * |v|)) := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    exact exp_neg_mul_abs_sub_add_le_two_cosh_linear hc v w
  · rw [abs_of_nonpos hv]
    have h := exp_neg_mul_abs_sub_add_le_two_cosh_linear hc (-v) (-w)
    have e1 : |-v - -w| = |v - w| := by rw [← abs_neg]; congr 1; ring
    have e2 : |-v + -w| = |v + w| := by rw [← abs_neg]; congr 1; ring
    have e3 : Real.cosh (c * -w) = Real.cosh (c * w) := by rw [mul_neg, Real.cosh_neg]
    rw [e1, e2, e3] at h
    exact h

/-- Sub-critical exponential decay bound for `arcPoissonProfile ν` across `c ≤ 1/2`. -/
theorem abs_arcPoissonProfile_le_exp_mul
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {c : ℝ} (hc : c ≤ 1 / 2) (v : ℝ) :
    |arcPoissonProfile ν v| ≤ 5 * ν.real univ * Real.exp (-(c * |v|)) := by
  have h1 := abs_arcPoissonProfile_le_exp hν v
  have h2 : Real.exp (-(|v| / 2)) ≤ Real.exp (-(c * |v|)) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg v])
  have h0 : 0 ≤ 5 * ν.real univ := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)

/-- **Scale-independent sub-critical exponential bound for `arcLineAtomicProfile b ν`:**
For **every** `b ∈ ℝ`, **every** `c ∈ [0, 1/2]`, and **every** `v ∈ ℝ`,
`|arcLineAtomicProfile b ν v| ≤ 25 · ν.real univ · exp(−c|v|)` (completely independent of `b`). -/
theorem abs_arcLineAtomicProfile_le_exp_mul
    (b : ℝ) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (v : ℝ) :
    |arcLineAtomicProfile b ν v| ≤ 25 * ν.real univ * Real.exp (-(c * |v|)) := by
  have hexp : arcLineAtomicProfile b ν v =
      atomW0 b * arcPoissonProfile ν v +
        atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)) +
        atomW2 b * (arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)) := by
    simp only [arcLineAtomicProfile, Fin.sum_univ_five, atomWeight, atomShift,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sub_zero, sub_neg_eq_add]
    ring
  set A := 5 * ν.real univ * Real.exp (-(c * |v|))
  have hν0 : 0 ≤ 5 * ν.real univ := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hC1 : 1 ≤ Real.cosh (b / 2) := Real.one_le_cosh (b / 2)
  have hCpos : 0 < Real.cosh (b / 2) := Real.cosh_pos (b / 2)
  have hCsq : 1 ≤ Real.cosh (b / 2) ^ 2 := by nlinarith
  have ht0 : |atomW0 b * arcPoissonProfile ν v| ≤ (3 / 2 : ℝ) * A := by
    have hw0_pos : 0 ≤ atomW0 b := by unfold atomW0; positivity
    have hw0_le : atomW0 b ≤ 3 / 2 := by
      unfold atomW0
      have : 1 / (2 * Real.cosh (b / 2) ^ 2) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      linarith
    rw [abs_mul, abs_of_nonneg hw0_pos]
    exact mul_le_mul hw0_le (abs_arcPoissonProfile_le_exp_mul hν hc v) (abs_nonneg _) (by positivity)
  have ht1 : |atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b))| ≤ 2 * A := by
    have hw1 : |atomW1 b| = 1 / Real.cosh (b / 2) := by
      unfold atomW1
      rw [abs_neg, abs_of_pos (by positivity)]
    have hsum1 : |arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)| ≤
        2 * Real.cosh (c * b) * A := by
      have hp1 := abs_arcPoissonProfile_le_exp_mul hν hc (v - b)
      have hp2 := abs_arcPoissonProfile_le_exp_mul hν hc (v + b)
      have hshift := exp_neg_mul_abs_sub_add_le_two_cosh hc0 v b
      have htri := (abs_add_le _ _).trans (add_le_add hp1 hp2)
      have hmul := mul_le_mul_of_nonneg_left hshift hν0
      dsimp [A]
      linarith
    have hcosh1 : Real.cosh (c * b) ≤ Real.cosh (b / 2) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_div, abs_of_nonneg hc0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg b]
    rw [abs_mul, hw1]
    calc 1 / Real.cosh (b / 2) * |arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)|
        ≤ 1 / Real.cosh (b / 2) * (2 * Real.cosh (c * b) * A) :=
          mul_le_mul_of_nonneg_left hsum1 (by positivity)
      _ ≤ 1 / Real.cosh (b / 2) * (2 * Real.cosh (b / 2) * A) := by
          gcongr
      _ = 2 * A := by field_simp
  have ht2 : |atomW2 b * (arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b))| ≤ A := by
    have hw2 : |atomW2 b| = 1 / (4 * Real.cosh (b / 2) ^ 2) := by
      unfold atomW2
      rw [abs_of_pos (by positivity)]
    have hsum2 : |arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)| ≤
        2 * Real.cosh (c * (2 * b)) * A := by
      have hp1 := abs_arcPoissonProfile_le_exp_mul hν hc (v - 2 * b)
      have hp2 := abs_arcPoissonProfile_le_exp_mul hν hc (v + 2 * b)
      have hshift := exp_neg_mul_abs_sub_add_le_two_cosh hc0 v (2 * b)
      have htri := (abs_add_le _ _).trans (add_le_add hp1 hp2)
      have hmul := mul_le_mul_of_nonneg_left hshift hν0
      dsimp [A]
      linarith
    have hcosh2 : Real.cosh (c * (2 * b)) ≤ 2 * Real.cosh (b / 2) ^ 2 := by
      have hle : Real.cosh (c * (2 * b)) ≤ Real.cosh b := by
        rw [Real.cosh_le_cosh, show c * (2 * b) = (2 * c) * b by ring, abs_mul,
          abs_of_nonneg (by positivity)]
        nlinarith [abs_nonneg b]
      have hdbl : Real.cosh b = 2 * Real.cosh (b / 2) ^ 2 - 1 := by
        have hb2 : Real.cosh b = Real.cosh (2 * (b / 2)) := by congr 1; ring
        rw [hb2, Real.cosh_two_mul, Real.sinh_sq]
        ring
      linarith
    rw [abs_mul, hw2]
    calc 1 / (4 * Real.cosh (b / 2) ^ 2) *
          |arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)|
        ≤ 1 / (4 * Real.cosh (b / 2) ^ 2) * (2 * Real.cosh (c * (2 * b)) * A) :=
          mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ ≤ 1 / (4 * Real.cosh (b / 2) ^ 2) * (2 * (2 * Real.cosh (b / 2) ^ 2) * A) := by
          gcongr
      _ = A := by field_simp; ring
  rw [hexp]
  have htri1 := abs_add_le
    (atomW0 b * arcPoissonProfile ν v +
      atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)))
    (atomW2 b * (arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)))
  have htri2 := abs_add_le
    (atomW0 b * arcPoissonProfile ν v)
    (atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)))
  have htotal : |atomW0 b * arcPoissonProfile ν v +
      atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)) +
      atomW2 b * (arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b))| ≤
      5 * A := by linarith
  refine htotal.trans_eq ?_
  dsimp [A]; ring

/-! ### Preservation of sub-critical exponential bounds across `symScaleProfile` and `hyperbolicFilterProfile` -/

/-- `symScaleProfile M` maps `|P(v)| ≤ B · exp(−c|v|)` to
`|symScaleProfile M P v| ≤ B · cosh(c · 2 log M) · exp(−c|v|)`. -/
theorem abs_symScaleProfile_le_exp_mul (M : ℕ) {P : ℝ → ℝ} {B c : ℝ}
    (hc0 : 0 ≤ c) (hP : ∀ v, |P v| ≤ B * Real.exp (-(c * |v|))) (v : ℝ) :
    |symScaleProfile M P v| ≤
      B * Real.cosh (c * (2 * Real.log M)) * Real.exp (-(c * |v|)) := by
  have hB0 : 0 ≤ B := by
    have h0 := (abs_nonneg (P 0)).trans (hP 0)
    simpa using h0
  unfold symScaleProfile forwardScaleProfile backwardScaleProfile
  rw [abs_mul, abs_of_pos (by positivity)]
  have h1 := hP (v - 2 * Real.log M)
  have h2 := hP (v + 2 * Real.log M)
  have htri := (abs_add_le _ _).trans (add_le_add h1 h2)
  have hshift := mul_le_mul_of_nonneg_left
    (exp_neg_mul_abs_sub_add_le_two_cosh hc0 v (2 * Real.log M)) hB0
  linarith

/-- For `c ∈ [0, 1/2]`, `hyperbolicFilterProfile M` maps `|P(v)| ≤ B · exp(−c|v|)` to
`|hyperbolicFilterProfile M P v| ≤ (2 B) · exp(−c|v|)`. -/
theorem abs_hyperbolicFilterProfile_le_exp_mul (M : ℕ) {P : ℝ → ℝ} {B c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
    (hP : ∀ v, |P v| ≤ B * Real.exp (-(c * |v|))) (v : ℝ) :
    |hyperbolicFilterProfile M P v| ≤ (2 * B) * Real.exp (-(c * |v|)) := by
  have hB0 : 0 ≤ B := by
    have h0 := (abs_nonneg (P 0)).trans (hP 0)
    simpa using h0
  rw [hyperbolicFilterProfile_eq_sub_symScaleProfile]
  have h0 := hP v
  have hS := abs_symScaleProfile_le_exp_mul M hc0 hP v
  have hcosh : Real.cosh (c * (2 * Real.log M)) / Real.cosh (Real.log M) ≤ 1 := by
    rw [div_le_one (Real.cosh_pos _), Real.cosh_le_cosh,
      show c * (2 * Real.log M) = (2 * c) * Real.log M by ring,
      abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [abs_nonneg (Real.log M)]
  have hmul : |(1 / Real.cosh (Real.log M)) * symScaleProfile M P v| ≤
      B * Real.exp (-(c * |v|)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / Real.cosh (Real.log M) * |symScaleProfile M P v|
        ≤ 1 / Real.cosh (Real.log M) *
            (B * Real.cosh (c * (2 * Real.log M)) * Real.exp (-(c * |v|))) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = (Real.cosh (c * (2 * Real.log M)) / Real.cosh (Real.log M)) *
            (B * Real.exp (-(c * |v|))) := by ring
      _ ≤ 1 * (B * Real.exp (-(c * |v|))) :=
          mul_le_mul_of_nonneg_right hcosh (by positivity)
      _ = B * Real.exp (-(c * |v|)) := one_mul _
  have hsub := abs_sub (P v) ((1 / Real.cosh (Real.log M)) * symScaleProfile M P v)
  linarith

/-- Scale-independent `2^r · (25 · ν.real univ) · exp(−c|v|)` bound at dyadic level `r`
for every `c ∈ [0, 1/2]`. -/
theorem abs_arcLineDyadicTowerProfile_le_two_pow_exp_mul
    (k r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) :
    ∀ v : ℝ, |arcLineDyadicTowerProfile k r ν v| ≤
      (2 ^ r * (25 * ν.real univ)) * Real.exp (-(c * |v|)) := by
  induction r with
  | zero =>
    intro v
    simpa [arcLineDyadicTowerProfile] using
      abs_arcLineAtomicProfile_le_exp_mul (Real.log k) hν hc0 hc v
  | succ r ih =>
    intro v
    have hstep := abs_hyperbolicFilterProfile_le_exp_mul (k ^ (2 ^ r)) hc0 hc ih v
    calc |arcLineDyadicTowerProfile k (r + 1) ν v|
        ≤ (2 * (2 ^ r * (25 * ν.real univ))) * Real.exp (-(c * |v|)) := hstep
      _ = (2 ^ (r + 1) * (25 * ν.real univ)) * Real.exp (-(c * |v|)) := by
          rw [pow_succ']; ring

/-- Scale-independent `2^r · (25 · ν.real univ) · cosh(c · 2 log(k^{2^r})) · exp(−c|v|)` bound for
`arcLineSymDyadicTowerProfile k r ν` across `c ∈ [0, 1/2]`. -/
theorem abs_arcLineSymDyadicTowerProfile_le_two_pow_exp_mul
    (k r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (v : ℝ) :
    |arcLineSymDyadicTowerProfile k r ν v| ≤
      (2 ^ r * (25 * ν.real univ)) *
        Real.cosh (c * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) * Real.exp (-(c * |v|)) :=
  abs_symScaleProfile_le_exp_mul (k ^ (2 ^ r)) hc0
    (abs_arcLineDyadicTowerProfile_le_two_pow_exp_mul k r hν hc0 hc) v

/-! ### Depth-and-scale-uniform `O(exp(−|v|/4))` bound and depth-uniform sub-critical `O(exp(−c|v|))` bound -/

/-- **Dyadic squaring bound at `c = 1/4` (`k ≥ 2`):**
Because `k^{2^{s+1}} = (k^{2^s})²`, at `c = 1/4` the half-exponent `(1/2) log(k^{2^{s+1}})` equals
`log(k^{2^s})`, yielding the scale-independent geometric bound
`2^r · cosh((1/4) · 2 log(k^{2^r})) / cosh(log(k^{2^r})) ≤ 16 · (1/2)^r` for all `k ≥ 2` and `r ∈ ℕ`. -/
theorem two_pow_mul_cosh_quarter_div_cosh_log_pow_two_pow_le
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    (2 : ℝ) ^ r *
        (Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) ≤
      16 * (1 / 2 : ℝ) ^ r := by
  rcases r with _ | s
  · set L := Real.log ((k ^ (2 ^ 0) : ℕ))
    have hcosh : Real.cosh ((1 / 4 : ℝ) * (2 * L)) / Real.cosh L ≤ 1 := by
      have habs : 0 ≤ |L| := abs_nonneg L
      rw [div_le_one (Real.cosh_pos _), Real.cosh_le_cosh]
      rw [show (1 / 4 : ℝ) * (2 * L) = (1 / 2 : ℝ) * L by ring,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    calc (2 : ℝ) ^ 0 * (Real.cosh ((1 / 4 : ℝ) * (2 * L)) / Real.cosh L)
        ≤ 1 * 1 := by linarith
      _ ≤ 16 * (1 / 2 : ℝ) ^ 0 := by norm_num
  · have hk1 : 1 ≤ k := by omega
    have hm_succ : (1 : ℝ) ≤ (k ^ (2 ^ (s + 1)) : ℕ) := by
      exact_mod_cast one_le_pow_two_pow hk1 (s + 1)
    have hb0 : 0 ≤ Real.log ((k ^ (2 ^ (s + 1)) : ℕ)) := Real.log_nonneg hm_succ
    have hstep1 := cosh_two_mul_div_cosh_le_two_mul_exp_neg hb0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hsq : ((k ^ (2 ^ (s + 1)) : ℕ) : ℝ) = ((k ^ (2 ^ s) : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast (pow_two_pow_sq k s).symm
    have hms_pos : (0 : ℝ) < (k ^ (2 ^ s) : ℕ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one (one_le_pow_two_pow hk1 s))
    have hexp_eq : Real.exp (-((1 - 2 * (1 / 4 : ℝ)) * Real.log ((k ^ (2 ^ (s + 1)) : ℕ)))) =
        (((k ^ (2 ^ s) : ℕ) : ℝ))⁻¹ := by
      rw [hsq, Real.log_pow, Nat.cast_ofNat,
        show -((1 - 2 * (1 / 4 : ℝ)) * (2 * Real.log ((k ^ (2 ^ s) : ℕ)))) =
          -Real.log ((k ^ (2 ^ s) : ℕ)) by ring,
        Real.exp_neg, Real.exp_log hms_pos]
    rw [hexp_eq] at hstep1
    have hdom := two_pow_mul_two_pow_le_two_mul_pow_two_pow hk s
    have hinv_le : (2 : ℝ) ^ s * (((k ^ (2 ^ s) : ℕ) : ℝ))⁻¹ ≤ 2 * (1 / 2 : ℝ) ^ s := by
      rw [← div_eq_mul_inv, div_le_iff₀ hms_pos]
      have hcancel : 2 * (1 / 2 : ℝ) ^ s * ((k ^ (2 ^ s) : ℕ) : ℝ) * (2 : ℝ) ^ s =
          2 * ((k ^ (2 ^ s) : ℕ) : ℝ) := by
        calc 2 * (1 / 2 : ℝ) ^ s * ((k ^ (2 ^ s) : ℕ) : ℝ) * (2 : ℝ) ^ s
            = 2 * ((k ^ (2 ^ s) : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ s * (2 : ℝ) ^ s) := by ring
          _ = 2 * ((k ^ (2 ^ s) : ℕ) : ℝ) * ((1 / 2 : ℝ) * 2) ^ s := by rw [← mul_pow]
          _ = 2 * ((k ^ (2 ^ s) : ℕ) : ℝ) := by norm_num
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      nlinarith
    calc (2 : ℝ) ^ (s + 1) *
          (Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ (s + 1)) : ℕ)))) /
            Real.cosh (Real.log ((k ^ (2 ^ (s + 1)) : ℕ))))
        ≤ (2 : ℝ) ^ (s + 1) * (2 * (((k ^ (2 ^ s) : ℕ) : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ = 4 * ((2 : ℝ) ^ s * (((k ^ (2 ^ s) : ℕ) : ℝ))⁻¹) := by rw [pow_succ']; ring
      _ ≤ 4 * (2 * (1 / 2 : ℝ) ^ s) := mul_le_mul_of_nonneg_left hinv_le (by positivity)
      _ = 16 * (1 / 2 : ℝ) ^ (s + 1) := by rw [pow_succ']; ring

/-- **Geometric `(1/2)^r` step bound with `exp(−|v|/4)` decay (`k ≥ 2`).** -/
theorem abs_arcLineDyadicTowerProfile_succ_sub_le_exp_quarter
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |(1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v| ≤
      (400 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) * (1 / 2 : ℝ) ^ r := by
  rw [abs_mul, abs_of_pos (by positivity)]
  have hS := abs_arcLineSymDyadicTowerProfile_le_two_pow_exp_mul k r hν
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) v
  have hratio := two_pow_mul_cosh_quarter_div_cosh_log_pow_two_pow_le hk r
  have hB0 : 0 ≤ 25 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |arcLineSymDyadicTowerProfile k r ν v|
      ≤ 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
          ((2 ^ r * (25 * ν.real univ)) *
            Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) *
            Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ((2 : ℝ) ^ r *
          (Real.cosh ((1 / 4 : ℝ) * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
            Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))) *
          (25 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ ≤ (16 * (1 / 2 : ℝ) ^ r) *
          (25 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul_of_nonneg_right hratio hB0
    _ = (400 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) * (1 / 2 : ℝ) ^ r := by ring

/-- **Depth-and-scale-uniform `O(exp(−|v|/4))` bound for `arcLineDyadicTowerProfile k R ν`:**
For **every** integer `k ≥ 2`, **every** dyadic depth `R ∈ ℕ`, and **every** `v ∈ ℝ`,
`|arcLineDyadicTowerProfile k R ν v| ≤ 825 · ν.real univ · exp(−|v| / 4)`
(with an absolute constant completely independent of BOTH `k` and `R`). -/
theorem abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineDyadicTowerProfile k R ν v| ≤
      825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  rw [arcLineDyadicTowerProfile_eq_atomic_sub_sum k R ν v]
  have h0 := abs_arcLineAtomicProfile_le_exp_mul (Real.log k) hν
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) v
  set B := 25 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))
  have hB0 : 0 ≤ B := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    dsimp [B]; positivity
  have hsum : |∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v| ≤
      (16 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    refine (abs_arcLineDyadicTowerProfile_succ_sub_le_exp_quarter hk r hν v).trans_eq ?_
    dsimp [B]; ring
  have hgeom : (16 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r ≤ 32 * B := by
    have h2 := sum_range_half_pow_le_two R
    nlinarith
  have hsub := abs_sub (arcLineAtomicProfile (Real.log k) ν v)
    (∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v)
  calc |arcLineAtomicProfile (Real.log k) ν v -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            arcLineSymDyadicTowerProfile k r ν v|
      ≤ B + 32 * B := by linarith
    _ = 825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)) := by dsimp [B]; ring

/-- **Depth-and-scale-uniform `O(exp(−|v|/4))` bound for the infinite-horizon profile (`k ≥ 2`):**
For every `k ≥ 2` and `v ∈ ℝ`,
`|arcLineInfiniteDyadicProfile k ν v| ≤ 825 · ν.real univ · exp(−|v| / 4)`
(with constant completely independent of `k`). -/
theorem abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v| ≤
      825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)) :=
  le_of_tendsto (continuous_abs.tendsto _ |>.comp (tendsto_arcLineDyadicTowerProfile_atTop hk ν v))
    (Eventually.of_forall fun R => abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v)

/-- Quadratic decay bound `exp(−y) ≤ 4 / y²` for `y > 0`. -/
theorem exp_neg_le_four_div_sq {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ 4 / y ^ 2 := by
  have hy2 : 0 < y / 2 := by linarith
  have h1 := exp_neg_le_one_div hy2
  have heq : Real.exp (-y) = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [heq]
  calc Real.exp (-(y / 2)) * Real.exp (-(y / 2))
      ≤ (1 / (y / 2)) * (1 / (y / 2)) :=
        mul_le_mul h1 h1 (Real.exp_pos _).le (by positivity)
    _ = 4 / y ^ 2 := by ring

/-- **Sub-critical geometric `cosh` ratio bound across all `c ∈ [0, 1/2)` (`k ≥ 2`):**
For every `k ≥ 2`, `r ∈ ℕ`, and `c ∈ [0, 1/2)`,
`2^r · cosh(c · 2 log(k^{2^r})) / cosh(log(k^{2^r})) ≤ (8 / ((1 − 2c)² (log k)²)) · (1/2)^r`. -/
theorem two_pow_mul_cosh_div_cosh_log_pow_two_pow_le
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) :
    (2 : ℝ) ^ r *
        (Real.cosh (c * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) ≤
      (8 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2)) * (1 / 2 : ℝ) ^ r := by
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hlog : 0 < Real.log k := Real.log_pos hkgt1
  have h12c : 0 < 1 - 2 * c := by linarith
  set b := Real.log ((k ^ (2 ^ r) : ℕ))
  have hb_eq : b = (2 : ℝ) ^ r * Real.log k := by
    dsimp [b]
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hb0 : 0 ≤ b := by rw [hb_eq]; positivity
  have hy : 0 < (1 - 2 * c) * b := by rw [hb_eq]; positivity
  have h1 := cosh_two_mul_div_cosh_le_two_mul_exp_neg hb0 hc0
  have h2 := exp_neg_le_four_div_sq hy
  calc (2 : ℝ) ^ r * (Real.cosh (c * (2 * b)) / Real.cosh b)
      ≤ (2 : ℝ) ^ r * (2 * Real.exp (-((1 - 2 * c) * b))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (2 : ℝ) ^ r * (2 * (4 / ((1 - 2 * c) * b) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
    _ = (8 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2)) * (1 / 2 : ℝ) ^ r := by
        rw [hb_eq, one_div_pow]
        field_simp
        ring

/-- **Sub-critical geometric `(1/2)^r` step bound for any `c ∈ [0, 1/2)` (`k ≥ 2`).** -/
theorem abs_arcLineDyadicTowerProfile_succ_sub_le_exp_subcritical
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) (v : ℝ) :
    |(1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v| ≤
      (25 * ν.real univ * (8 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2)) *
        Real.exp (-(c * |v|))) * (1 / 2 : ℝ) ^ r := by
  rw [abs_mul, abs_of_pos (by positivity)]
  have hS := abs_arcLineSymDyadicTowerProfile_le_two_pow_exp_mul k r hν hc0 hc.le v
  have hratio := two_pow_mul_cosh_div_cosh_log_pow_two_pow_le hk r hc0 hc
  have hB0 : 0 ≤ 25 * ν.real univ * Real.exp (-(c * |v|)) := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |arcLineSymDyadicTowerProfile k r ν v|
      ≤ 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
          ((2 ^ r * (25 * ν.real univ)) *
            Real.cosh (c * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) *
            Real.exp (-(c * |v|))) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ((2 : ℝ) ^ r *
          (Real.cosh (c * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
            Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))) *
          (25 * ν.real univ * Real.exp (-(c * |v|))) := by ring
    _ ≤ ((8 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2)) * (1 / 2 : ℝ) ^ r) *
          (25 * ν.real univ * Real.exp (-(c * |v|))) :=
        mul_le_mul_of_nonneg_right hratio hB0
    _ = (25 * ν.real univ * (8 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2)) *
          Real.exp (-(c * |v|))) * (1 / 2 : ℝ) ^ r := by ring

/-- **Depth-uniform sub-critical exponential decay across all `c ∈ [0, 1/2)` and `R ∈ ℕ` (`k ≥ 2`):**
For every `k ≥ 2`, `R ∈ ℕ`, `c ∈ [0, 1/2)`, and `v ∈ ℝ`,
`|arcLineDyadicTowerProfile k R ν v| ≤ 25 · ν.real univ · (1 + 16 / ((1 − 2c)² (log k)²)) · exp(−c|v|)`. -/
theorem abs_arcLineDyadicTowerProfile_le_exp_subcritical
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) (v : ℝ) :
    |arcLineDyadicTowerProfile k R ν v| ≤
      (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) *
        Real.exp (-(c * |v|)) := by
  rw [arcLineDyadicTowerProfile_eq_atomic_sub_sum k R ν v]
  have h0 := abs_arcLineAtomicProfile_le_exp_mul (Real.log k) hν hc0 hc.le v
  set B := 25 * ν.real univ * Real.exp (-(c * |v|))
  set K := 8 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2)
  have hB0 : 0 ≤ B := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    dsimp [B]; positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hsum : |∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v| ≤
      (K * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    refine (abs_arcLineDyadicTowerProfile_succ_sub_le_exp_subcritical hk r hν hc0 hc v).trans_eq ?_
    dsimp [B, K]; ring
  have hgeom : (K * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r ≤ 2 * K * B := by
    have h2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two R) (mul_nonneg hK0 hB0)
    linarith
  have hsub := abs_sub (arcLineAtomicProfile (Real.log k) ν v)
    (∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v)
  calc |arcLineAtomicProfile (Real.log k) ν v -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            arcLineSymDyadicTowerProfile k r ν v|
      ≤ B + 2 * K * B := by linarith
    _ = (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) *
          Real.exp (-(c * |v|)) := by dsimp [B, K]; ring

/-- **Sub-critical exponential decay of `arcLineInfiniteDyadicProfile k ν` across all `c ∈ [0, 1/2)` (`k ≥ 2`).** -/
theorem abs_arcLineInfiniteDyadicProfile_le_exp_subcritical
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v| ≤
      (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) *
        Real.exp (-(c * |v|)) :=
  le_of_tendsto (continuous_abs.tendsto _ |>.comp (tendsto_arcLineDyadicTowerProfile_atTop hk ν v))
    (Eventually.of_forall fun R =>
      abs_arcLineDyadicTowerProfile_le_exp_subcritical hk R hν hc0 hc v)

/-! ### Continuity, `L¹(ℝ)` integrability, and Dominated Convergence integral identification -/

theorem continuous_symScaleProfile (M : ℕ) {P : ℝ → ℝ} (hP : Continuous P) :
    Continuous (symScaleProfile M P) := by
  unfold symScaleProfile forwardScaleProfile backwardScaleProfile
  fun_prop

theorem continuous_hyperbolicFilterProfile (M : ℕ) {P : ℝ → ℝ} (hP : Continuous P) :
    Continuous (hyperbolicFilterProfile M P) := by
  unfold hyperbolicFilterProfile
  fun_prop

theorem continuous_arcLineDyadicTowerProfile (k r : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] :
    Continuous (arcLineDyadicTowerProfile k r ν) := by
  induction r with
  | zero => exact continuous_arcLineAtomicProfile (Real.log k) ν
  | succ r ih => exact continuous_hyperbolicFilterProfile (k ^ (2 ^ r)) ih

theorem continuous_arcLineSymDyadicTowerProfile (k r : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] :
    Continuous (arcLineSymDyadicTowerProfile k r ν) :=
  continuous_symScaleProfile (k ^ (2 ^ r)) (continuous_arcLineDyadicTowerProfile k r ν)

/-- **Continuity of the infinite-horizon dyadic profile `arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`).** -/
theorem continuous_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Continuous (arcLineInfiniteDyadicProfile k ν) := by
  unfold arcLineInfiniteDyadicProfile
  refine (continuous_arcLineAtomicProfile (Real.log k) ν).sub ?_
  refine continuous_tsum
    (fun r => continuous_const.mul (continuous_arcLineSymDyadicTowerProfile k r ν))
    (summable_geometric_two.mul_left (32 * ν.real univ)) fun r v => ?_
  rw [Real.norm_eq_abs]
  exact abs_arcLineDyadicTowerProfile_succ_sub_le hk r ν v

/-- **`L¹(ℝ)` integrability of `arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`).** -/
theorem integrable_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Integrable (arcLineInfiniteDyadicProfile k ν) := by
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (825 * ν.real univ)).mono'
    (continuous_arcLineInfiniteDyadicProfile hk ν).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]
  exact abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v

/-- **`L¹(ℝ)` integrability of `cos(τv) · arcLineInfiniteDyadicProfile k ν v` (`k ≥ 2`, `τ ∈ ℝ`).** -/
theorem integrable_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Integrable fun v => Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v :=
  (integrable_arcLineInfiniteDyadicProfile hk hν).bdd_mul (by fun_prop)
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- **Unconditional Dominated Convergence on the critical line (`R → ∞`):**
For every `k ≥ 2` and `τ ∈ ℝ`, the genuine Fourier-cosine integral of
`arcLineInfiniteDyadicProfile k ν` equals `arcLineInfiniteDyadicCosTransform k ν τ`. -/
theorem integral_cos_mul_arcLineInfiniteDyadicProfile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    (∫ v, Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      arcLineInfiniteDyadicCosTransform k ν τ := by
  have hdom : Tendsto (fun R : ℕ => ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v)
      atTop (𝓝 (∫ v, Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun v => 825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)))
      (fun R => ((by fun_prop : Continuous fun v : ℝ => Real.cos (τ * v)).mul
        (continuous_arcLineDyadicTowerProfile k R ν)).aestronglyMeasurable)
      ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
        (825 * ν.real univ))
      (fun R => Eventually.of_forall fun v => ?_)
      (Eventually.of_forall fun v => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Real.cos (τ * v)| * |arcLineDyadicTowerProfile k R ν v|
          ≤ 1 * (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
            mul_le_mul (Real.abs_cos_le_one _)
              (abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v)
              (abs_nonneg _) zero_le_one
        _ = 825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)) := one_mul _
    · exact (tendsto_arcLineDyadicTowerProfile_atTop hk ν v).const_mul (Real.cos (τ * v))
  exact tendsto_nhds_unique hdom
    (tendsto_integral_cos_mul_arcLineDyadicTowerProfile_atTop hk ν τ)

/-- **`L¹(ℝ)` integrability of `e^{lv} · arcLineInfiniteDyadicProfile k ν v` across `l ∈ [0, 1/2)` (`k ≥ 2`).** -/
theorem integrable_exp_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Integrable fun v => Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v := by
  set c := (l + 1 / 2) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc : c < 1 / 2 := by dsimp [c]; linarith
  have hcl : 0 < c - l := by dsimp [c]; linarith
  set A := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))
  refine ((integrable_rexp_neg_mul_abs hcl).const_mul A).mono'
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v)).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |Real.exp (l * v)| * |arcLineInfiniteDyadicProfile k ν v|
      ≤ Real.exp (l * |v|) * (A * Real.exp (-(c * |v|))) :=
        mul_le_mul (abs_exp_mul_le hl0)
          (abs_arcLineInfiniteDyadicProfile_le_exp_subcritical hk hν hc0 hc v)
          (abs_nonneg _) (Real.exp_pos _).le
    _ = A * Real.exp (-((c - l) * |v|)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- **Unconditional Dominated Convergence on the strip `l ∈ [0, 1/2)` (`R → ∞`):**
For every `k ≥ 2` and `l ∈ [0, 1/2)`, the genuine Laplace/Mellin integral of
`arcLineInfiniteDyadicProfile k ν` equals `arcLineInfiniteDyadicLaplaceTransform k ν l`. -/
theorem integral_exp_mul_arcLineInfiniteDyadicProfile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    (∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) =
      arcLineInfiniteDyadicLaplaceTransform k ν l := by
  have hk1 : 1 ≤ k := by omega
  set c := (l + 1 / 2) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc : c < 1 / 2 := by dsimp [c]; linarith
  have hcl : 0 < c - l := by dsimp [c]; linarith
  set A := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))
  have hdom : Tendsto (fun R : ℕ => ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v)
      atTop (𝓝 (∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun v => A * Real.exp (-((c - l) * |v|)))
      (fun R => ((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v)).mul
        (continuous_arcLineDyadicTowerProfile k R ν)).aestronglyMeasurable)
      ((integrable_rexp_neg_mul_abs hcl).const_mul A)
      (fun R => Eventually.of_forall fun v => ?_)
      (Eventually.of_forall fun v => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Real.exp (l * v)| * |arcLineDyadicTowerProfile k R ν v|
          ≤ Real.exp (l * |v|) * (A * Real.exp (-(c * |v|))) :=
            mul_le_mul (abs_exp_mul_le hl0)
              (abs_arcLineDyadicTowerProfile_le_exp_subcritical hk R hν hc0 hc v)
              (abs_nonneg _) (Real.exp_pos _).le
        _ = A * Real.exp (-((c - l) * |v|)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    · exact (tendsto_arcLineDyadicTowerProfile_atTop hk ν v).const_mul (Real.exp (l * v))
  exact tendsto_nhds_unique hdom
    (tendsto_integral_exp_mul_arcLineDyadicTowerProfile_atTop hk1 hν hl0 hl)

/-! ### Direct integral consequences for the single continuous profile `arcLineInfiniteDyadicProfile k ν` -/

/-- **Strict critical-line positive definiteness of the genuine Fourier-cosine integral of
`arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`).** -/
theorem integral_cos_mul_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [integral_cos_mul_arcLineInfiniteDyadicProfile_eq hk hν τ]
  exact arcLineInfiniteDyadicCosTransform_pos hk hpd τ

/-- **Strict interior strip positivity of the genuine Laplace/Mellin integral of
`arcLineInfiniteDyadicProfile k ν` across `l ∈ [0, 1/2)` (`k ≥ 2`).** -/
theorem integral_exp_mul_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 < ∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [integral_exp_mul_arcLineInfiniteDyadicProfile_eq hk hν hl0 hl]
  exact arcLineInfiniteDyadicLaplaceTransform_pos hk hν hpd hl0 hl

/-- **Infinite-order (`O((1/2 − l)^{N+1})` for every `N ∈ ℕ`) strip-edge vanishing of the genuine
Laplace/Mellin integral of `arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`).** -/
theorem abs_integral_exp_mul_arcLineInfiniteDyadicProfile_le_pow_sub_half
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v| ≤
      (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - l) ^ (N + 1) := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_exp_mul_arcLineInfiniteDyadicProfile_eq hk hν hl0 hl]
  exact arcLineInfiniteDyadicLaplaceTransform_le_pow_sub_half hk1 N hν hl0 hl

/-- **Infinite-order divided-difference vanishing as `l → (1/2)⁻` for the genuine Laplace/Mellin
integral of `arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`).** -/
theorem tendsto_div_pow_integral_exp_mul_arcLineInfiniteDyadicProfile_nhdsWithin
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) / (1 / 2 - l) ^ N)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  have hk1 : 1 ≤ k := by omega
  have hlim := tendsto_div_pow_arcLineInfiniteDyadicLaplaceTransform_nhdsWithin hk1 N hν
  have heq : ∀ᶠ l in 𝓝[<] (1 / 2 : ℝ),
      arcLineInfiniteDyadicLaplaceTransform k ν l / (1 / 2 - l) ^ N =
        (∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) / (1 / 2 - l) ^ N := by
    have hlt : ∀ᶠ l in 𝓝[<] (1 / 2 : ℝ), l < 1 / 2 := eventually_mem_nhdsWithin
    have hgt : ∀ᶠ l in 𝓝[<] (1 / 2 : ℝ), (0 : ℝ) < l :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hlt, hgt] with l hl hl0
    rw [integral_exp_mul_arcLineInfiniteDyadicProfile_eq hk hν hl0.le hl]
  exact hlim.congr' heq

/-- **Master unconditional theorem for the single continuous profile `arcLineInfiniteDyadicProfile k ν`.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, the single function `P_k = arcLineInfiniteDyadicProfile k ν : ℝ → ℝ` satisfies:
1. `P_k` is continuous, even (`P_k(−v) = P_k(v)`), and satisfies the `k`-independent exponential
   decay bound `|P_k(v)| ≤ 825 · ν.real univ · exp(−|v| / 4)` for all `v ∈ ℝ`;
2. For every `c ∈ [0, 1/2)` and `v ∈ ℝ`,
   `|P_k(v)| ≤ 25 · ν.real univ · (1 + 16 / ((1 − 2c)² (log k)²)) · exp(−c|v|)`;
3. `P_k` is `L¹(ℝ)`-integrable against `cos(τv)` (`τ ∈ ℝ`) and against `e^{lv}` (`l ∈ [0, 1/2)`),
   with genuine integrals equal to `arcLineInfiniteDyadicCosTransform k ν τ` and
   `arcLineInfiniteDyadicLaplaceTransform k ν l`;
4. Its genuine Fourier-cosine integral is strictly positive (`0 < ∫ cos(τv) P_k(v) dv`) for every
   `τ ∈ ℝ`, and its genuine Laplace/Mellin integral is strictly positive (`0 < ∫ e^{lv} P_k(v) dv`)
   for every `l ∈ [0, 1/2)` while vanishing to **infinite order (`O((1/2 − l)^{N+1})` for every `N ∈ ℕ`)**
   as `l → (1/2)⁻`;
5. As `k → ∞`, `∫ cos(τv) P_k(v) dv → ∫ cos(τv) arcPoissonProfile ν v > 0` for all `τ ∈ ℝ`,
   `∫ e^{lv} P_k(v) dv → ∫ e^{lv} arcPoissonProfile ν v > 0` for all `l ∈ [0, 1/2)`, and
   `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` for all `n ∈ ℕ`. -/
theorem exists_dyadic_infiniteProfile_integral_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        Continuous (arcLineInfiniteDyadicProfile k ν) ∧
        Integrable (arcLineInfiniteDyadicProfile k ν) ∧
        (∀ v : ℝ, arcLineInfiniteDyadicProfile k ν (-v) = arcLineInfiniteDyadicProfile k ν v) ∧
        (∀ v : ℝ, |arcLineInfiniteDyadicProfile k ν v| ≤
          825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) ∧
        (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ∧
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          0 < ∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) ∧
        (∀ N : ℕ, ∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v| ≤
            (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - l) ^ (N + 1)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) / (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0))) ∧
      (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
        Tendsto (fun k : ℕ => ∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v)
          atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v))) ∧
      (∀ τ : ℝ,
        Tendsto (fun k : ℕ => ∫ v, Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
          atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v))) ∧
      (∀ n : ℕ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicSineMoment k ν (arcFreq n))
        atTop (𝓝 0)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym,
    fun k hk => ?_,
    fun l hl0 hl => ?_,
    fun τ => ?_,
    tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop hblind⟩
  · exact ⟨continuous_arcLineInfiniteDyadicProfile hk ν,
      integrable_arcLineInfiniteDyadicProfile hk hsym,
      arcLineInfiniteDyadicProfile_neg k ν,
      abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hsym,
      integral_cos_mul_arcLineInfiniteDyadicProfile_pos hk hsym hpd,
      fun l hl0 hl => integral_exp_mul_arcLineInfiniteDyadicProfile_pos hk hsym hpd hl0 hl,
      fun N l hl0 hl =>
        abs_integral_exp_mul_arcLineInfiniteDyadicProfile_le_pow_sub_half hk N hsym hl0 hl,
      fun N => tendsto_div_pow_integral_exp_mul_arcLineInfiniteDyadicProfile_nhdsWithin hk N hsym⟩
  · refine (tendsto_arcLineInfiniteDyadicLaplaceTransform_atTop hsym hl0 hl).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (integral_exp_mul_arcLineInfiniteDyadicProfile_eq hk hsym hl0 hl).symm
  · refine (tendsto_arcLineInfiniteDyadicCosTransform_atTop ν τ).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (integral_cos_mul_arcLineInfiniteDyadicProfile_eq hk hsym τ).symm

end

end RHTower
