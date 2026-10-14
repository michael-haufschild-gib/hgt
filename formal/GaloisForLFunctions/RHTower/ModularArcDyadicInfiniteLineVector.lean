import GaloisForLFunctions.RHTower.ModularArcDyadicInfiniteProfileIntegral

/-!
# The infinite-horizon dyadic line-model vector: `x ↦ 1/x` self-reciprocity, `O(|x|^{−3/4})` decay, and multiplicative Mellin strip positivity with infinite-order edge vanishing

In `ModularArcDyadicInfiniteProfileIntegral`, we proved that on the logarithmic axis `v ∈ ℝ`, the
infinite-horizon profile `arcLineInfiniteDyadicProfile k ν : ℝ → ℝ` is a continuous, even,
exponentially decaying (`O(exp(−|v|/4))` uniformly in `k ≥ 2`) function whose genuine
Fourier-cosine and Laplace/Mellin integrals equal `arcLineInfiniteDyadicCosTransform k ν` and
`arcLineInfiniteDyadicLaplaceTransform k ν`.

In this module we complete the real-line (`x ∈ ℝ`) and multiplicative (`x ∈ (0, ∞)`) theory of the
infinite-horizon dyadic modular arc witness by constructing the **infinite-horizon line-model
vector** `arcLineInfiniteDyadicVector k ν : ℝ → ℝ`:

1. **Unconditional `R → ∞` convergence, origin vanishing, even parity, and `x ↦ 1/x` Mellin
   self-reciprocity (`tendsto_arcLineDyadicTowerVector_atTop`,
   `arcLineInfiniteDyadicVector_zero`, `arcLineInfiniteDyadicVector_neg_of_map_arcNeg`,
   `arcLineInfiniteDyadicVector_inv`):**
   For every `k ≥ 2` and `x ∈ ℝ`, `arcLineDyadicTowerVector k R ν x → arcLineInfiniteDyadicVector k ν x`
   as `R → ∞`, and `arcLineInfiniteDyadicVector k ν` is even, vanishes at `x = 0`, and satisfies
   exact `x ↦ 1/x` self-reciprocity `f(1/x) = |x| f(x)` for all `x ≠ 0`.
2. **Exact log-scale bridge and `k`-independent `O(|x|^{−3/4})` power-law decay
   (`exp_half_mul_arcLineInfiniteDyadicVector`,
   `arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile`,
   `abs_arcLineInfiniteDyadicVector_le_rpow_quarter_uniform`,
   `abs_arcLineInfiniteDyadicVector_le_rpow_subcritical`):**
   For all `v ∈ ℝ`, `exp(v/2) · arcLineInfiniteDyadicVector k ν (exp v) = arcLineInfiniteDyadicProfile k ν v`,
   and for all `|x| ≥ 1`, `|arcLineInfiniteDyadicVector k ν x| ≤ 825 · ν.real univ · |x|^{−3/4}`
   independently of `k ≥ 2` (and `O(|x|^{−(1/2 + c)})` for every `c ∈ [0, 1/2)`).
3. **Exact multiplicative Mellin and critical-line integral identities on `(0, ∞)`
   (`setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos`,
   `abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_half`,
   `tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin`,
   `setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_pos`,
   `exists_dyadic_infiniteLineVector_mellin_arcWitness`):**
   On `(0, ∞)`, the multiplicative Mellin integral
   `∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx` equals
   `arcLineInfiniteDyadicLaplaceTransform k ν l`, so it is **strictly positive (`> 0`) for every
   `l ∈ [0, 1/2)`** and **vanishes to infinite order (`O((1/2 − l)^{N+1})` for every `N ∈ ℕ`)** at
   the strip edge `l → (1/2)⁻`, while its critical-line oscillatory Mellin integral
   `∫_{x > 0} x^{−1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx` equals
   `arcLineInfiniteDyadicCosTransform k ν τ > 0` for all `τ ∈ ℝ`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Origin vanishing and log-scale bridge at finite dyadic levels -/

theorem forwardScaleVec_zero (M : ℕ) {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    forwardScaleVec M f 0 = 0 := by
  simp [forwardScaleVec, hf0]

theorem backwardScaleVec_zero (M : ℕ) {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    backwardScaleVec M f 0 = 0 := by
  simp [backwardScaleVec, hf0]

theorem symScaleVec_zero (M : ℕ) {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    symScaleVec M f 0 = 0 := by
  unfold symScaleVec
  rw [forwardScaleVec_zero M hf0, backwardScaleVec_zero M hf0, add_zero, mul_zero]

theorem hyperbolicFilterVec_zero (M : ℕ) {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    hyperbolicFilterVec M f 0 = 0 := by
  rw [hyperbolicFilterVec_eq_sub_symScaleVec, hf0, symScaleVec_zero M hf0, mul_zero, sub_zero]

theorem arcLineDyadicTowerVector_zero (k r : ℕ) (ν : Measure ArcParam) :
    arcLineDyadicTowerVector k r ν 0 = 0 := by
  induction r with
  | zero => exact arcLineAtomicVector_zero (Real.log k) ν
  | succ r ih => exact hyperbolicFilterVec_zero (k ^ (2 ^ r)) ih

theorem arcLineSymDyadicTowerVector_zero (k r : ℕ) (ν : Measure ArcParam) :
    arcLineSymDyadicTowerVector k r ν 0 = 0 :=
  symScaleVec_zero (k ^ (2 ^ r)) (arcLineDyadicTowerVector_zero k r ν)

/-- Exact log-scale bridge for `arcLineSymDyadicTowerVector k r ν`. -/
theorem exp_half_mul_arcLineSymDyadicTowerVector
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineSymDyadicTowerVector k r ν (Real.exp v) =
      arcLineSymDyadicTowerProfile k r ν v :=
  exp_half_mul_symScaleVec (one_le_pow_two_pow hk r)
    (exp_half_mul_arcLineDyadicTowerVector hk r ν) v

/-- For `x ≠ 0` and an `arcNeg`-symmetric measure `ν`,
`arcLineDyadicTowerVector k r ν x = exp(−(log |x|)/2) · arcLineDyadicTowerProfile k r ν (log |x|)`. -/
theorem arcLineDyadicTowerVector_eq_exp_neg_half_mul_profile
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) {ν : Measure ArcParam} (hν : ν.map arcNeg = ν)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineDyadicTowerVector k r ν x =
      Real.exp (-(Real.log |x| / 2)) * arcLineDyadicTowerProfile k r ν (Real.log |x|) := by
  have habs_pos : 0 < |x| := abs_pos.mpr hx
  have heven : arcLineDyadicTowerVector k r ν x = arcLineDyadicTowerVector k r ν |x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, arcLineDyadicTowerVector_neg_of_map_arcNeg k r hν]
  rw [heven, ← exp_half_mul_arcLineDyadicTowerVector hk r ν (Real.log |x|),
    Real.exp_log habs_pos, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- For `x ≠ 0` and an `arcNeg`-symmetric measure `ν`,
`arcLineSymDyadicTowerVector k r ν x = exp(−(log |x|)/2) · arcLineSymDyadicTowerProfile k r ν (log |x|)`. -/
theorem arcLineSymDyadicTowerVector_eq_exp_neg_half_mul_profile
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) {ν : Measure ArcParam} (hν : ν.map arcNeg = ν)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineSymDyadicTowerVector k r ν x =
      Real.exp (-(Real.log |x| / 2)) * arcLineSymDyadicTowerProfile k r ν (Real.log |x|) := by
  have habs_pos : 0 < |x| := abs_pos.mpr hx
  have heven : arcLineSymDyadicTowerVector k r ν x = arcLineSymDyadicTowerVector k r ν |x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, arcLineSymDyadicTowerVector_neg_of_map_arcNeg k r hν]
  rw [heven, ← exp_half_mul_arcLineSymDyadicTowerVector hk r ν (Real.log |x|),
    Real.exp_log habs_pos, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-! ### The infinite-horizon dyadic line-model vector `arcLineInfiniteDyadicVector k ν` -/

/-- **The infinite-horizon dyadic line-model vector at integer scale `k`:**
`V_{k,∞}(x) = arcLineAtomicVector (log k) ν x − ∑'_{r=0}^∞ (1 / cosh(log(k^{2^r}))) · arcLineSymDyadicTowerVector k r ν x`. -/
def arcLineInfiniteDyadicVector (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  arcLineAtomicVector (Real.log k) ν x -
    ∑' r : ℕ, (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
      arcLineSymDyadicTowerVector k r ν x

/-- Vanishing at the origin: `arcLineInfiniteDyadicVector k ν 0 = 0`. -/
theorem arcLineInfiniteDyadicVector_zero (k : ℕ) (ν : Measure ArcParam) :
    arcLineInfiniteDyadicVector k ν 0 = 0 := by
  unfold arcLineInfiniteDyadicVector
  simp [arcLineAtomicVector_zero, arcLineSymDyadicTowerVector_zero]

/-- Even parity (`x ↦ −x`) of `arcLineInfiniteDyadicVector k ν`. -/
theorem arcLineInfiniteDyadicVector_neg_of_map_arcNeg
    (k : ℕ) {ν : Measure ArcParam} (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineInfiniteDyadicVector k ν (-x) = arcLineInfiniteDyadicVector k ν x := by
  unfold arcLineInfiniteDyadicVector
  rw [arcLineAtomicVector_neg_of_map_arcNeg (Real.log k) hν]
  congr 1
  exact tsum_congr fun r => by rw [arcLineSymDyadicTowerVector_neg_of_map_arcNeg k r hν]

/-- **Exact log-scale profile bridge for `arcLineInfiniteDyadicVector k ν` (`k ≥ 1`):**
For every `v ∈ ℝ`,
`exp(v/2) · arcLineInfiniteDyadicVector k ν (exp v) = arcLineInfiniteDyadicProfile k ν v`. -/
theorem exp_half_mul_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v) =
      arcLineInfiniteDyadicProfile k ν v := by
  unfold arcLineInfiniteDyadicVector arcLineInfiniteDyadicProfile
  rw [mul_sub, exp_half_mul_arcLineAtomicVector, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun r => by
    rw [← mul_left_comm, exp_half_mul_arcLineSymDyadicTowerVector hk r ν v]

/-- For `x ≠ 0` and an `arcNeg`-symmetric measure `ν`,
`arcLineInfiniteDyadicVector k ν x = exp(−(log |x|)/2) · arcLineInfiniteDyadicProfile k ν (log |x|)`. -/
theorem arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile
    {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam} (hν : ν.map arcNeg = ν)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineInfiniteDyadicVector k ν x =
      Real.exp (-(Real.log |x| / 2)) * arcLineInfiniteDyadicProfile k ν (Real.log |x|) := by
  have habs_pos : 0 < |x| := abs_pos.mpr hx
  have heven : arcLineInfiniteDyadicVector k ν x = arcLineInfiniteDyadicVector k ν |x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, arcLineInfiniteDyadicVector_neg_of_map_arcNeg k hν]
  rw [heven, ← exp_half_mul_arcLineInfiniteDyadicVector hk ν (Real.log |x|),
    Real.exp_log habs_pos, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- Absolute summability of the dyadic line-vector telescoping series for `k ≥ 2` and `x ∈ ℝ`. -/
theorem summable_inv_cosh_mul_arcLineSymDyadicTowerVector
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    Summable fun r : ℕ =>
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerVector k r ν x := by
  by_cases hx : x = 0
  · subst hx
    simp only [arcLineSymDyadicTowerVector_zero, mul_zero]
    exact summable_zero
  · have hk1 : 1 ≤ k := by omega
    have heq : (fun r : ℕ =>
        (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          arcLineSymDyadicTowerVector k r ν x) =
      fun r : ℕ => Real.exp (-(Real.log |x| / 2)) *
        ((1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          arcLineSymDyadicTowerProfile k r ν (Real.log |x|)) := by
      funext r
      rw [arcLineSymDyadicTowerVector_eq_exp_neg_half_mul_profile hk1 r hν hx]
      ring
    rw [heq]
    exact (summable_inv_cosh_mul_arcLineSymDyadicTowerProfile hk ν (Real.log |x|)).mul_left _

/-- **Unconditional `R → ∞` convergence of `arcLineDyadicTowerVector k R ν x` to
`arcLineInfiniteDyadicVector k ν x` (`k ≥ 2`, `x ∈ ℝ`).** -/
theorem tendsto_arcLineDyadicTowerVector_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    Tendsto (fun R : ℕ => arcLineDyadicTowerVector k R ν x)
      atTop (𝓝 (arcLineInfiniteDyadicVector k ν x)) := by
  simp_rw [arcLineDyadicTowerVector_eq_atomic_sub_sum]
  exact tendsto_const_nhds.sub
    (summable_inv_cosh_mul_arcLineSymDyadicTowerVector hk hν x).hasSum.tendsto_sum_nat

/-- **Exact `x ↦ 1/x` Mellin self-reciprocity of `arcLineInfiniteDyadicVector k ν` (`k ≥ 2`):**
For every `x ≠ 0`,
`arcLineInfiniteDyadicVector k ν (1 / x) = |x| · arcLineInfiniteDyadicVector k ν x`. -/
theorem arcLineInfiniteDyadicVector_inv
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {x : ℝ} (hx : x ≠ 0) :
    arcLineInfiniteDyadicVector k ν (1 / x) =
      |x| * arcLineInfiniteDyadicVector k ν x := by
  have hk1 : 1 ≤ k := by omega
  have h1 := tendsto_arcLineDyadicTowerVector_atTop hk hν (1 / x)
  have h2 := (tendsto_arcLineDyadicTowerVector_atTop hk hν x).const_mul |x|
  have heq : (fun R : ℕ => arcLineDyadicTowerVector k R ν (1 / x)) =
      fun R : ℕ => |x| * arcLineDyadicTowerVector k R ν x :=
    funext fun R => arcLineDyadicTowerVector_inv hk1 R ν x hx
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### Power-law decay bounds on `|x| ≥ 1` -/

/-- **Scale-independent `O(|x|^{−3/4})` decay bound on `|x| ≥ 1` (`k ≥ 2`):**
For every `k ≥ 2` and every `x ∈ ℝ` with `1 ≤ |x|`,
`|arcLineInfiniteDyadicVector k ν x| ≤ 825 · ν.real univ · |x|^{−3/4}`
(with constant completely independent of `k`). -/
theorem abs_arcLineInfiniteDyadicVector_le_rpow_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {x : ℝ} (hx : 1 ≤ |x|) :
    |arcLineInfiniteDyadicVector k ν x| ≤
      825 * ν.real univ * |x| ^ (-(3 / 4 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hxne : x ≠ 0 := abs_pos.mp habs_pos
  have hlog0 : 0 ≤ Real.log |x| := Real.log_nonneg hx
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hxne,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν (Real.log |x|)
  rw [abs_of_nonneg hlog0] at hprof
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = 825 * ν.real univ *
          (Real.exp (-(Real.log |x| / 2)) * Real.exp (-((1 / 4 : ℝ) * Real.log |x|))) := by ring
    _ = 825 * ν.real univ * Real.exp (Real.log |x| * (-(3 / 4 : ℝ))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = 825 * ν.real univ * |x| ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-- **Sub-critical `O(|x|^{−(1/2 + c)})` decay bound on `|x| ≥ 1` across `c ∈ [0, 1/2)` (`k ≥ 2`).** -/
theorem abs_arcLineInfiniteDyadicVector_le_rpow_subcritical
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2)
    {x : ℝ} (hx : 1 ≤ |x|) :
    |arcLineInfiniteDyadicVector k ν x| ≤
      (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) *
        |x| ^ (-(1 / 2 + c)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hxne : x ≠ 0 := abs_pos.mp habs_pos
  have hlog0 : 0 ≤ Real.log |x| := Real.log_nonneg hx
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hxne,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_le_exp_subcritical hk hν hc0 hc (Real.log |x|)
  rw [abs_of_nonneg hlog0] at hprof
  set A := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          (A * Real.exp (-(c * Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = A * (Real.exp (-(Real.log |x| / 2)) * Real.exp (-(c * Real.log |x|))) := by ring
    _ = A * Real.exp (Real.log |x| * (-(1 / 2 + c))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = A * |x| ^ (-(1 / 2 + c)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-! ### Multiplicative Mellin and critical-line integral identities on `(0, ∞)` -/

/-- **Exact multiplicative Mellin change of variables on `(0, ∞)` (`k ≥ 1`):**
For every `l ∈ ℝ`,
`∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx = ∫_ℝ e^{lv} · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v, Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
      Real.exp (l * v) * Real.exp (v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (Real.exp (v * (l - 1 / 2)) * arcLineInfiniteDyadicVector k ν (Real.exp v))
      = (Real.exp v * Real.exp (v * (l - 1 / 2))) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
    _ = (Real.exp (l * v) * Real.exp (v / 2)) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [hexp]
    _ = Real.exp (l * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring

/-- **Identification of the multiplicative Mellin integral of `arcLineInfiniteDyadicVector k ν`
with `arcLineInfiniteDyadicLaplaceTransform k ν l` (`k ≥ 2`, `l ∈ [0, 1/2)`).** -/
theorem setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) =
      arcLineInfiniteDyadicLaplaceTransform k ν l := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l,
    integral_exp_mul_arcLineInfiniteDyadicProfile_eq hk hν hl0 hl]

/-- **Strict interior positivity of the multiplicative Mellin integral of
`arcLineInfiniteDyadicVector k ν` across `l ∈ [0, 1/2)` (`k ≥ 2`).** -/
theorem setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 < ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l]
  exact integral_exp_mul_arcLineInfiniteDyadicProfile_pos hk hν hpd hl0 hl

/-- **Infinite-order (`O((1/2 − l)^{N+1})` for every `N ∈ ℕ`) strip-edge vanishing of the
multiplicative Mellin integral of `arcLineInfiniteDyadicVector k ν` (`k ≥ 2`).** -/
theorem abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_half
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x| ≤
      (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - l) ^ (N + 1) := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l]
  exact abs_integral_exp_mul_arcLineInfiniteDyadicProfile_le_pow_sub_half hk N hν hl0 hl

/-- **Infinite-order divided-difference vanishing as `l → (1/2)⁻` for the multiplicative Mellin
integral of `arcLineInfiniteDyadicVector k ν` (`k ≥ 2`).** -/
theorem tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / (1 / 2 - l) ^ N)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  have hk1 : 1 ≤ k := by omega
  simp_rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν]
  exact tendsto_div_pow_integral_exp_mul_arcLineInfiniteDyadicProfile_nhdsWithin hk N hν

/-- **Exact critical-line multiplicative Mellin change of variables on `(0, ∞)` (`k ≥ 1`):**
For every `τ ∈ ℝ`,
`∫_{x > 0} x^{−1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx = ∫_ℝ cos(τv) · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ v, Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * -(1 / 2 : ℝ)) = Real.exp (v / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp v * (Real.exp (v * -(1 / 2 : ℝ)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = Real.cos (τ * v) * ((Real.exp v * Real.exp (v * -(1 / 2 : ℝ))) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
    _ = Real.cos (τ * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) := by rw [hexp]

/-- **Identification of the critical-line oscillatory Mellin integral of
`arcLineInfiniteDyadicVector k ν` with `arcLineInfiniteDyadicCosTransform k ν τ` (`k ≥ 2`).** -/
theorem setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    (∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      arcLineInfiniteDyadicCosTransform k ν τ := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν τ,
    integral_cos_mul_arcLineInfiniteDyadicProfile_eq hk hν τ]

/-- **Strict critical-line positivity of the oscillatory Mellin integral of
`arcLineInfiniteDyadicVector k ν` (`k ≥ 2`).** -/
theorem setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
      arcLineInfiniteDyadicVector k ν x := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν τ]
  exact integral_cos_mul_arcLineInfiniteDyadicProfile_pos hk hν hpd τ

/-! ### Master unconditional theorem for the infinite-horizon dyadic line-model vector -/

/-- **Master unconditional theorem for the infinite-horizon dyadic line-model vector
`arcLineInfiniteDyadicVector k ν`.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, the single line-model function
`V_k = arcLineInfiniteDyadicVector k ν : ℝ → ℝ` satisfies:
1. For every `x ∈ ℝ`, `arcLineDyadicTowerVector k R ν x → V_k(x)` as `R → ∞`;
2. `V_k(0) = 0`, `V_k(−x) = V_k(x)` for all `x ∈ ℝ`, and `V_k` satisfies exact `x ↦ 1/x` Mellin
   self-reciprocity `V_k(1/x) = |x| · V_k(x)` for all `x ≠ 0`;
3. For all `|x| ≥ 1`, `|V_k(x)| ≤ 825 · ν.real univ · |x|^{−3/4}` (independently of `k`);
4. For every `τ ∈ ℝ`, its critical-line oscillatory Mellin integral on `(0, ∞)` is strictly
   positive: `0 < ∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx`;
5. For every `l ∈ [0, 1/2)`, its multiplicative Mellin integral on `(0, ∞)` is strictly positive:
   `0 < ∫_{x > 0} x^{l − 1/2} V_k(x) dx`, while vanishing to **infinite order (`O((1/2 − l)^{N+1})`
   for every `N ∈ ℕ`)** at the strip edge `l → (1/2)⁻`;
6. As `k → ∞`, simultaneously:
   - `∫_{x > 0} x^{l − 1/2} V_k(x) dx → ∫ e^{lv} arcPoissonProfile ν v > 0` for all `l ∈ [0, 1/2)`,
   - `∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx → ∫ cos(τv) arcPoissonProfile ν v > 0` for all `τ ∈ ℝ`, and
   - `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` for all `n ∈ ℕ`. -/
theorem exists_dyadic_infiniteLineVector_mellin_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ x : ℝ, Tendsto (fun R : ℕ => arcLineDyadicTowerVector k R ν x)
          atTop (𝓝 (arcLineInfiniteDyadicVector k ν x))) ∧
        arcLineInfiniteDyadicVector k ν 0 = 0 ∧
        (∀ x : ℝ, arcLineInfiniteDyadicVector k ν (-x) = arcLineInfiniteDyadicVector k ν x) ∧
        (∀ x : ℝ, x ≠ 0 →
          arcLineInfiniteDyadicVector k ν (1 / x) = |x| * arcLineInfiniteDyadicVector k ν x) ∧
        (∀ x : ℝ, 1 ≤ |x| →
          |arcLineInfiniteDyadicVector k ν x| ≤ 825 * ν.real univ * |x| ^ (-(3 / 4 : ℝ))) ∧
        (∀ τ : ℝ,
          0 < ∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
            arcLineInfiniteDyadicVector k ν x) ∧
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          0 < ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ∧
        (∀ N : ℕ, ∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x| ≤
            (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - l) ^ (N + 1)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0))) ∧
      (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x)
          atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v))) ∧
      (∀ τ : ℝ,
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
            arcLineInfiniteDyadicVector k ν x)
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
  · exact ⟨fun x => tendsto_arcLineDyadicTowerVector_atTop hk hsym x,
      arcLineInfiniteDyadicVector_zero k ν,
      fun x => arcLineInfiniteDyadicVector_neg_of_map_arcNeg k hsym x,
      fun x hx => arcLineInfiniteDyadicVector_inv hk hsym hx,
      fun x hx => abs_arcLineInfiniteDyadicVector_le_rpow_quarter_uniform hk hsym hx,
      fun τ => setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_pos hk hsym hpd τ,
      fun l hl0 hl =>
        setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos hk hsym hpd hl0 hl,
      fun N l hl0 hl =>
        abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_half hk N hsym hl0 hl,
      fun N =>
        tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin hk N hsym⟩
  · refine (tendsto_arcLineInfiniteDyadicLaplaceTransform_atTop hsym hl0 hl).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq hk hsym hl0 hl).symm
  · refine (tendsto_arcLineInfiniteDyadicCosTransform_atTop ν τ).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq hk hsym τ).symm

end

end RHTower
