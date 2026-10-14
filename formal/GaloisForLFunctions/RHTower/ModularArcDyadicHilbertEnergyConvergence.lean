import GaloisForLFunctions.RHTower.ModularArcDyadicInfiniteLineVector

/-!
# Unitary `L²((0, ∞)) ≃ L²(ℝ)` Hilbert energy isometry, near-origin `O(|x|^{−1/4})` asymptotics, and doubly-exponential `L²` convergence of the dyadic modular arc tower

In `ModularArcDyadicInfiniteLineVector`, we constructed the infinite-horizon dyadic line-model
vector `arcLineInfiniteDyadicVector k ν : ℝ → ℝ`, proved its `x ↦ 1/x` Mellin self-reciprocity and
`k`-independent `O(|x|^{−3/4})` decay on `|x| ≥ 1`, and identified its multiplicative Mellin and
critical-line oscillatory integrals on `(0, ∞)`.

In this module we establish the complete two-sided power-law envelope and the `L²((0, ∞))` Hilbert
energy theory of `arcLineInfiniteDyadicVector k ν`:

1. **Near-origin `O(|x|^{−1/4})` and sub-critical `O(|x|^{−(1/2 − c)})` power-law bounds on
   `0 < |x| ≤ 1` (`abs_arcLineInfiniteDyadicVector_le_rpow_quarter_near_zero`,
   `abs_arcLineInfiniteDyadicVector_le_rpow_subcritical_near_zero`):**
   Dual to the `|x| ≥ 1` decay `825 · ν.real univ · |x|^{−3/4}`, for all `0 < |x| ≤ 1` we have
   `|arcLineInfiniteDyadicVector k ν x| ≤ 825 · ν.real univ · |x|^{−1/4}` independently of `k ≥ 2`
   (and `O(|x|^{−(1/2 − c)})` for every `c ∈ [0, 1/2)`), where the near-zero and near-infinity
   exponents `−1/4` and `−3/4` sum to `−1` by Mellin self-reciprocity `V_k(1/x) = |x| V_k(x)`.
2. **Exact unitary `L²((0, ∞)) ≃ L²(ℝ)` logarithmic inner-product and norm isometry
   (`setIntegral_Ioi_mul_eq_integral_exp_half_mul`,
   `setIntegral_Ioi_sq_eq_integral_sq_exp_half_mul`,
   `setIntegral_Ioi_sq_arcLineDyadicTowerVector_eq`,
   `setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_eq`):**
   Under `x = exp v`, `∫_{x > 0} f(x) g(x) dx = ∫_ℝ (e^{v/2} f(e^v)) (e^{v/2} g(e^v)) dv`, so the
   `L²((0, ∞))` Hilbert energy of `arcLineInfiniteDyadicVector k ν` equals the `L²(ℝ)` energy of
   `arcLineInfiniteDyadicProfile k ν`.
3. **Strict `L²((0, ∞))` Hilbert energy positivity and depth-and-scale-uniform `475200 · (ν.real univ)²`
   upper bound (`setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos`,
   `setIntegral_Ioi_sq_arcLineDyadicTowerVector_le_uniform`,
   `setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_uniform`):**
   For every `k ≥ 2`, `0 < ∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx ≤ 475200 · (ν.real univ)²`
   independently of `k`.
4. **Doubly-exponential `O((k^{2^R})⁻¹)` `L²((0, ∞))` norm and energy convergence
   (`setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le`,
   `abs_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le`,
   `tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atTop`,
   `tendsto_setIntegral_Ioi_sq_arcLineDyadicTowerVector_atTop`,
   `tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atomic_atTop`,
   `exists_dyadic_hilbertEnergy_convergence_arcWitness`):**
   Interpolating the `O((k^{2^R})⁻¹)` uniform tail bound with the `O(exp(−|v|/4))` exponential
   envelope yields
   `∫_{x > 0} (arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k R ν x)² dx ≤ 1900800 · (ν.real univ)² / k^{2^R}`,
   establishing doubly-exponential `L²((0, ∞))` convergence as `R → ∞` and `O(k⁻¹)` asymptotic
   `L²((0, ∞))` convergence to `arcLineAtomicVector (log k) ν` as `k → ∞`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Near-origin `O(|x|^{−1/4})` and sub-critical `O(|x|^{−(1/2 − c)})` bounds on `0 < |x| ≤ 1` -/

/-- **Scale-independent `O(|x|^{−1/4})` bound near the origin (`0 < |x| ≤ 1`, `k ≥ 2`):**
For every `k ≥ 2` and every `x ∈ ℝ` with `0 < |x| ≤ 1`,
`|arcLineInfiniteDyadicVector k ν x| ≤ 825 · ν.real univ · |x|^{−1/4}`
(with constant completely independent of `k`). -/
theorem abs_arcLineInfiniteDyadicVector_le_rpow_quarter_near_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |arcLineInfiniteDyadicVector k ν x| ≤
      825 * ν.real univ * |x| ^ (-(1 / 4 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := abs_pos.mpr hx0
  have hlog_nonpos : Real.log |x| ≤ 0 := Real.log_nonpos habs_pos.le hx1
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hx0,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν (Real.log |x|)
  rw [abs_of_nonpos hlog_nonpos] at hprof
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * -Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = 825 * ν.real univ *
          (Real.exp (-(Real.log |x| / 2)) * Real.exp (-((1 / 4 : ℝ) * -Real.log |x|))) := by ring
    _ = 825 * ν.real univ * Real.exp (Real.log |x| * (-(1 / 4 : ℝ))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = 825 * ν.real univ * |x| ^ (-(1 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-- **Sub-critical `O(|x|^{−(1/2 − c)})` bound near the origin (`0 < |x| ≤ 1`) across `c ∈ [0, 1/2)` (`k ≥ 2`).** -/
theorem abs_arcLineInfiniteDyadicVector_le_rpow_subcritical_near_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |arcLineInfiniteDyadicVector k ν x| ≤
      (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) *
        |x| ^ (-(1 / 2 - c)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := abs_pos.mpr hx0
  have hlog_nonpos : Real.log |x| ≤ 0 := Real.log_nonpos habs_pos.le hx1
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hx0,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_le_exp_subcritical hk hν hc0 hc (Real.log |x|)
  rw [abs_of_nonpos hlog_nonpos] at hprof
  set A := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          (A * Real.exp (-(c * -Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = A * (Real.exp (-(Real.log |x| / 2)) * Real.exp (-(c * -Real.log |x|))) := by ring
    _ = A * Real.exp (Real.log |x| * (-(1 / 2 - c))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = A * |x| ^ (-(1 / 2 - c)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-! ### Unitary `L²((0, ∞)) ≃ L²(ℝ)` logarithmic inner-product and norm isometry -/

/-- **Unitary logarithmic inner-product identity on `(0, ∞)`:**
Under `x = exp v`, `∫_{x > 0} f(x) g(x) dx = ∫_ℝ (e^{v/2} f(e^v)) · (e^{v/2} g(e^v)) dv`. -/
theorem setIntegral_Ioi_mul_eq_integral_exp_half_mul (f g : ℝ → ℝ) :
    (∫ x in Ioi 0, f x * g x) =
      ∫ v : ℝ, (Real.exp (v / 2) * f (Real.exp v)) * (Real.exp (v / 2) * g (Real.exp v)) := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  have hexp : Real.exp v = Real.exp (v / 2) * Real.exp (v / 2) := by
    rw [← Real.exp_add, add_halves]
  calc Real.exp v * (f (Real.exp v) * g (Real.exp v))
      = (Real.exp (v / 2) * Real.exp (v / 2)) * (f (Real.exp v) * g (Real.exp v)) := by rw [hexp]
    _ = (Real.exp (v / 2) * f (Real.exp v)) * (Real.exp (v / 2) * g (Real.exp v)) := by ring

/-- **Unitary logarithmic `L²((0, ∞))` norm identity:**
Under `x = exp v`, `∫_{x > 0} (f(x))² dx = ∫_ℝ (e^{v/2} f(e^v))² dv`. -/
theorem setIntegral_Ioi_sq_eq_integral_sq_exp_half_mul (f : ℝ → ℝ) :
    (∫ x in Ioi 0, (f x) ^ 2) =
      ∫ v : ℝ, (Real.exp (v / 2) * f (Real.exp v)) ^ 2 := by
  simp_rw [sq]
  exact setIntegral_Ioi_mul_eq_integral_exp_half_mul f f

/-- Exact `L²((0, ∞)) ≃ L²(ℝ)` energy identity for `arcLineAtomicVector b ν`. -/
theorem setIntegral_Ioi_sq_arcLineAtomicVector_eq (b : ℝ) (ν : Measure ArcParam) :
    (∫ x in Ioi 0, (arcLineAtomicVector b ν x) ^ 2) =
      ∫ v : ℝ, (arcLineAtomicProfile b ν v) ^ 2 := by
  rw [setIntegral_Ioi_sq_eq_integral_sq_exp_half_mul]
  simp_rw [exp_half_mul_arcLineAtomicVector]

/-- Exact `L²((0, ∞)) ≃ L²(ℝ)` energy identity for `arcLineDyadicTowerVector k R ν` (`k ≥ 1`). -/
theorem setIntegral_Ioi_sq_arcLineDyadicTowerVector_eq
    {k : ℕ} (hk : 1 ≤ k) (R : ℕ) (ν : Measure ArcParam) :
    (∫ x in Ioi 0, (arcLineDyadicTowerVector k R ν x) ^ 2) =
      ∫ v : ℝ, (arcLineDyadicTowerProfile k R ν v) ^ 2 := by
  rw [setIntegral_Ioi_sq_eq_integral_sq_exp_half_mul]
  simp_rw [exp_half_mul_arcLineDyadicTowerVector hk R ν]

/-- Exact `L²((0, ∞)) ≃ L²(ℝ)` energy identity for `arcLineInfiniteDyadicVector k ν` (`k ≥ 1`). -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) :
    (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_sq_eq_integral_sq_exp_half_mul]
  simp_rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν]

/-- Exact `L²((0, ∞)) ≃ L²(ℝ)` difference-energy identity between `arcLineInfiniteDyadicVector k ν`
and `arcLineDyadicTowerVector k R ν` (`k ≥ 1`). -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_eq
    {k : ℕ} (hk : 1 ≤ k) (R : ℕ) (ν : Measure ArcParam) :
    (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k R ν x) ^ 2) =
      ∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v) ^ 2 := by
  rw [setIntegral_Ioi_sq_eq_integral_sq_exp_half_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [mul_sub, exp_half_mul_arcLineInfiniteDyadicVector hk ν v,
    exp_half_mul_arcLineDyadicTowerVector hk R ν v]

/-! ### `L²` integrability, depth-and-scale-uniform energy bounds, and strict Hilbert positivity -/

/-- Pointwise quadratic-exponential bound at finite dyadic depth `R`:
`(arcLineDyadicTowerProfile k R ν v)² ≤ 59400 · (ν.real univ)² · exp(−|v|/4)` (`k ≥ 2`). -/
theorem sq_arcLineDyadicTowerProfile_le_exp_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    (arcLineDyadicTowerProfile k R ν v) ^ 2 ≤
      59400 * (ν.real univ) ^ 2 * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have h1 := abs_arcLineDyadicTowerProfile_le_uniform hk R ν v
  have h2 := abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc (arcLineDyadicTowerProfile k R ν v) ^ 2
      = |arcLineDyadicTowerProfile k R ν v| * |arcLineDyadicTowerProfile k R ν v| := by
        rw [← sq, sq_abs]
    _ ≤ (72 * ν.real univ) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 59400 * (ν.real univ) ^ 2 * Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring

/-- Pointwise quadratic-exponential bound for `arcLineInfiniteDyadicProfile k ν`:
`(arcLineInfiniteDyadicProfile k ν v)² ≤ 59400 · (ν.real univ)² · exp(−|v|/4)` (`k ≥ 2`). -/
theorem sq_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    (arcLineInfiniteDyadicProfile k ν v) ^ 2 ≤
      59400 * (ν.real univ) ^ 2 * Real.exp (-((1 / 4 : ℝ) * |v|)) :=
  le_of_tendsto
    ((continuous_pow 2).tendsto _ |>.comp (tendsto_arcLineDyadicTowerProfile_atTop hk ν v))
    (Eventually.of_forall fun R =>
      sq_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v)

/-- Integrability of `(arcLineDyadicTowerProfile k R ν v)²` on `ℝ` (`k ≥ 2`). -/
theorem integrable_sq_arcLineDyadicTowerProfile
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Integrable (fun v : ℝ => (arcLineDyadicTowerProfile k R ν v) ^ 2) := by
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (59400 * (ν.real univ) ^ 2)).mono'
    ((continuous_arcLineDyadicTowerProfile k R ν).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v

/-- Integrability of `(arcLineInfiniteDyadicProfile k ν v)²` on `ℝ` (`k ≥ 2`). -/
theorem integrable_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Integrable (fun v : ℝ => (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (59400 * (ν.real univ) ^ 2)).mono'
    ((continuous_arcLineInfiniteDyadicProfile hk ν).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v

/-- **Depth-and-scale-uniform `L²(ℝ)` energy bound for `arcLineDyadicTowerProfile k R ν` (`k ≥ 2`):**
`∫_ℝ (arcLineDyadicTowerProfile k R ν v)² dv ≤ 475200 · (ν.real univ)²`
(completely independent of both `k ≥ 2` and `R ∈ ℕ`). -/
theorem integral_sq_arcLineDyadicTowerProfile_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ v : ℝ, (arcLineDyadicTowerProfile k R ν v) ^ 2) ≤
      475200 * (ν.real univ) ^ 2 := by
  have hmono := integral_mono (integrable_sq_arcLineDyadicTowerProfile hk R hν)
    ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (59400 * (ν.real univ) ^ 2))
    (fun v => sq_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v)
  rw [integral_const_mul, integral_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)] at hmono
  linarith

/-- **Scale-independent `L²(ℝ)` energy bound for `arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`):**
`∫_ℝ (arcLineInfiniteDyadicProfile k ν v)² dv ≤ 475200 · (ν.real univ)²`
(completely independent of `k ≥ 2`). -/
theorem integral_sq_arcLineInfiniteDyadicProfile_le_uniform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      475200 * (ν.real univ) ^ 2 := by
  have hmono := integral_mono (integrable_sq_arcLineInfiniteDyadicProfile hk hν)
    ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (59400 * (ν.real univ) ^ 2))
    (fun v => sq_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v)
  rw [integral_const_mul, integral_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)] at hmono
  linarith

/-- **Depth-and-scale-uniform `L²((0, ∞))` energy bound for `arcLineDyadicTowerVector k R ν` (`k ≥ 2`):**
`∫_{x > 0} (arcLineDyadicTowerVector k R ν x)² dx ≤ 475200 · (ν.real univ)²`. -/
theorem setIntegral_Ioi_sq_arcLineDyadicTowerVector_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ x in Ioi 0, (arcLineDyadicTowerVector k R ν x) ^ 2) ≤
      475200 * (ν.real univ) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_sq_arcLineDyadicTowerVector_eq hk1 R ν]
  exact integral_sq_arcLineDyadicTowerProfile_le_uniform hk R hν

/-- **Scale-independent `L²((0, ∞))` energy bound for `arcLineInfiniteDyadicVector k ν` (`k ≥ 2`):**
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx ≤ 475200 · (ν.real univ)²`. -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_uniform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
      475200 * (ν.real univ) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq hk1 ν]
  exact integral_sq_arcLineInfiniteDyadicProfile_le_uniform hk hν

/-- **Strict `L²(ℝ)` energy positivity for `arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`).** -/
theorem integral_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    0 < ∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hnn : 0 ≤ᵐ[volume] fun v : ℝ => (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
    Eventually.of_forall fun v => sq_nonneg _
  have hint_nn : 0 ≤ ∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
    integral_nonneg fun v => sq_nonneg _
  rcases hint_nn.eq_or_lt with hzero | hlt
  · exfalso
    have hae : (fun v : ℝ => (arcLineInfiniteDyadicProfile k ν v) ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn
        (integrable_sq_arcLineInfiniteDyadicProfile hk hν)).mp hzero.symm
    have hfae : (fun v : ℝ => Real.cos (0 * v) * arcLineInfiniteDyadicProfile k ν v) =ᵐ[volume] 0 := by
      filter_upwards [hae] with v hv
      have hv0 : arcLineInfiniteDyadicProfile k ν v = 0 := sq_eq_zero_iff.mp hv
      simp [hv0]
    have hpos := integral_cos_mul_arcLineInfiniteDyadicProfile_pos hk hν hpd 0
    have hf0 : (∫ v : ℝ, Real.cos (0 * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
      rw [integral_congr_ae hfae]
      simp
    linarith
  · exact hlt

/-- **Strict `L²((0, ∞))` Hilbert energy positivity for `arcLineInfiniteDyadicVector k ν` (`k ≥ 2`).** -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    0 < ∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq hk1 ν]
  exact integral_sq_arcLineInfiniteDyadicProfile_pos hk hν hpd

/-! ### Doubly-exponential `O((k^{2^R})⁻¹)` `L²` norm and energy convergence -/

/-- Pointwise quadratic-exponential tail bound between `arcLineInfiniteDyadicProfile k ν` and
`arcLineDyadicTowerProfile k R ν` (`k ≥ 2`, `R ∈ ℕ`):
`(arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k R ν v)² ≤ (475200 · (ν.real univ)² / k^{2^R}) · exp(−|v|/4)`. -/
theorem sq_arcLineInfiniteDyadicProfile_sub_le
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v) ^ 2 ≤
      (475200 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have htail := abs_arcLineInfiniteDyadicProfile_sub_le hk R ν v
  have h1 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  have h2 := abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v
  have hsum_exp : |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v| ≤
      (1650 * ν.real univ) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have htri := abs_sub (arcLineInfiniteDyadicProfile k ν v) (arcLineDyadicTowerProfile k R ν v)
    linarith
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v) ^ 2
      = |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v| *
          |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v| := by
        rw [← sq, sq_abs]
    _ ≤ (288 * ν.real univ * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) *
          ((1650 * ν.real univ) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul htail hsum_exp (abs_nonneg _) (by positivity)
    _ = (475200 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) *
          Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring

/-- Pointwise difference-of-squares tail bound (`k ≥ 2`, `R ∈ ℕ`):
`|(arcLineInfiniteDyadicProfile k ν v)² − (arcLineDyadicTowerProfile k R ν v)²| ≤ (475200 · (ν.real univ)² / k^{2^R}) · exp(−|v|/4)`. -/
theorem abs_sq_arcLineInfiniteDyadicProfile_sub_le
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |(arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcLineDyadicTowerProfile k R ν v) ^ 2| ≤
      (475200 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have htail := abs_arcLineInfiniteDyadicProfile_sub_le hk R ν v
  have h1 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  have h2 := abs_arcLineDyadicTowerProfile_le_exp_quarter_uniform hk R hν v
  have hadd_exp : |arcLineInfiniteDyadicProfile k ν v + arcLineDyadicTowerProfile k R ν v| ≤
      (1650 * ν.real univ) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have htri := abs_add_le (arcLineInfiniteDyadicProfile k ν v) (arcLineDyadicTowerProfile k R ν v)
    linarith
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcLineDyadicTowerProfile k R ν v) ^ 2|
      = |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v| *
          |arcLineInfiniteDyadicProfile k ν v + arcLineDyadicTowerProfile k R ν v| := by
        rw [sq_sub_sq, abs_mul, mul_comm]
    _ ≤ (288 * ν.real univ * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) *
          ((1650 * ν.real univ) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul htail hadd_exp (abs_nonneg _) (by positivity)
    _ = (475200 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) *
          Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring

/-- Integrability of `(arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k R ν v)²` on `ℝ` (`k ≥ 2`). -/
theorem integrable_sq_arcLineInfiniteDyadicProfile_sub
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Integrable (fun v : ℝ =>
      (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v) ^ 2) := by
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (475200 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹)).mono'
    (((continuous_arcLineInfiniteDyadicProfile hk ν).sub
      (continuous_arcLineDyadicTowerProfile k R ν)).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_arcLineInfiniteDyadicProfile_sub_le hk R hν v

/-- **Doubly-exponential `O((k^{2^R})⁻¹)` `L²(ℝ)` tail bound for `arcLineInfiniteDyadicProfile k ν` (`k ≥ 2`):**
`∫_ℝ (arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k R ν v)² dv ≤ 3801600 · (ν.real univ)² · (k^{2^R})⁻¹`. -/
theorem integral_sq_arcLineInfiniteDyadicProfile_sub_le
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v) ^ 2) ≤
      3801600 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹ := by
  have hmono := integral_mono (integrable_sq_arcLineInfiniteDyadicProfile_sub hk R hν)
    ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (475200 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹))
    (fun v => sq_arcLineInfiniteDyadicProfile_sub_le hk R hν v)
  rw [integral_const_mul, integral_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)] at hmono
  linarith

/-- **Doubly-exponential `O((k^{2^R})⁻¹)` `L²((0, ∞))` Hilbert norm tail bound (`k ≥ 2`):**
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k R ν x)² dx ≤ 3801600 · (ν.real univ)² · (k^{2^R})⁻¹`. -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ x in Ioi 0,
        (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k R ν x) ^ 2) ≤
      3801600 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹ := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_eq hk1 R ν]
  exact integral_sq_arcLineInfiniteDyadicProfile_sub_le hk R hν

/-- **Doubly-exponential `O((k^{2^R})⁻¹)` `L²((0, ∞))` energy tail bound (`k ≥ 2`):**
`|∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx − ∫_{x > 0} (arcLineDyadicTowerVector k R ν x)² dx| ≤ 3801600 · (ν.real univ)² · (k^{2^R})⁻¹`. -/
theorem abs_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    |(∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi 0, (arcLineDyadicTowerVector k R ν x) ^ 2)| ≤
      3801600 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹ := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq hk1 ν,
    setIntegral_Ioi_sq_arcLineDyadicTowerVector_eq hk1 R ν,
    ← integral_sub (integrable_sq_arcLineInfiniteDyadicProfile hk hν)
      (integrable_sq_arcLineDyadicTowerProfile hk R hν)]
  have h1 := abs_integral_le_integral_abs
    (μ := volume)
    (f := fun v : ℝ => (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
      (arcLineDyadicTowerProfile k R ν v) ^ 2)
  have h2 := integral_mono
    (((integrable_sq_arcLineInfiniteDyadicProfile hk hν).sub
      (integrable_sq_arcLineDyadicTowerProfile hk R hν)).abs)
    ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (475200 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹))
    (fun v => abs_sq_arcLineInfiniteDyadicProfile_sub_le hk R hν v)
  dsimp only [Pi.sub_apply] at h2
  rw [integral_const_mul, integral_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)] at h2
  linarith

/-- Helper: `((k^{2^R} : ℕ) : ℝ)⁻¹ → 0` as `R → ∞` for `k ≥ 2`. -/
theorem tendsto_inv_pow_two_pow_depth_atTop {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun R : ℕ => (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
  have hpow : Tendsto (fun R : ℕ => (1 / 2 : ℝ) ^ R) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  refine squeeze_zero (fun R => by positivity) (fun R => ?_) hpow
  have hdom_nat : 2 ^ R ≤ k ^ (2 ^ R) := by
    calc 2 ^ R
        ≤ k * 2 ^ R := Nat.le_mul_of_pos_left _ (by omega)
      _ = k ^ (2 ^ 0) * 2 ^ R := by simp
      _ ≤ k ^ (2 ^ (0 + R)) := pow_two_pow_mul_two_pow_le hk 0 R
      _ = k ^ (2 ^ R) := by simp
  have hdom : (2 : ℝ) ^ R ≤ ((k ^ (2 ^ R) : ℕ) : ℝ) := by exact_mod_cast hdom_nat
  calc (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹
      ≤ ((2 : ℝ) ^ R)⁻¹ := inv_anti₀ (by positivity) hdom
    _ = (1 / 2 : ℝ) ^ R := by rw [one_div, inv_pow]

/-- **Unconditional `L²((0, ∞))` norm convergence (`R → ∞`, `k ≥ 2`):**
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k R ν x)² dx → 0` as `R → ∞`. -/
theorem tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun R : ℕ =>
      ∫ x in Ioi 0,
        (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k R ν x) ^ 2)
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun R : ℕ => 3801600 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    rw [← mul_zero (3801600 * (ν.real univ) ^ 2)]
    exact (tendsto_inv_pow_two_pow_depth_atTop hk).const_mul _
  exact squeeze_zero
    (fun R => setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _)
    (fun R => setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le hk R hν)
    hbound

/-- **Unconditional `L²((0, ∞))` Hilbert energy convergence (`R → ∞`, `k ≥ 2`):**
`∫_{x > 0} (arcLineDyadicTowerVector k R ν x)² dx → ∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx` as `R → ∞`. -/
theorem tendsto_setIntegral_Ioi_sq_arcLineDyadicTowerVector_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun R : ℕ => ∫ x in Ioi 0, (arcLineDyadicTowerVector k R ν x) ^ 2)
      atTop (𝓝 (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  have hbound : Tendsto
      (fun R : ℕ => 3801600 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    rw [← mul_zero (3801600 * (ν.real univ) ^ 2)]
    exact (tendsto_inv_pow_two_pow_depth_atTop hk).const_mul _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun R => norm_nonneg _) (fun R => ?_) hbound
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le hk R hν

/-- **Quantitative `O(k⁻¹)` `L²((0, ∞))` distance to the single-step atomic vector `arcLineAtomicVector (log k) ν` (`k ≥ 2`):**
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x − arcLineAtomicVector (log k) ν x)² dx ≤ 3801600 · (ν.real univ)² · k⁻¹`. -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atomic_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ x in Ioi 0,
        (arcLineInfiniteDyadicVector k ν x - arcLineAtomicVector (Real.log k) ν x) ^ 2) ≤
      3801600 * (ν.real univ) ^ 2 * (k : ℝ)⁻¹ := by
  simpa [arcLineDyadicTowerVector] using
    setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le hk 0 hν

/-- **Asymptotic `k → ∞` `L²((0, ∞))` convergence of `arcLineInfiniteDyadicVector k ν` to
`arcLineAtomicVector (log k) ν`.** -/
theorem tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atomic_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Tendsto (fun k : ℕ =>
      ∫ x in Ioi 0,
        (arcLineInfiniteDyadicVector k ν x - arcLineAtomicVector (Real.log k) ν x) ^ 2)
      atTop (𝓝 0) := by
  have hbound : Tendsto (fun k : ℕ => 3801600 * (ν.real univ) ^ 2 * (k : ℝ)⁻¹) atTop (𝓝 0) := by
    rw [← mul_zero (3801600 * (ν.real univ) ^ 2)]
    exact (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _
  refine squeeze_zero'
    (Eventually.of_forall fun k => setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _)
    ?_ hbound
  filter_upwards [eventually_ge_atTop 2] with k hk
  exact setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atomic_le hk hν

/-! ### Master unconditional theorem for the `L²((0, ∞))` Hilbert energy of the infinite-horizon dyadic witness -/

/-- **Master unconditional theorem for the two-sided power-law envelope and `L²((0, ∞))` Hilbert
energy convergence of `arcLineInfiniteDyadicVector k ν`.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, the single line-model vector
`V_k = arcLineInfiniteDyadicVector k ν : ℝ → ℝ` satisfies:
1. Near-origin `O(|x|^{−1/4})` bound: for all `0 < |x| ≤ 1`,
   `|V_k(x)| ≤ 825 · ν.real univ · |x|^{−1/4}` (independently of `k`);
2. Near-infinity `O(|x|^{−3/4})` bound: for all `|x| ≥ 1`,
   `|V_k(x)| ≤ 825 · ν.real univ · |x|^{−3/4}` (independently of `k`);
3. Exact unitary `L²((0, ∞)) ≃ L²(ℝ)` energy identity:
   `∫_{x > 0} (V_k(x))² dx = ∫_ℝ (arcLineInfiniteDyadicProfile k ν v)² dv`;
4. Strict `L²((0, ∞))` energy positivity and `k`-independent upper bound:
   `0 < ∫_{x > 0} (V_k(x))² dx ≤ 475200 · (ν.real univ)²`;
5. Doubly-exponential `O((k^{2^R})⁻¹)` `L²((0, ∞))` norm and energy convergence across all dyadic
   depths `R ∈ ℕ`:
   `∫_{x > 0} (V_k(x) − arcLineDyadicTowerVector k R ν x)² dx ≤ 3801600 · (ν.real univ)² · (k^{2^R})⁻¹`
   and `∫_{x > 0} (arcLineDyadicTowerVector k R ν x)² dx → ∫_{x > 0} (V_k(x))² dx` as `R → ∞`;
6. As `k → ∞`, simultaneously:
   - `∫_{x > 0} (V_k(x) − arcLineAtomicVector (log k) ν x)² dx → 0` (at rate `O(k⁻¹)`),
   - `∫_{x > 0} x^{l − 1/2} V_k(x) dx → ∫ e^{lv} arcPoissonProfile ν v > 0` for all `l ∈ [0, 1/2)`,
   - `∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx → ∫ cos(τv) arcPoissonProfile ν v > 0` for all `τ ∈ ℝ`, and
   - `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` for all `n ∈ ℕ`. -/
theorem exists_dyadic_hilbertEnergy_convergence_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ x : ℝ, x ≠ 0 → |x| ≤ 1 →
          |arcLineInfiniteDyadicVector k ν x| ≤ 825 * ν.real univ * |x| ^ (-(1 / 4 : ℝ))) ∧
        (∀ x : ℝ, 1 ≤ |x| →
          |arcLineInfiniteDyadicVector k ν x| ≤ 825 * ν.real univ * |x| ^ (-(3 / 4 : ℝ))) ∧
        (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) =
          (∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        0 < (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤ 475200 * (ν.real univ) ^ 2 ∧
        (∀ R : ℕ,
          (∫ x in Ioi 0,
              (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k R ν x) ^ 2) ≤
            3801600 * (ν.real univ) ^ 2 * (((k ^ (2 ^ R) : ℕ) : ℝ))⁻¹) ∧
        Tendsto (fun R : ℕ =>
          ∫ x in Ioi 0,
            (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k R ν x) ^ 2)
          atTop (𝓝 0) ∧
        Tendsto (fun R : ℕ => ∫ x in Ioi 0, (arcLineDyadicTowerVector k R ν x) ^ 2)
          atTop (𝓝 (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2)) ∧
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          0 < ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0))) ∧
      Tendsto (fun k : ℕ =>
        ∫ x in Ioi 0,
          (arcLineInfiniteDyadicVector k ν x - arcLineAtomicVector (Real.log k) ν x) ^ 2)
        atTop (𝓝 0) ∧
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
    tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atomic_atTop hsym,
    fun l hl0 hl => ?_,
    fun τ => ?_,
    tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop hblind⟩
  · have hk1 : 1 ≤ k := by omega
    exact ⟨fun x hx0 hx1 => abs_arcLineInfiniteDyadicVector_le_rpow_quarter_near_zero hk hsym hx0 hx1,
      fun x hx => abs_arcLineInfiniteDyadicVector_le_rpow_quarter_uniform hk hsym hx,
      setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq hk1 ν,
      setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hsym hpd,
      setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_uniform hk hsym,
      fun R => setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_le hk R hsym,
      tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atTop hk hsym,
      tendsto_setIntegral_Ioi_sq_arcLineDyadicTowerVector_atTop hk hsym,
      fun l hl0 hl =>
        setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos hk hsym hpd hl0 hl,
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
