import GaloisForLFunctions.RHTower.ModularArcDyadicJointExponentialTail

/-!
# Strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy, the Critical-Line Minimum Principle across `|l| < 1/2`, and squared/cubic doubly-exponential `L²` tail laws

In `ModularArcDyadicHilbertEnergyConvergence`, we established the unweighted (`l = 0`) unitary
isometry `L²((0, ∞), dx) ≃ L²(ℝ, dv)` for `arcLineInfiniteDyadicVector k ν` and proved an
`O((k^{2^R})⁻¹)` `L²` tail bound by interpolating the `L^∞` tail bound with the depth-uniform
`O(exp(−|v|/4))` spatial envelope.

In this module we combine the full-strip reflection theory of
`ModularArcDyadicFullStripFunctionalSymmetry` with the joint exponential-doubly-exponential tail
bound of `ModularArcDyadicJointExponentialTail` to establish:

1. **Strip-weighted `L²((0, ∞), x^{2l} dx) ≃ L²(ℝ, e^{2lv} dv)` logarithmic isometry and `l ↦ −l`
   functional-equation reflection symmetry (`setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq`,
   `setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_rpow_two_neg_mul_sq_arcLineInfiniteDyadicVector`):**
   Under `x = exp v`, for every `l ∈ ℝ`,
   `∫_{x > 0} x^{2l} (V_k(x))² dx = ∫_ℝ e^{2lv} (Φ_k(v))² dv = ∫_{x > 0} x^{−2l} (V_k(x))² dx`.
2. **Full critical-strip (`|l| < 1/2`) `cosh(2lv)` representation and the Critical-Line Minimum
   Principle (`integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile`,
   `integral_exp_two_mul_sq_arcLineInfiniteDyadicProfile_eq_cosh`,
   `setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul`,
   `setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos`):**
   Across the entire open critical strip `l ∈ (−1/2, 1/2)` (`|l| < 1/2`), `e^{2lv} (Φ_k(v))²` is
   integrable on `ℝ`,
   `∫_{x > 0} x^{2l} (V_k(x))² dx = ∫_ℝ cosh(2lv) (Φ_k(v))² dv`,
   and because `1 ≤ cosh(2lv)` pointwise, the **critical line `l = 0` (`Re(s) = 1/2`) is the global
   minimum of the strip-weighted `L²` Hilbert energy across `|l| < 1/2`**:
   `0 < ∫_{x > 0} (V_k(x))² dx ≤ ∫_{x > 0} x^{2l} (V_k(x))² dx`.
3. **Doubled spatial decay `O(exp(−|v|/2))`, scale-independent strip-weighted `L²` upper bound on
   `|l| < 1/4`, and squared/cubic doubly-exponential `L²` tail bounds
   (`sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform`,
   `setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_le_quarter`,
   `sq_arcLineInfiniteDyadicProfile_sub_succ_le_exp_half`,
   `setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_succ_le`,
   `setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_succ_le_cubic`,
   `exists_dyadic_stripWeighted_hilbertMinimum_arcWitness`):**
   - Squaring the joint exponential tail bound yields `(Φ_k(v) − Φ_{k, r₀+1}(v))² ≤ 10890000 · (ν.real univ)² · (k^{2^{r₀+1}})⁻¹ · exp(−|v|/2)`,
     giving the strip-weighted `L²` tail bound `∫_{x > 0} x^{2l} (V_k(x) − V_{k, r₀+1}(x))² dx ≤ (10890000 · (ν.real univ)² / (1/4 − |l|)) · (k^{2^{r₀+1}})⁻¹` for all `|l| < 1/4`.
   - Interpolating the `L^∞` tail at `r₀ + 1` (`O((k^{2^{r₀}})⁻²)`) with the joint exponential tail
     at `r₀ + 1` (`O((k^{2^{r₀}})⁻¹ exp(−|v|/4))`) upgrades the unweighted `L²((0, ∞))` tail to
     **cubic doubly-exponential decay**:
     `∫_{x > 0} (V_k(x) − V_{k, r₀+1}(x))² dx ≤ 7603200 · (ν.real univ)² · ((k^{2^{r₀}})⁻¹)³`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Strip-weighted `L²((0, ∞), x^{2l} dx) ≃ L²(ℝ, e^{2lv} dv)` isometry and `l ↦ −l` symmetry -/

/-- **Strip-weighted logarithmic `L²((0, ∞), x^{2l} dx)` norm identity:**
Under `x = exp v`, for every `l ∈ ℝ` and `f : ℝ → ℝ`,
`∫_{x > 0} x^{2l} · (f(x))² dx = ∫_ℝ e^{2lv} · (e^{v/2} f(e^v))² dv`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq
    (f : ℝ → ℝ) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (2 * l) * (f x) ^ 2) =
      ∫ v : ℝ, Real.exp (2 * l * v) * (Real.exp (v / 2) * f (Real.exp v)) ^ 2 := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]
  have hexp : Real.exp v * Real.exp (v * (2 * l)) =
      Real.exp (2 * l * v) * (Real.exp (v / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp v * (Real.exp (v * (2 * l)) * (f (Real.exp v)) ^ 2)
      = (Real.exp v * Real.exp (v * (2 * l))) * (f (Real.exp v)) ^ 2 := by ring
    _ = (Real.exp (2 * l * v) * (Real.exp (v / 2)) ^ 2) * (f (Real.exp v)) ^ 2 := by rw [hexp]
    _ = Real.exp (2 * l * v) * (Real.exp (v / 2) * f (Real.exp v)) ^ 2 := by ring

/-- Exact strip-weighted `L²((0, ∞), x^{2l} dx) ≃ L²(ℝ, e^{2lv} dv)` identity for
`arcLineDyadicTowerVector k R ν` (`k ≥ 1`). -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineDyadicTowerVector_eq
    {k : ℕ} (hk : 1 ≤ k) (R : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (2 * l) * (arcLineDyadicTowerVector k R ν x) ^ 2) =
      ∫ v : ℝ, Real.exp (2 * l * v) * (arcLineDyadicTowerProfile k R ν v) ^ 2 := by
  rw [setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq]
  simp_rw [exp_half_mul_arcLineDyadicTowerVector hk R ν]

/-- Exact strip-weighted `L²((0, ∞), x^{2l} dx) ≃ L²(ℝ, e^{2lv} dv)` identity for
`arcLineInfiniteDyadicVector k ν` (`k ≥ 1`). -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq]
  simp_rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν]

/-- Exact strip-weighted `L²((0, ∞), x^{2l} dx) ≃ L²(ℝ, e^{2lv} dv)` difference-energy identity
between `arcLineInfiniteDyadicVector k ν` and `arcLineDyadicTowerVector k R ν` (`k ≥ 1`). -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_eq
    {k : ℕ} (hk : 1 ≤ k) (R : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0,
        x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k R ν x) ^ 2) =
      ∫ v : ℝ,
        Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k R ν v) ^ 2 := by
  rw [setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [mul_sub, exp_half_mul_arcLineInfiniteDyadicVector hk ν v,
    exp_half_mul_arcLineDyadicTowerVector hk R ν v]

/-- **Functional-equation reflection `l ↦ −l` for the strip-weighted `L²(ℝ)` energy of
`arcLineInfiniteDyadicProfile k ν`:**
For every `l ∈ ℝ`,
`∫_ℝ e^{2(−l)v} · (arcLineInfiniteDyadicProfile k ν v)² dv = ∫_ℝ e^{2lv} · (arcLineInfiniteDyadicProfile k ν v)² dv`. -/
theorem integral_exp_two_neg_mul_sq_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ v : ℝ, Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have h := integral_neg_eq_self
    (fun v : ℝ => Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) volume
  simpa [mul_neg, neg_mul, arcLineInfiniteDyadicProfile_neg] using h

/-- **Functional-equation reflection `l ↦ −l` for the strip-weighted `L²((0, ∞), x^{2l} dx)`
Hilbert energy of `arcLineInfiniteDyadicVector k ν` (`k ≥ 1`):**
For every `l ∈ ℝ`,
`∫_{x > 0} x^{2(−l)} (arcLineInfiniteDyadicVector k ν x)² dx = ∫_{x > 0} x^{2l} (arcLineInfiniteDyadicVector k ν x)² dx`. -/
theorem setIntegral_Ioi_rpow_two_neg_mul_sq_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (2 * (-l)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk ν (-l),
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk ν l,
    integral_exp_two_neg_mul_sq_arcLineInfiniteDyadicProfile]

/-- **Absolute-value reduction `l ↦ |l|` for the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert
energy of `arcLineInfiniteDyadicVector k ν` (`k ≥ 1`).** -/
theorem setIntegral_Ioi_rpow_two_abs_mul_sq_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (2 * |l|) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl]
  · rw [abs_of_nonpos hl, setIntegral_Ioi_rpow_two_neg_mul_sq_arcLineInfiniteDyadicVector hk ν l]

/-! ### Full critical-strip (`|l| < 1/2`) integrability, `cosh(2lv)` representation, and the Critical-Line Minimum Principle -/

/-- **Sub-critical quadratic-exponential bound across `c ∈ [0, 1/2)` (`k ≥ 2`):**
For every `c ∈ [0, 1/2)` and `v ∈ ℝ`,
`(arcLineInfiniteDyadicProfile k ν v)² ≤ (25 · ν.real univ · (1 + 16 / ((1 − 2c)² (log k)²)))² · exp(−2c|v|)`. -/
theorem sq_arcLineInfiniteDyadicProfile_le_exp_two_mul_subcritical
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) (v : ℝ) :
    (arcLineInfiniteDyadicProfile k ν v) ^ 2 ≤
      (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) ^ 2 *
        Real.exp (-((2 * c) * |v|)) := by
  have h := abs_arcLineInfiniteDyadicProfile_le_exp_subcritical hk hν hc0 hc v
  calc (arcLineInfiniteDyadicProfile k ν v) ^ 2
      = |arcLineInfiniteDyadicProfile k ν v| * |arcLineInfiniteDyadicProfile k ν v| := by
        rw [← sq, sq_abs]
    _ ≤ ((25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) *
          Real.exp (-(c * |v|))) *
        ((25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) *
          Real.exp (-(c * |v|))) :=
        mul_le_mul h h (abs_nonneg _) (le_trans (abs_nonneg _) h)
    _ = (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) ^ 2 *
          (Real.exp (-(c * |v|)) * Real.exp (-(c * |v|))) := by ring
    _ = (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) ^ 2 *
          Real.exp (-((2 * c) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Integrability of `e^{2lv} · (arcLineInfiniteDyadicProfile k ν v)²` across the entire open
critical strip `|l| < 1/2` (`k ≥ 2`).** -/
theorem integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    Integrable (fun v : ℝ => Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  set c := (1 / 2 + |l|) / 2
  have hc0 : 0 ≤ c := by
    have := abs_nonneg l
    dsimp [c]; linarith
  have hc : c < 1 / 2 := by dsimp [c]; linarith
  have hcl : 0 < 1 / 2 - |l| := sub_pos.mpr hl
  set A := (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))) ^ 2
  refine ((integrable_rexp_neg_mul_abs hcl).const_mul A).mono'
    (((continuous_const.mul continuous_id).rexp).mul
      ((continuous_arcLineInfiniteDyadicProfile hk ν).pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hnn : 0 ≤ Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hexp : Real.exp (2 * l * v) ≤ Real.exp ((2 * |l|) * |v|) := by
    have h1 := abs_exp_mul_le_exp_abs_mul (2 * l) v
    rw [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
    simpa [mul_assoc] using h1
  have hsq := sq_arcLineInfiniteDyadicProfile_le_exp_two_mul_subcritical hk hν hc0 hc v
  calc Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2
      ≤ Real.exp ((2 * |l|) * |v|) * (A * Real.exp (-((2 * c) * |v|))) :=
        mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le
    _ = A * (Real.exp ((2 * |l|) * |v|) * Real.exp (-((2 * c) * |v|))) := by ring
    _ = A * Real.exp (-((1 / 2 - |l|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; dsimp [c]; ring

/-- **Exact `cosh(2lv)` representation of the strip-weighted `L²(ℝ)` energy across the entire open
critical strip `|l| < 1/2` (`k ≥ 2`):**
`∫_ℝ e^{2lv} · (arcLineInfiniteDyadicProfile k ν v)² dv = ∫_ℝ cosh(2lv) · (arcLineInfiniteDyadicProfile k ν v)² dv`. -/
theorem integral_exp_two_mul_sq_arcLineInfiniteDyadicProfile_eq_cosh
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∫ v : ℝ, Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hIl : Integrable (fun v : ℝ =>
      Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) :=
    integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl
  have hIneg : Integrable (fun v : ℝ =>
      Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    have heq : (fun v : ℝ => Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; congr 2; ring
    rw [heq]
    exact integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν (by simpa using hl)
  have hneg_eq : (∫ v : ℝ, Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
    have heq : (fun v : ℝ => Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; congr 2; ring
    rw [heq, integral_exp_two_neg_mul_sq_arcLineInfiniteDyadicProfile]
  have e : (fun v : ℝ => Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ => (1 / 2 : ℝ) *
        (Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          Real.exp (-(2 * l * v)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    funext v; rw [Real.cosh_eq]; ring
  rw [e, integral_const_mul, integral_add hIl hIneg, hneg_eq]
  ring

/-- **Critical-Line Minimum Principle on the logarithmic axis `v ∈ ℝ` (`|l| < 1/2`, `k ≥ 2`):**
For every `l ∈ (−1/2, 1/2)`,
`∫_ℝ (arcLineInfiniteDyadicProfile k ν v)² dv ≤ ∫_ℝ e^{2lv} · (arcLineInfiniteDyadicProfile k ν v)² dv`. -/
theorem integral_sq_arcLineInfiniteDyadicProfile_le_exp_two_mul
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      ∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [integral_exp_two_mul_sq_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl]
  have hIcosh : Integrable (fun v : ℝ =>
      Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    have e : (fun v : ℝ => Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => (1 / 2 : ℝ) *
          (Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      funext v; rw [Real.cosh_eq, show -(2 * l * v) = 2 * (-l) * v by ring]; ring
    rw [e]
    exact ((integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl).add
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν (by simpa using hl))).const_mul _
  refine integral_mono (integrable_sq_arcLineInfiniteDyadicProfile hk hν) hIcosh fun v => ?_
  calc (arcLineInfiniteDyadicProfile k ν v) ^ 2
      = 1 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := (one_mul _).symm
    _ ≤ Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.one_le_cosh _) (sq_nonneg _)

/-- **Critical-Line Minimum Principle for the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy
across the entire open critical strip `l ∈ (−1/2, 1/2)` (`|l| < 1/2`, `k ≥ 2`):**
The critical line `l = 0` (`Re(s) = 1/2`) minimizes the strip-weighted `L²` Hilbert energy of
`arcLineInfiniteDyadicVector k ν`:
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx ≤ ∫_{x > 0} x^{2l} · (arcLineInfiniteDyadicVector k ν x)² dx`. -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
      ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq hk1 ν,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l]
  exact integral_sq_arcLineInfiniteDyadicProfile_le_exp_two_mul hk hν hl

/-- **Strict positivity of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy across the
entire open critical strip `|l| < 1/2` (`k ≥ 2`).** -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    0 < ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 :=
  lt_of_lt_of_le (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd)
    (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul hk hν hl)

/-! ### Doubled spatial decay `O(exp(−|v|/2))`, scale-independent strip-weighted `L²` bound on `|l| < 1/4`, and squared/cubic doubly-exponential `L²` tail bounds -/

/-- **Doubled-rate quadratic-exponential bound (`k ≥ 2`):**
Squaring `|arcLineInfiniteDyadicProfile k ν v| ≤ 825 · ν.real univ · exp(−|v|/4)` yields
`(arcLineInfiniteDyadicProfile k ν v)² ≤ 680625 · (ν.real univ)² · exp(−|v|/2)`
with twice the exponential decay rate (`1/2` vs `1/4`). -/
theorem sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    (arcLineInfiniteDyadicProfile k ν v) ^ 2 ≤
      680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
  have h := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc (arcLineInfiniteDyadicProfile k ν v) ^ 2
      = |arcLineInfiniteDyadicProfile k ν v| * |arcLineInfiniteDyadicProfile k ν v| := by
        rw [← sq, sq_abs]
    _ ≤ (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul h h (abs_nonneg _) (by positivity)
    _ = 680625 * (ν.real univ) ^ 2 *
          (Real.exp (-((1 / 4 : ℝ) * |v|)) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ = 680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Scale-independent strip-weighted `L²((0, ∞), x^{2l} dx)` upper bound across `|l| < 1/4` (`k ≥ 2`):**
For every `|l| < 1/4`,
`∫_{x > 0} x^{2l} · (arcLineInfiniteDyadicVector k ν x)² dx ≤ 680625 · (ν.real univ)² / (1/4 − |l|)`
(completely independent of `k ≥ 2`). -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_le_quarter
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 4) :
    (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
      680625 * (ν.real univ) ^ 2 / (1 / 4 - |l|) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith
  have hcl : 0 < 1 / 2 - 2 * |l| := by linarith
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l]
  have hmono := integral_mono
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_half)
    ((integrable_rexp_neg_mul_abs hcl).const_mul (680625 * (ν.real univ) ^ 2))
    (fun v => ?_)
  · rw [integral_const_mul, integral_rexp_neg_mul_abs hcl] at hmono
    have h2div : 2 / (1 / 2 - 2 * |l|) = 1 / (1 / 4 - |l|) := by
      have hne1 : 1 / 2 - 2 * |l| ≠ 0 := ne_of_gt hcl
      have hne2 : 1 / 4 - |l| ≠ 0 := ne_of_gt (sub_pos.mpr hl)
      rw [div_eq_div_iff hne1 hne2]
      ring
    calc (∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
        ≤ 680625 * (ν.real univ) ^ 2 * (2 / (1 / 2 - 2 * |l|)) := hmono
      _ = 680625 * (ν.real univ) ^ 2 / (1 / 4 - |l|) := by
          rw [h2div]; ring
  · have hexp : Real.exp (2 * l * v) ≤ Real.exp ((2 * |l|) * |v|) := by
      have h1 := abs_exp_mul_le_exp_abs_mul (2 * l) v
      rw [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
      simpa [mul_assoc] using h1
    calc Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2
        ≤ Real.exp ((2 * |l|) * |v|) *
            (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul hexp (sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v)
            (sq_nonneg _) (Real.exp_pos _).le
      _ = 680625 * (ν.real univ) ^ 2 *
            (Real.exp ((2 * |l|) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
      _ = 680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-- **Squared doubly-exponential `O((k^{2^{r₀+1}})⁻¹ · exp(−|v|/2))` quadratic profile tail bound (`k ≥ 2`):**
Squaring `abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter` and using
`((k^{2^{r₀}})⁻¹)² = (k^{2^{r₀+1}})⁻¹` gives
`(arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k (r₀ + 1) ν v)² ≤ 10890000 · (ν.real univ)² · (k^{2^{r₀+1}})⁻¹ · exp(−|v|/2)`. -/
theorem sq_arcLineInfiniteDyadicProfile_sub_succ_le_exp_half
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2 ≤
      10890000 * (ν.real univ) ^ 2 * (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹) *
        Real.exp (-((1 / 2 : ℝ) * |v|)) := by
  have h := abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk r₀ hν v
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hsq_scale : (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) =
      (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹) := by
    rw [← mul_inv, ← sq]
    congr 1
    exact_mod_cast pow_two_pow_sq k r₀
  calc (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2
      = |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v| *
          |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v| := by
        rw [← sq, sq_abs]
    _ ≤ (3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * Real.exp (-((1 / 4 : ℝ) * |v|))) *
          (3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul h h (abs_nonneg _) (by positivity)
    _ = 10890000 * (ν.real univ) ^ 2 *
          ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) *
          (Real.exp (-((1 / 4 : ℝ) * |v|)) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ = 10890000 * (ν.real univ) ^ 2 * (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹) *
          Real.exp (-((1 / 2 : ℝ) * |v|)) := by
        rw [hsq_scale, ← Real.exp_add]; congr 2; ring

/-- **Strip-weighted `L²((0, ∞), x^{2l} dx)` doubly-exponential tail bound across `|l| < 1/4` (`k ≥ 2`):**
For every `r₀ ∈ ℕ` and `|l| < 1/4`,
`∫_{x > 0} x^{2l} (arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x)² dx ≤ (10890000 · (ν.real univ)² / (1/4 − |l|)) · (k^{2^{r₀+1}})⁻¹`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_succ_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 4) :
    (∫ x in Ioi 0,
        x ^ (2 * l) *
          (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x) ^ 2) ≤
      (10890000 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
        (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹) := by
  have hk1 : 1 ≤ k := by omega
  have hcl : 0 < 1 / 2 - 2 * |l| := by linarith
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_eq hk1 (r₀ + 1) ν l]
  set B := 10890000 * (ν.real univ) ^ 2 * (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹)
  have hpoint : ∀ v : ℝ,
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2 ≤
      B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := fun v => by
    have hexp : Real.exp (2 * l * v) ≤ Real.exp ((2 * |l|) * |v|) := by
      have h1 := abs_exp_mul_le_exp_abs_mul (2 * l) v
      rw [abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
      simpa [mul_assoc] using h1
    calc Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2
        ≤ Real.exp ((2 * |l|) * |v|) * (B * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul hexp (sq_arcLineInfiniteDyadicProfile_sub_succ_le_exp_half hk r₀ hν v)
            (sq_nonneg _) (Real.exp_pos _).le
      _ = B * (Real.exp ((2 * |l|) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
      _ = B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring
  have hInt : Integrable (fun v : ℝ =>
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2) := by
    refine ((integrable_rexp_neg_mul_abs hcl).const_mul B).mono'
      (((continuous_const.mul continuous_id).rexp).mul
        (((continuous_arcLineInfiniteDyadicProfile hk ν).sub
          (continuous_arcLineDyadicTowerProfile k (r₀ + 1) ν)).pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hpoint v
  have hmono := integral_mono hInt
    ((integrable_rexp_neg_mul_abs hcl).const_mul B) hpoint
  rw [integral_const_mul, integral_rexp_neg_mul_abs hcl] at hmono
  have h2div : 2 / (1 / 2 - 2 * |l|) = 1 / (1 / 4 - |l|) := by
    have hne1 : 1 / 2 - 2 * |l| ≠ 0 := ne_of_gt hcl
    have hne2 : 1 / 4 - |l| ≠ 0 := ne_of_gt (sub_pos.mpr hl)
    rw [div_eq_div_iff hne1 hne2]
    ring
  calc (∫ v : ℝ,
        Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2)
      ≤ B * (2 / (1 / 2 - 2 * |l|)) := hmono
    _ = (10890000 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
          (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹) := by
        rw [h2div]; dsimp [B]; ring

/-- **Cubic doubly-exponential `O(((k^{2^{r₀}})⁻¹)³ · exp(−|v|/4))` pointwise quadratic tail bound (`k ≥ 2`):**
Interpolating the `L^∞` tail at `r₀ + 1` (`≤ 288 · ν.real univ · ((k^{2^{r₀}})⁻¹)²`) with the joint
exponential tail at `r₀ + 1` (`≤ 3300 · ν.real univ · (k^{2^{r₀}})⁻¹ · exp(−|v|/4)`) yields
`(arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k (r₀ + 1) ν v)² ≤ 950400 · (ν.real univ)² · ((k^{2^{r₀}})⁻¹)³ · exp(−|v|/4)`. -/
theorem sq_arcLineInfiniteDyadicProfile_sub_succ_le_cubic_exp_quarter
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2 ≤
      950400 * (ν.real univ) ^ 2 * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ^ 3) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have h1 := abs_arcLineInfiniteDyadicProfile_sub_le hk (r₀ + 1) ν v
  have h2 := abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk r₀ hν v
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hsq_scale : (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹) = (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ^ 2 := by
    rw [inv_pow]
    congr 1
    exact_mod_cast (pow_two_pow_sq k r₀).symm
  rw [hsq_scale] at h1
  calc (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) ^ 2
      = |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v| *
          |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v| := by
        rw [← sq, sq_abs]
    _ ≤ (288 * ν.real univ * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ^ 2)) *
          (3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
            Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 950400 * (ν.real univ) ^ 2 * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ^ 3) *
          Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring

/-- **Cubic doubly-exponential `O(((k^{2^{r₀}})⁻¹)³)` `L²((0, ∞))` Hilbert norm tail bound (`k ≥ 2`):**
For every `r₀ ∈ ℕ`,
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x − arcLineDyadicTowerVector k (r₀ + 1) ν x)² dx ≤ 7603200 · (ν.real univ)² · ((k^{2^{r₀}})⁻¹)³`. -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_succ_le_cubic
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ x in Ioi 0,
        (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x) ^ 2) ≤
      7603200 * (ν.real univ) ^ 2 * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ^ 3) := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_eq hk1 (r₀ + 1) ν]
  have hmono := integral_mono
    (integrable_sq_arcLineInfiniteDyadicProfile_sub hk (r₀ + 1) hν)
    ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (950400 * (ν.real univ) ^ 2 * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ^ 3)))
    (fun v => sq_arcLineInfiniteDyadicProfile_sub_succ_le_cubic_exp_quarter hk r₀ hν v)
  rw [integral_const_mul, integral_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)] at hmono
  linarith

/-! ### Master unconditional theorem for the strip-weighted `L²` Critical-Line Minimum Principle and cubic `L²` tail laws -/

/-- **Master unconditional theorem for the strip-weighted `L²((0, ∞), x^{2l} dx)` Critical-Line
Minimum Principle and squared/cubic doubly-exponential `L²` tail laws.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, the single line-model vector
`V_k = arcLineInfiniteDyadicVector k ν : ℝ → ℝ` satisfies:
1. Functional-equation reflection symmetry of the strip-weighted `L²` Hilbert energy (`l ∈ ℝ`):
   `∫_{x > 0} x^{2(−l)} (V_k(x))² dx = ∫_{x > 0} x^{2l} (V_k(x))² dx`;
2. Critical-Line Minimum Principle across the entire open critical strip `l ∈ (−1/2, 1/2)` (`|l| < 1/2`):
   `0 < ∫_{x > 0} (V_k(x))² dx ≤ ∫_{x > 0} x^{2l} (V_k(x))² dx`;
3. Scale-independent strip-weighted `L²` upper bound across `|l| < 1/4`:
   `∫_{x > 0} x^{2l} (V_k(x))² dx ≤ 680625 · (ν.real univ)² / (1/4 − |l|)`;
4. Strip-weighted doubly-exponential `L²` tail bound across `(|l| < 1/4, r₀ ∈ ℕ)`:
   `∫_{x > 0} x^{2l} (V_k(x) − V_{k, r₀+1}(x))² dx ≤ (10890000 · (ν.real univ)² / (1/4 − |l|)) · (k^{2^{r₀+1}})⁻¹`;
5. Cubic doubly-exponential unweighted `L²((0, ∞))` tail bound (`r₀ ∈ ℕ`):
   `∫_{x > 0} (V_k(x) − V_{k, r₀+1}(x))² dx ≤ 7603200 · (ν.real univ)² · ((k^{2^{r₀}})⁻¹)³`;
6. Full critical-strip (`|l| < 1/2`) strict Mellin positivity, two-sided infinite-order strip-edge
   vanishing (`l → (1/2)⁻` and `l → (−1/2)⁺`), and `k → ∞` convergence across the strip, critical
   line, `L²((0, ∞))` norm, and all integer frequencies `arcFreq n`. -/
theorem exists_dyadic_stripWeighted_hilbertMinimum_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ l : ℝ,
          (∫ x in Ioi 0, x ^ (2 * (-l)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
            ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ l : ℝ, |l| < 1 / 2 →
          0 < (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
          (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
            ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ l : ℝ, |l| < 1 / 4 →
          (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
            680625 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) ∧
        (∀ r₀ : ℕ, ∀ l : ℝ, |l| < 1 / 4 →
          (∫ x in Ioi 0,
              x ^ (2 * l) *
                (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x) ^ 2) ≤
            (10890000 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
              (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹)) ∧
        (∀ r₀ : ℕ,
          (∫ x in Ioi 0,
              (arcLineInfiniteDyadicVector k ν x - arcLineDyadicTowerVector k (r₀ + 1) ν x) ^ 2) ≤
            7603200 * (ν.real univ) ^ 2 * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ^ 3)) ∧
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
  · have hk1 : 1 ≤ k := by omega
    exact ⟨fun l => setIntegral_Ioi_rpow_two_neg_mul_sq_arcLineInfiniteDyadicVector hk1 ν l,
      fun l hl => ⟨setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hsym hpd,
        setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul hk hsym hl⟩,
      fun l hl => setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_le_quarter hk hsym hl,
      fun r₀ l hl =>
        setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_succ_le hk r₀ hsym hl,
      fun r₀ => setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_succ_le_cubic hk r₀ hsym,
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
