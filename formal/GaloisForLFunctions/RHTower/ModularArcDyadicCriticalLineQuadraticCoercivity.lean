import GaloisForLFunctions.RHTower.ModularArcDyadicOriginInfinityTransversality

/-!
# Global quadratic coercivity on `(−1/2, 1/2)`, cubic `O(|l|³)` Taylor remainder, exact critical-line curvature limit, and the Cauchy–Schwarz moment inequality for the infinite-horizon dyadic Hilbert energy

In `ModularArcDyadicCriticalLineStrictConvexity`, we proved the quadratic upper bound
`E_k(l) − E_k(0) ≤ (87120000 · (ν.real univ)² / (1/8 − |l|)) · l²` (`|l| < 1/8`) and the vanishing
first-order stationary derivative `(E_k(l) − E_k(0)) / l → 0` as `l → 0`.

In this module we complete the second-order Taylor theory of the strip-weighted Hilbert energy
`E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx` at the critical line `l = 0` (`Re(s) = 1/2`):

1. **Elementary hyperbolic sine quadratic coercivity and cubic remainder bounds
   (`sq_le_sinh_sq`, `two_mul_sq_le_two_mul_sinh_sq`, `sinh_sq_le_sq_mul_exp_two_abs`,
   `exp_two_abs_sub_one_le`, `two_mul_sinh_sq_sub_sq_le`,
   `two_mul_sinh_sq_sub_sq_mul_le_exp`):**
   - For all `u ∈ ℝ`, `u² ≤ (sinh u)² ≤ u² exp(2|u|)` and
     `0 ≤ 2 (sinh u)² − 2 u² ≤ 4 |u|³ exp(2|u|)`.
   - For all `l, v ∈ ℝ`,
     `0 ≤ 2 (sinh(lv))² − 2 l² v² ≤ 6912 · |l|³ · exp((2|l| + 1/4)|v|)`.
2. **Integrability, `(0, 1]`/`(1, ∞)` equipartition, and strict positivity of the second
   logarithmic energy moment (`integrable_sq_mul_sq_arcLineInfiniteDyadicProfile`,
   `setIntegral_Ioi_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_zero_sq_mul_sq_arcLineInfiniteDyadicProfile_pos`,
   `integral_sq_mul_sq_arcLineInfiniteDyadicProfile_pos`):**
   - `∫_{x > 0} (log x)² (V_k(x))² dx = ∫_ℝ v² (Φ_k(v))² dv = 2 ∫_{v > 0} v² (Φ_k(v))² dv > 0`.
3. **Global quadratic coercivity across `|l| < 1/2`, cubic `O(|l|³)` Taylor remainder on
   `|l| < 1/8`, and exact critical-line curvature limit as `l → 0`
   (`two_mul_sq_mul_integral_sq_mul_sq_le_excess`,
   `excess_sub_two_mul_sq_le_cubic`,
   `tendsto_div_sq_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero`):**
   - Across the entire open critical strip `|l| < 1/2`,
     `2 l² ∫_ℝ v² (Φ_k(v))² dv ≤ ∫_{x > 0} x^{2l} (V_k(x))² dx − ∫_{x > 0} (V_k(x))² dx`.
   - For `|l| < 1/8`,
     `0 ≤ (E_k(l) − E_k(0)) − 2 l² ∫_ℝ v² (Φ_k(v))² dv ≤ (4704480000 · (ν.real univ)² / (1/8 − |l|)) · |l|³`.
   - Consequently, as `l → 0` (`l ≠ 0`),
     `(E_k(l) − E_k(0)) / l² → 2 ∫_ℝ v² (Φ_k(v))² dv = 2 ∫_{x > 0} (log x)² (V_k(x))² dx > 0`.
4. **Cauchy–Schwarz logarithmic moment inequality (`sq_setIntegral_Ioi_zero_mul_sq_le`,
   `exists_dyadic_criticalLine_quadraticCoercivity_arcWitness`):**
   `(∫_{v > 0} v (Φ_k(v))² dv)² ≤ (∫_{v > 0} (Φ_k(v))² dv) · (∫_{v > 0} v² (Φ_k(v))² dv)`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Elementary hyperbolic sine quadratic coercivity and cubic Taylor remainder bounds -/

/-- **Quadratic lower bound for `sinh`:** for every `u ∈ ℝ`, `u² ≤ (sinh u)²`. -/
theorem sq_le_sinh_sq (u : ℝ) : u ^ 2 ≤ (Real.sinh u) ^ 2 := by
  rw [sq_le_sq, Real.abs_sinh]
  exact Real.self_le_sinh_iff.mpr (abs_nonneg u)

/-- Pointwise quadratic lower bound `2 l² v² ≤ 2 (sinh(lv))²` for all `l, v ∈ ℝ`. -/
theorem two_mul_sq_le_two_mul_sinh_sq (l v : ℝ) :
    2 * l ^ 2 * v ^ 2 ≤ 2 * (Real.sinh (l * v)) ^ 2 := by
  calc 2 * l ^ 2 * v ^ 2
      = 2 * (l * v) ^ 2 := by ring
    _ ≤ 2 * (Real.sinh (l * v)) ^ 2 :=
        mul_le_mul_of_nonneg_left (sq_le_sinh_sq (l * v)) (by norm_num)

/-- Pointwise quadratic-exponential upper bound `(sinh u)² ≤ u² exp(2|u|)` for all `u ∈ ℝ`. -/
theorem sinh_sq_le_sq_mul_exp_two_abs (u : ℝ) :
    (Real.sinh u) ^ 2 ≤ u ^ 2 * Real.exp (2 * |u|) := by
  have h := abs_sinh_le_abs_mul_exp_abs u
  calc (Real.sinh u) ^ 2
      = |Real.sinh u| * |Real.sinh u| := by rw [← sq, sq_abs]
    _ ≤ (|u| * Real.exp |u|) * (|u| * Real.exp |u|) :=
        mul_le_mul h h (abs_nonneg _) (by positivity)
    _ = u ^ 2 * (Real.exp |u| * Real.exp |u|) := by
        have hu : |u| * |u| = u ^ 2 := by rw [← sq, sq_abs]
        linear_combination (Real.exp |u| * Real.exp |u|) * hu
    _ = u ^ 2 * Real.exp (2 * |u|) := by
        rw [← Real.exp_add]; congr 2; ring

/-- Elementary bound `exp(2|u|) − 1 ≤ 2 |u| exp(2|u|)` for all `u ∈ ℝ`. -/
theorem exp_two_abs_sub_one_le (u : ℝ) :
    Real.exp (2 * |u|) - 1 ≤ 2 * |u| * Real.exp (2 * |u|) := by
  have h1 : -(2 * |u|) + 1 ≤ Real.exp (-(2 * |u|)) := Real.add_one_le_exp (-(2 * |u|))
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (2 * |u|)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  linarith

/-- **Cubic Taylor remainder bound for `2 (sinh u)²`:**
For every `u ∈ ℝ`, `2 (sinh u)² − 2 u² ≤ 4 |u|³ exp(2|u|)`. -/
theorem two_mul_sinh_sq_sub_sq_le (u : ℝ) :
    2 * (Real.sinh u) ^ 2 - 2 * u ^ 2 ≤ 4 * |u| ^ 3 * Real.exp (2 * |u|) := by
  have h1 := sinh_sq_le_sq_mul_exp_two_abs u
  have h2 := exp_two_abs_sub_one_le u
  have hu3 : u ^ 2 * |u| = |u| ^ 3 := by
    rw [← sq_abs u]; ring
  calc 2 * (Real.sinh u) ^ 2 - 2 * u ^ 2
      ≤ 2 * (u ^ 2 * Real.exp (2 * |u|)) - 2 * u ^ 2 := by linarith
    _ = 2 * u ^ 2 * (Real.exp (2 * |u|) - 1) := by ring
    _ ≤ 2 * u ^ 2 * (2 * |u| * Real.exp (2 * |u|)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 * (u ^ 2 * |u|) * Real.exp (2 * |u|) := by ring
    _ = 4 * |u| ^ 3 * Real.exp (2 * |u|) := by rw [hu3]

/-- Specialization of `abs_le_inv_mul_exp_mul` at `c = 1/12`:
`|v| ≤ 12 · exp((1/12) |v|)`. -/
theorem abs_le_twelve_mul_exp_twelfth (v : ℝ) :
    |v| ≤ 12 * Real.exp ((1 / 12 : ℝ) * |v|) := by
  have h := abs_le_inv_mul_exp_mul (by norm_num : (0 : ℝ) < 1 / 12) v
  linarith

/-- Cubic-by-exponential domination `|v|³ ≤ 1728 · exp((1/4) |v|)` for all `v ∈ ℝ`. -/
theorem abs_cube_le_exp_quarter (v : ℝ) :
    |v| ^ 3 ≤ 1728 * Real.exp ((1 / 4 : ℝ) * |v|) := by
  have hv := abs_le_twelve_mul_exp_twelfth v
  have hv2 : |v| ^ 2 ≤ 144 * Real.exp ((1 / 6 : ℝ) * |v|) := by
    calc |v| ^ 2
        = |v| * |v| := sq |v|
      _ ≤ (12 * Real.exp ((1 / 12 : ℝ) * |v|)) * (12 * Real.exp ((1 / 12 : ℝ) * |v|)) :=
          mul_le_mul hv hv (abs_nonneg v) (by positivity)
      _ = 144 * (Real.exp ((1 / 12 : ℝ) * |v|) * Real.exp ((1 / 12 : ℝ) * |v|)) := by ring
      _ = 144 * Real.exp ((1 / 6 : ℝ) * |v|) := by rw [← Real.exp_add]; congr 2; ring
  calc |v| ^ 3
      = |v| ^ 2 * |v| := by ring
    _ ≤ (144 * Real.exp ((1 / 6 : ℝ) * |v|)) * (12 * Real.exp ((1 / 12 : ℝ) * |v|)) :=
        mul_le_mul hv2 hv (abs_nonneg v) (by positivity)
    _ = 1728 * (Real.exp ((1 / 6 : ℝ) * |v|) * Real.exp ((1 / 12 : ℝ) * |v|)) := by ring
    _ = 1728 * Real.exp ((1 / 4 : ℝ) * |v|) := by rw [← Real.exp_add]; congr 2; ring

/-- **Pointwise cubic-exponential bound on `2 (sinh(lv))² − 2 l² v²`:**
For all `l, v ∈ ℝ`,
`2 (sinh(l v))² − 2 l² v² ≤ 6912 · |l|³ · exp((2 |l| + 1/4) |v|)`. -/
theorem two_mul_sinh_sq_sub_sq_mul_le_exp (l v : ℝ) :
    2 * (Real.sinh (l * v)) ^ 2 - 2 * l ^ 2 * v ^ 2 ≤
      6912 * |l| ^ 3 * Real.exp ((2 * |l| + 1 / 4) * |v|) := by
  have h1 := two_mul_sinh_sq_sub_sq_le (l * v)
  have hrew : 2 * (l * v) ^ 2 = 2 * l ^ 2 * v ^ 2 := by ring
  rw [hrew, abs_mul, mul_pow] at h1
  have hv3 := abs_cube_le_exp_quarter v
  calc 2 * (Real.sinh (l * v)) ^ 2 - 2 * l ^ 2 * v ^ 2
      ≤ 4 * (|l| ^ 3 * |v| ^ 3) * Real.exp (2 * (|l| * |v|)) := h1
    _ = 4 * |l| ^ 3 * |v| ^ 3 * Real.exp (2 * (|l| * |v|)) := by ring
    _ ≤ 4 * |l| ^ 3 * (1728 * Real.exp ((1 / 4 : ℝ) * |v|)) * Real.exp (2 * (|l| * |v|)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hv3 (by positivity)) (by positivity)
    _ = 6912 * |l| ^ 3 * (Real.exp ((1 / 4 : ℝ) * |v|) * Real.exp (2 * (|l| * |v|))) := by ring
    _ = 6912 * |l| ^ 3 * Real.exp ((2 * |l| + 1 / 4) * |v|) := by
        rw [← Real.exp_add]; congr 2; ring

/-! ### Integrability, `(0, 1]`/`(1, ∞)` equipartition, and strict positivity of the second logarithmic energy moment -/

/-- Integrability of `v ↦ v² · (arcLineInfiniteDyadicProfile k ν v)²` on `ℝ` (`k ≥ 2`). -/
theorem integrable_sq_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Integrable (fun v : ℝ => v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  set B := 64 * (680625 * (ν.real univ) ^ 2)
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul B).mono'
    ((continuous_id.pow 2).mul
      ((continuous_arcLineInfiniteDyadicProfile hk ν).pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hnn : 0 ≤ v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
    mul_nonneg (sq_nonneg v) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hv8 := abs_le_eight_mul_exp_eighth v
  have hv_sq : v ^ 2 ≤ 64 * Real.exp ((1 / 4 : ℝ) * |v|) := by
    calc v ^ 2
        = |v| * |v| := by rw [← sq, sq_abs]
      _ ≤ (8 * Real.exp ((1 / 8 : ℝ) * |v|)) * (8 * Real.exp ((1 / 8 : ℝ) * |v|)) :=
          mul_le_mul hv8 hv8 (abs_nonneg v) (by positivity)
      _ = 64 * (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp ((1 / 8 : ℝ) * |v|)) := by ring
      _ = 64 * Real.exp ((1 / 4 : ℝ) * |v|) := by rw [← Real.exp_add]; congr 2; ring
  calc v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2
      ≤ (64 * Real.exp ((1 / 4 : ℝ) * |v|)) *
          (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
        mul_le_mul hv_sq (sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v)
          (sq_nonneg _) (by positivity)
    _ = B * (Real.exp ((1 / 4 : ℝ) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by
        dsimp [B]; ring
    _ = B * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Logarithmic second-moment identity on `(0, ∞)` (`k ≥ 1`):**
`∫_{x > 0} (log x)² (V_k(x))² dx = ∫_ℝ v² (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) :
    (∫ x in Ioi (0 : ℝ), (Real.log x) ^ 2 * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.log_exp, ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (v ^ 2 * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2)
      = v ^ 2 * (Real.exp v * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
    _ = v ^ 2 * ((Real.exp (v / 2)) ^ 2 * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by
        rw [hexp]
    _ = v ^ 2 * (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2 := by ring

/-- **Infinity-sector (`x > 1`) logarithmic second-moment identity (`k ≥ 1`):**
`∫_{x > 1} (log x)² (V_k(x))² dx = ∫_{v > 0} v² (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_one_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) :
    (∫ x in Ioi (1 : ℝ), (Real.log x) ^ 2 * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.log_exp, ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (v ^ 2 * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2)
      = v ^ 2 * (Real.exp v * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
    _ = v ^ 2 * ((Real.exp (v / 2)) ^ 2 * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by
        rw [hexp]
    _ = v ^ 2 * (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2 := by ring

/-- **Origin-sector (`x ∈ (0, 1]`) logarithmic second-moment identity (`k ≥ 1`):**
`∫_{x ∈ (0, 1]} (log x)² (V_k(x))² dx = ∫_{v > 0} v² (Φ_k(v))² dv`. -/
theorem setIntegral_Ioc_zero_one_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) :
    (∫ x in Ioc (0 : ℝ) 1, (Real.log x) ^ 2 * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.log_exp, neg_sq]
  have hprof : Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v)) =
      arcLineInfiniteDyadicProfile k ν v := by
    rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν (-v), arcLineInfiniteDyadicProfile_neg]
  have hexp : Real.exp (-v) = (Real.exp ((-v) / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc Real.exp (-v) * (v ^ 2 * (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2)
      = v ^ 2 * (Real.exp (-v) * (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2) := by ring
    _ = v ^ 2 * ((Real.exp ((-v) / 2)) ^ 2 *
          (arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2) := by rw [hexp]
    _ = v ^ 2 * (Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v))) ^ 2 := by
        ring
    _ = v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by rw [hprof]

/-- **Half-line second logarithmic energy moment identity (`k ≥ 2`):**
`∫_ℝ v² (Φ_k(v))² dv = 2 ∫_{v > 0} v² (Φ_k(v))² dv`. -/
theorem integral_sq_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_setIntegral_Ioi
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      2 * ∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hg : IntegrableOn
      (fun x : ℝ => (Real.log x) ^ 2 * (arcLineInfiniteDyadicVector k ν x) ^ 2)
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_iff_integrable_exp_mul]
    refine (integrable_sq_mul_sq_arcLineInfiniteDyadicProfile hk hν).congr
      (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.log_exp, ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v = (Real.exp (v / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc v ^ 2 * (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2
        = v ^ 2 * ((Real.exp (v / 2)) ^ 2 * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by
          ring
      _ = v ^ 2 * (Real.exp v * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by
          rw [← hexp]
      _ = Real.exp v * (v ^ 2 * (arcLineInfiniteDyadicVector k ν (Real.exp v)) ^ 2) := by ring
  have hsum := setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one hg
  rw [setIntegral_Ioc_zero_one_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν,
    setIntegral_Ioi_one_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν,
    setIntegral_Ioi_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν] at hsum
  linarith

/-- **Strict positivity of the half-line second logarithmic energy moment
`∫_{v > 0} v² (Φ_k(v))² dv > 0` (`k ≥ 2`).** -/
theorem setIntegral_Ioi_zero_sq_mul_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    0 < ∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
  setIntegral_Ioi_pos_of_pos_mul
    (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn
    (integrable_sq_mul_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn
    (fun _ _ => sq_nonneg _)
    (fun _ hv => sq_pos_of_pos hv)
    (setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos)

/-- **Strict positivity of the full second logarithmic energy moment
`∫_ℝ v² (Φ_k(v))² dv > 0` (`k ≥ 2`).** -/
theorem integral_sq_mul_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    0 < ∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  rw [integral_sq_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_setIntegral_Ioi hk hν]
  exact mul_pos (by norm_num)
    (setIntegral_Ioi_zero_sq_mul_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos)

/-! ### Global quadratic coercivity across `|l| < 1/2`, cubic `O(|l|³)` Taylor remainder, and exact critical-line curvature limit -/

/-- **Global quadratic coercivity (strong convexity) of the strip-weighted Hilbert energy across the
entire open critical strip `|l| < 1/2` (`k ≥ 2`):**
For every `l ∈ (−1/2, 1/2)`,
`2 l² ∫_ℝ v² (Φ_k(v))² dv ≤ ∫_{x > 0} x^{2l} (V_k(x))² dx − ∫_{x > 0} (V_k(x))² dx`. -/
theorem two_mul_sq_mul_integral_sq_mul_sq_le_excess
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
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
    ((integrable_sq_mul_sq_arcLineInfiniteDyadicProfile hk hν).const_mul (2 * l ^ 2))
    hInt fun v => ?_
  calc 2 * l ^ 2 * (v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      = (2 * l ^ 2 * v ^ 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by ring
    _ ≤ (2 * (Real.sinh (l * v)) ^ 2) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
        mul_le_mul_of_nonneg_right (two_mul_sq_le_two_mul_sinh_sq l v) (sq_nonneg _)

/-- **Scale-independent cubic `O(|l|³)` Taylor remainder bound for the critical-line quadratic
expansion (`|l| < 1/8`, `k ≥ 2`):**
`0 ≤ (E_k(l) − E_k(0)) − 2 l² ∫_ℝ v² (Φ_k(v))² dv ≤ (4704480000 · (ν.real univ)² / (1/8 − |l|)) · |l|³`. -/
theorem excess_sub_two_mul_sq_le_cubic
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
      2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (4704480000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * |l| ^ 3 := by
  have hl_half : |l| < 1 / 2 := by linarith
  have hcl : 0 < 1 / 4 - 2 * |l| := by linarith
  have hInt_sinh : Integrable (fun v : ℝ =>
      2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    have heq : (fun v : ℝ =>
        2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ =>
          (1 / 2 : ℝ) * (Real.exp (l * v) - Real.exp ((-l) * v)) ^ 2 *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; rw [two_mul_sq_sinh_eq_half_sq_exp_sub]
    rw [heq]
    exact integrable_half_sq_exp_sub_exp_mul_sq_arcLineInfiniteDyadicProfile
      hk hν hl_half (by simpa using hl_half)
  have hInt_quad : Integrable (fun v : ℝ =>
      2 * l ^ 2 * (v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) :=
    (integrable_sq_mul_sq_arcLineInfiniteDyadicProfile hk hν).const_mul (2 * l ^ 2)
  rw [setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_eq hk hν hl_half,
    ← integral_const_mul, ← integral_sub hInt_sinh hInt_quad]
  set B := 4704480000 * (ν.real univ) ^ 2 * |l| ^ 3
  have hmono := integral_mono (hInt_sinh.sub hInt_quad)
    ((integrable_rexp_neg_mul_abs hcl).const_mul B)
    (fun v => ?_)
  · rw [integral_const_mul, integral_rexp_neg_mul_abs hcl] at hmono
    have h2div : 2 / (1 / 4 - 2 * |l|) = 1 / (1 / 8 - |l|) := by
      have hne1 : 1 / 4 - 2 * |l| ≠ 0 := ne_of_gt hcl
      have hne2 : 1 / 8 - |l| ≠ 0 := ne_of_gt (sub_pos.mpr hl)
      rw [div_eq_div_iff hne1 hne2]
      ring
    calc (∫ v : ℝ,
          2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
            2 * l ^ 2 * (v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
        ≤ B * (2 / (1 / 4 - 2 * |l|)) := hmono
      _ = (4704480000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * |l| ^ 3 := by
          rw [h2div]; dsimp [B]; ring
  · dsimp only
    calc 2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
          2 * l ^ 2 * (v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
        = (2 * (Real.sinh (l * v)) ^ 2 - 2 * l ^ 2 * v ^ 2) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by ring
      _ ≤ (6912 * |l| ^ 3 * Real.exp ((2 * |l| + 1 / 4) * |v|)) *
            (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul (two_mul_sinh_sq_sub_sq_mul_le_exp l v)
            (sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v)
            (sq_nonneg _) (by positivity)
      _ = B * (Real.exp ((2 * |l| + 1 / 4) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 4 - 2 * |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-- **Exact second-order critical-line curvature limit (`k ≥ 2`):**
`((∫_{x > 0} x^{2l} V_k(x)² dx) − (∫_{x > 0} V_k(x)² dx)) / l² → 2 ∫_ℝ v² (Φ_k(v))² dv > 0`
as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_sq_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l ^ 2)
      (𝓝[≠] 0)
      (𝓝 (2 * ∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hupper : Tendsto (fun l : ℝ =>
      (4704480000 * (ν.real univ) ^ 2 / (1 / 16 : ℝ)) * |l|) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : (0 : ℝ) = (4704480000 * (ν.real univ) ^ 2 / (1 / 16 : ℝ)) * |(0 : ℝ)| := by simp
    have hcont : Tendsto (fun l : ℝ =>
        (4704480000 * (ν.real univ) ^ 2 / (1 / 16 : ℝ)) * |l|) (𝓝 0) (𝓝 0) := by
      nth_rw 2 [h0]
      exact (continuous_abs.tendsto (0 : ℝ)).const_mul _
    exact hcont.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hupper
  have hmem : {l : ℝ | |l| < 1 / 16 ∧ l ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := by
    refine inter_mem (mem_nhdsWithin_of_mem_nhds ?_) self_mem_nhdsWithin
    have : Ioo (-(1 / 16 : ℝ)) (1 / 16) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with l hl
    exact abs_lt.mpr hl
  filter_upwards [hmem] with l ⟨hl16, hl0⟩
  have hl8 : |l| < 1 / 8 := by linarith
  have hl2 : |l| < 1 / 2 := by linarith
  rw [Real.norm_eq_abs]
  have hdiv :
      ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l ^ 2 -
        2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      (((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
        2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) / l ^ 2 := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos (sq_pos_of_ne_zero hl0)]
  have hnn : 0 ≤
      ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
        2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) :=
    sub_nonneg.mpr (two_mul_sq_mul_integral_sq_mul_sq_le_excess hk hν hl2)
  rw [abs_of_nonneg hnn]
  have habs_pos : 0 < |l| := abs_pos.mpr hl0
  have hcub := excess_sub_two_mul_sq_le_cubic hk hν hl8
  have hdiv_le := div_le_div_of_nonneg_right hcub (sq_nonneg l)
  have hcancel : (4704480000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * |l| ^ 3 / l ^ 2 =
      (4704480000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * |l| := by
    have hsq : l ^ 2 = |l| ^ 2 := (sq_abs l).symm
    have hpow : |l| ^ 3 = |l| * |l| ^ 2 := by ring
    rw [hsq, hpow, ← mul_assoc, mul_div_cancel_right₀ _ (ne_of_gt (sq_pos_of_pos habs_pos))]
  rw [hcancel] at hdiv_le
  have hden : 4704480000 * (ν.real univ) ^ 2 / (1 / 8 - |l|) ≤
      4704480000 * (ν.real univ) ^ 2 / (1 / 16 : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  exact hdiv_le.trans (mul_le_mul_of_nonneg_right hden habs_pos.le)

/-! ### Cauchy–Schwarz logarithmic moment inequality on `(0, ∞)` -/

/-- **Cauchy–Schwarz logarithmic moment inequality (`k ≥ 2`):**
`(∫_{v > 0} v (Φ_k(v))² dv)² ≤ (∫_{v > 0} (Φ_k(v))² dv) · (∫_{v > 0} v² (Φ_k(v))² dv)`. -/
theorem sq_setIntegral_Ioi_zero_mul_sq_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ^ 2 ≤
      (∫ v in Ioi (0 : ℝ), (arcLineInfiniteDyadicProfile k ν v) ^ 2) *
        (∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  set M0 := ∫ v in Ioi (0 : ℝ), (arcLineInfiniteDyadicProfile k ν v) ^ 2
  set M1 := ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2
  set M2 := ∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2
  have hI0 := (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn (s := Ioi (0 : ℝ))
  have hI1 := integrableOn_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile hk hν
  have hI2 := (integrable_sq_mul_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn (s := Ioi (0 : ℝ))
  have hexpand : ∀ t : ℝ,
      (∫ v in Ioi (0 : ℝ), (t * v - M1) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    have hfun : (fun v : ℝ => (t * v - M1) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ =>
          (t ^ 2 * (v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
            (2 * t * M1) * (v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) +
            M1 ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; ring
    have hsub : IntegrableOn
        (fun v : ℝ => t ^ 2 * (v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
          (2 * t * M1) * (v * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
        (Ioi (0 : ℝ)) volume :=
      (hI2.const_mul (t ^ 2)).sub (hI1.const_mul (2 * t * M1))
    rw [hfun, integral_add hsub (hI0.const_mul (M1 ^ 2)),
      integral_sub (hI2.const_mul (t ^ 2)) (hI1.const_mul (2 * t * M1)),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have h_any_t : ∀ t : ℝ, 0 ≤ t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    rw [← hexpand t]
    exact setIntegral_nonneg measurableSet_Ioi fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hM0_nn : 0 ≤ M0 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rcases eq_or_lt_of_le hM0_nn with hM0_zero | hM0_pos
  · have hM1_zero : M1 = 0 := by
      by_contra hne
      have ht := h_any_t (M1 ^ 2 / (M2 + 1))
      rw [← hM0_zero, mul_zero, add_zero] at ht
      have hM2_nn : 0 ≤ M2 :=
        setIntegral_nonneg measurableSet_Ioi fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
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

/-- **Master theorem for the global quadratic coercivity, cubic `O(|l|³)` Taylor remainder,
exact critical-line curvature limit, and Cauchy–Schwarz moment inequality:**
There exists a concrete non-zero finite Borel measure `ν` on `ArcParam` such that for every integer
`k ≥ 2`, `V_k = arcLineInfiniteDyadicVector k ν` and `Φ_k = arcLineInfiniteDyadicProfile k ν`
satisfy:
1. **Strict positivity and origin–infinity equipartition of the second logarithmic energy moment:**
   `0 < ∫_{v > 0} v² (Φ_k(v))² dv` and
   `∫_{x > 0} (log x)² (V_k(x))² dx = ∫_ℝ v² (Φ_k(v))² dv = 2 ∫_{v > 0} v² (Φ_k(v))² dv > 0`.
2. **Global quadratic coercivity across the entire open critical strip `|l| < 1/2`:**
   `2 l² ∫_ℝ v² (Φ_k(v))² dv ≤ ∫_{x > 0} x^{2l} (V_k(x))² dx − ∫_{x > 0} (V_k(x))² dx`.
3. **Scale-independent cubic `O(|l|³)` Taylor remainder bound on `|l| < 1/8`:**
   `0 ≤ (E_k(l) − E_k(0)) − 2 l² ∫_ℝ v² (Φ_k(v))² dv ≤ (4704480000 · (ν.real univ)² / (1/8 − |l|)) · |l|³`.
4. **Exact second-order critical-line curvature limit (`l → 0`, `l ≠ 0`):**
   `(E_k(l) − E_k(0)) / l² → 2 ∫_ℝ v² (Φ_k(v))² dv > 0`.
5. **Cauchy–Schwarz logarithmic moment inequality:**
   `(∫_{v > 0} v (Φ_k(v))² dv)² ≤ (∫_{v > 0} (Φ_k(v))² dv) · (∫_{v > 0} v² (Φ_k(v))² dv)`. -/
theorem exists_dyadic_criticalLine_quadraticCoercivity_arcWitness :
    ∃ (ν : Measure ArcParam) (_ : IsFiniteMeasure ν),
      ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0) ∧
      (∀ ⦃k : ℕ⦄, 2 ≤ k →
        (0 < ∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        ((∫ x in Ioi (0 : ℝ), (Real.log x) ^ 2 * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
          ∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        ((∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
          2 * ∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 →
          2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 →
          ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
            2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            (4704480000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * |l| ^ 3) ∧
        Tendsto (fun l : ℝ =>
          ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l ^ 2)
          (𝓝[≠] 0)
          (𝓝 (2 * ∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) ∧
        ((∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ^ 2 ≤
          (∫ v in Ioi (0 : ℝ), (arcLineInfiniteDyadicProfile k ν v) ^ 2) *
            (∫ v in Ioi (0 : ℝ), v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  obtain ⟨ν, hfin, hne, hsymm, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsymm, hblind, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  refine ⟨integral_sq_mul_sq_arcLineInfiniteDyadicProfile_pos hk hsymm hpd,
    setIntegral_Ioi_sq_log_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν,
    integral_sq_mul_sq_arcLineInfiniteDyadicProfile_eq_two_mul_setIntegral_Ioi hk hsymm,
    fun l hl => two_mul_sq_mul_integral_sq_mul_sq_le_excess hk hsymm hl,
    fun l hl => excess_sub_two_mul_sq_le_cubic hk hsymm hl,
    tendsto_div_sq_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero hk hsymm,
    sq_setIntegral_Ioi_zero_mul_sq_le hk hsymm⟩

end

end RHTower
