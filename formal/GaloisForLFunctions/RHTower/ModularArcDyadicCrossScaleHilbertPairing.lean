import GaloisForLFunctions.RHTower.ModularArcDyadicMellinHilbertRayleighRatio

/-!
# Cross-scale two-point strip-weighted Hilbert pairing, polarization, Cauchy–Schwarz Gram positivity, and global multiplicative log-convexity across `(−1/2, 1/2)`

In `ModularArcDyadicStripWeightedHilbertMinimum` and `ModularArcDyadicCriticalLineStrictConvexity`,
we analyzed the diagonal strip-weighted Hilbert energy
`E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx = ∫_ℝ e^{2lv} (Φ_k(v))² dv`
for a single integer scale `k ≥ 2`, proving its additive midpoint convexity
`E_k((l₁ + l₂)/2) ≤ (E_k(l₁) + E_k(l₂)) / 2`.

In this module we establish the **cross-scale, two-point strip-weighted Hilbert inner product**
`⟨V_{k₁}, V_{k₂}⟩_{l₁, l₂} = ∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx = ∫_ℝ e^{(l₁ + l₂)v} Φ_{k₁}(v) Φ_{k₂}(v) dv`
across arbitrary integer scale pairs `(k₁, k₂)` with `k₁, k₂ ≥ 2` and arbitrary strip coordinates
`l₁, l₂ ∈ (−1/2, 1/2)`:

1. **Subcritical and half-rate exponential envelopes and full-strip integrability
   (`abs_mul_arcLineInfiniteDyadicProfile_le_exp_subcritical`,
   `abs_mul_arcLineInfiniteDyadicProfile_le_exp_half_uniform`,
   `integrable_exp_add_mul_mul_arcLineInfiniteDyadicProfile`,
   `integrable_exp_two_mul_mul_arcLineInfiniteDyadicProfile`):**
   - For all `k₁, k₂ ≥ 2` and `v ∈ ℝ`,
     `|Φ_{k₁}(v) Φ_{k₂}(v)| ≤ 680625 · (ν.real univ)² · exp(−(1/2)|v|)`.
   - For all `k₁, k₂ ≥ 2` and `|l₁| < 1/2`, `|l₂| < 1/2`, the cross-scale two-point kernel
     `v ↦ exp((l₁ + l₂)v) Φ_{k₁}(v) Φ_{k₂}(v)` is integrable on `ℝ`.
2. **Multiplicative `(0, ∞)`, `(1, ∞)`, and `(0, 1]` log-scale bridges, reflection symmetry, and
   `1/2 - 1/2` origin–infinity equipartition
   (`setIntegral_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_one_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioc_zero_one_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq`,
   `setIntegral_Ioi_rpow_neg_add_mul_mul_arcLineInfiniteDyadicVector`,
   `setIntegral_Ioi_one_mul_eq_half_setIntegral_Ioi_mul`):**
   - Under `x = exp v`, `∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx = ∫_ℝ e^{(l₁ + l₂)v} Φ_{k₁}(v) Φ_{k₂}(v) dv`.
   - It is symmetric in `(k₁, k₂)` and `(l₁, l₂)`, invariant under `(l₁, l₂) ↦ (−l₁, −l₂)`, and
     satisfies exact `1/2 - 1/2` origin–infinity equipartition when `l₁ + l₂ = 0`.
3. **Exact strip-weighted polarization identity and arithmetic-mean cross-scale bound
   (`integral_exp_two_mul_sub_sq_arcLineInfiniteDyadicProfile_eq`,
   `setIntegral_Ioi_rpow_two_mul_sub_sq_arcLineInfiniteDyadicVector_eq`,
   `two_mul_abs_setIntegral_Ioi_rpow_two_mul_mul_le_add`):**
   - `∫_{x > 0} x^{2l} (V_{k₁}(x) − V_{k₂}(x))² dx = E_{k₁}(l) − 2 ⟨V_{k₁}, V_{k₂}⟩_l + E_{k₂}(l)`.
   - `2 |⟨V_{k₁}, V_{k₂}⟩_l| ≤ E_{k₁}(l) + E_{k₂}(l)`.
4. **General two-scale, two-point Cauchy–Schwarz inequality and global multiplicative log-convexity
   (`sq_integral_exp_add_mul_mul_le`, `sq_setIntegral_Ioi_rpow_add_mul_mul_le`,
   `sq_setIntegral_Ioi_one_rpow_add_mul_mul_le`,
   `sq_setIntegral_Ioi_rpow_two_mul_midpoint_le`,
   `sq_setIntegral_Ioi_one_rpow_two_mul_midpoint_le`,
   `sq_setIntegral_Ioc_zero_one_rpow_two_mul_midpoint_le`,
   `exists_dyadic_crossScale_hilbertPairing_arcWitness`):**
   - For all `k₁, k₂ ≥ 2` and `|l₁|, |l₂| < 1/2`,
     `(∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx)² ≤ E_{k₁}(l₁) · E_{k₂}(l₂)`.
   - Specializing to `k₁ = k₂ = k` yields the **global multiplicative log-convexity** of the full
     and half-line sector Hilbert energies across `(−1/2, 1/2)`:
     `(E_k((l₁ + l₂)/2))² ≤ E_k(l₁) · E_k(l₂)`,
     `(E_k^{(1, ∞)}((l₁ + l₂)/2))² ≤ E_k^{(1, ∞)}(l₁) · E_k^{(1, ∞)}(l₂)`,
     `(E_k^{(0, 1]}((l₁ + l₂)/2))² ≤ E_k^{(0, 1]}(l₁) · E_k^{(0, 1]}(l₂)`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Cross-scale exponential envelopes and full-strip two-point integrability -/

/-- **Cross-scale subcritical exponential envelope (`k₁, k₂ ≥ 2`, `0 ≤ c < 1/2`):**
For all `v ∈ ℝ`, `|Φ_{k₁}(v) Φ_{k₂}(v)| ≤ A_{k₁}(c) · A_{k₂}(c) · exp(−2c |v|)`. -/
theorem abs_mul_arcLineInfiniteDyadicProfile_le_exp_subcritical
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) (v : ℝ) :
    |arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v| ≤
      (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k₁) ^ 2))) *
        (25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k₂) ^ 2))) *
        Real.exp (-(2 * c * |v|)) := by
  rw [abs_mul]
  have h1 := abs_arcLineInfiniteDyadicProfile_le_exp_subcritical hk₁ hν hc0 hc v
  have h2 := abs_arcLineInfiniteDyadicProfile_le_exp_subcritical hk₂ hν hc0 hc v
  set A₁ := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k₁) ^ 2))
  set A₂ := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k₂) ^ 2))
  calc |arcLineInfiniteDyadicProfile k₁ ν v| * |arcLineInfiniteDyadicProfile k₂ ν v|
      ≤ (A₁ * Real.exp (-(c * |v|))) * (A₂ * Real.exp (-(c * |v|))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
    _ = A₁ * A₂ * (Real.exp (-(c * |v|)) * Real.exp (-(c * |v|))) := by ring
    _ = A₁ * A₂ * Real.exp (-(2 * c * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Scale-independent half-rate exponential envelope for the cross-scale product
(`k₁, k₂ ≥ 2`):**
For all `v ∈ ℝ`,
`|Φ_{k₁}(v) Φ_{k₂}(v)| ≤ 680625 · (ν.real univ)² · exp(−(1/2) |v|)`. -/
theorem abs_mul_arcLineInfiniteDyadicProfile_le_exp_half_uniform
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v| ≤
      680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
  rw [abs_mul]
  have h1 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk₁ hν v
  have h2 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk₂ hν v
  calc |arcLineInfiniteDyadicProfile k₁ ν v| * |arcLineInfiniteDyadicProfile k₂ ν v|
      ≤ (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 680625 * (ν.real univ) ^ 2 *
          (Real.exp (-((1 / 4 : ℝ) * |v|)) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ = 680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Full-strip two-point integrability of `v ↦ exp((l₁ + l₂)v) Φ_{k₁}(v) Φ_{k₂}(v)` on `ℝ`
(`k₁, k₂ ≥ 2`, `|l₁| < 1/2`, `|l₂| < 1/2`).** -/
theorem integrable_exp_add_mul_mul_arcLineInfiniteDyadicProfile
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    Integrable (fun v : ℝ =>
      Real.exp ((l₁ + l₂) * v) *
        (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)) := by
  set c := (|l₁ + l₂| + 1) / 4
  have habs_lt : |l₁ + l₂| < 1 := by
    calc |l₁ + l₂| ≤ |l₁| + |l₂| := abs_add_le l₁ l₂
      _ < 1 / 2 + 1 / 2 := add_lt_add hl₁ hl₂
      _ = 1 := by norm_num
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : c < 1 / 2 := by dsimp [c]; linarith
  have hcl : 0 < 2 * c - |l₁ + l₂| := by dsimp [c]; linarith
  set A₁ := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k₁) ^ 2))
  set A₂ := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k₂) ^ 2))
  refine ((integrable_rexp_neg_mul_abs hcl).const_mul (A₁ * A₂)).mono'
    (((by fun_prop : Continuous fun v : ℝ => Real.exp ((l₁ + l₂) * v))).mul
      ((continuous_arcLineInfiniteDyadicProfile hk₁ ν).mul
        (continuous_arcLineInfiniteDyadicProfile hk₂ ν))).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have hexp : Real.exp ((l₁ + l₂) * v) ≤ Real.exp (|l₁ + l₂| * |v|) := by
    rw [Real.exp_le_exp, ← abs_mul]
    exact le_abs_self _
  have hprof := abs_mul_arcLineInfiniteDyadicProfile_le_exp_subcritical hk₁ hk₂ hν hc0 hc v
  calc Real.exp ((l₁ + l₂) * v) *
          |arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v|
      ≤ Real.exp (|l₁ + l₂| * |v|) * (A₁ * A₂ * Real.exp (-(2 * c * |v|))) :=
        mul_le_mul hexp hprof (abs_nonneg _) (Real.exp_pos _).le
    _ = A₁ * A₂ * (Real.exp (|l₁ + l₂| * |v|) * Real.exp (-(2 * c * |v|))) := by ring
    _ = A₁ * A₂ * Real.exp (-((2 * c - |l₁ + l₂|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Full-strip single-point cross-scale integrability of `v ↦ exp(2lv) Φ_{k₁}(v) Φ_{k₂}(v)` on `ℝ`
(`k₁, k₂ ≥ 2`, `|l| < 1/2`).** -/
theorem integrable_exp_two_mul_mul_arcLineInfiniteDyadicProfile
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 2) :
    Integrable (fun v : ℝ =>
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)) := by
  have h := integrable_exp_add_mul_mul_arcLineInfiniteDyadicProfile hk₁ hk₂ hν hl hl
  refine h.congr (Eventually.of_forall fun v => ?_)
  dsimp only; rw [two_mul]

/-! ### Multiplicative `(0, ∞)`, `(1, ∞)`, and `(0, 1]` bridges, reflection symmetry, and `1/2 - 1/2` equipartition -/

/-- **Logarithmic change-of-variables bridge for the two-point cross-scale inner product on `(0, ∞)`
(`k₁, k₂ ≥ 1`, `l₁, l₂ ∈ ℝ`):**
`∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx = ∫_ℝ e^{(l₁ + l₂)v} Φ_{k₁}(v) Φ_{k₂}(v) dv`. -/
theorem setIntegral_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (ν : Measure ArcParam) (l₁ l₂ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) =
      ∫ v : ℝ,
        Real.exp ((l₁ + l₂) * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v) := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk₁ ν v,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk₂ ν v]
  have hexp : Real.exp v * Real.exp (v * (l₁ + l₂)) =
      Real.exp ((l₁ + l₂) * v) * Real.exp (v / 2) * Real.exp (v / 2) := by
    rw [← Real.exp_add, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp v *
          (Real.exp (v * (l₁ + l₂)) *
            (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
              arcLineInfiniteDyadicVector k₂ ν (Real.exp v)))
      = (Real.exp v * Real.exp (v * (l₁ + l₂))) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp v)) := by ring
    _ = (Real.exp ((l₁ + l₂) * v) * Real.exp (v / 2) * Real.exp (v / 2)) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp v)) := by rw [hexp]
    _ = Real.exp ((l₁ + l₂) * v) *
          ((Real.exp (v / 2) * arcLineInfiniteDyadicVector k₁ ν (Real.exp v)) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k₂ ν (Real.exp v))) := by ring

/-- **Infinity-sector (`x > 1`) log-scale bridge for the two-point cross-scale inner product
(`k₁, k₂ ≥ 1`, `l₁, l₂ ∈ ℝ`):**
`∫_{x > 1} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx = ∫_{v > 0} e^{(l₁ + l₂)v} Φ_{k₁}(v) Φ_{k₂}(v) dv`. -/
theorem setIntegral_Ioi_one_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (ν : Measure ArcParam) (l₁ l₂ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) =
      ∫ v in Ioi (0 : ℝ),
        Real.exp ((l₁ + l₂) * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v) := by
  rw [setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk₁ ν v,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk₂ ν v]
  have hexp : Real.exp v * Real.exp (v * (l₁ + l₂)) =
      Real.exp ((l₁ + l₂) * v) * Real.exp (v / 2) * Real.exp (v / 2) := by
    rw [← Real.exp_add, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp v *
          (Real.exp (v * (l₁ + l₂)) *
            (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
              arcLineInfiniteDyadicVector k₂ ν (Real.exp v)))
      = (Real.exp v * Real.exp (v * (l₁ + l₂))) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp v)) := by ring
    _ = (Real.exp ((l₁ + l₂) * v) * Real.exp (v / 2) * Real.exp (v / 2)) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp v)) := by rw [hexp]
    _ = Real.exp ((l₁ + l₂) * v) *
          ((Real.exp (v / 2) * arcLineInfiniteDyadicVector k₁ ν (Real.exp v)) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k₂ ν (Real.exp v))) := by ring

/-- **Origin-sector (`x ∈ (0, 1]`) log-scale bridge for the two-point cross-scale inner product
(`k₁, k₂ ≥ 1`, `l₁, l₂ ∈ ℝ`):**
`∫_{x ∈ (0, 1]} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx = ∫_{v > 0} e^{−(l₁ + l₂)v} Φ_{k₁}(v) Φ_{k₂}(v) dv`. -/
theorem setIntegral_Ioc_zero_one_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (ν : Measure ArcParam) (l₁ l₂ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) =
      ∫ v in Ioi (0 : ℝ),
        Real.exp (-((l₁ + l₂) * v)) *
          (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v) := by
  rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos (-v)), Real.log_exp]
  have hprof₁ : Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k₁ ν (Real.exp (-v)) =
      arcLineInfiniteDyadicProfile k₁ ν v := by
    rw [exp_half_mul_arcLineInfiniteDyadicVector hk₁ ν (-v), arcLineInfiniteDyadicProfile_neg]
  have hprof₂ : Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k₂ ν (Real.exp (-v)) =
      arcLineInfiniteDyadicProfile k₂ ν v := by
    rw [exp_half_mul_arcLineInfiniteDyadicVector hk₂ ν (-v), arcLineInfiniteDyadicProfile_neg]
  have hexp : Real.exp (-v) * Real.exp (-v * (l₁ + l₂)) =
      Real.exp (-((l₁ + l₂) * v)) * Real.exp ((-v) / 2) * Real.exp ((-v) / 2) := by
    rw [← Real.exp_add, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp (-v) *
          (Real.exp (-v * (l₁ + l₂)) *
            (arcLineInfiniteDyadicVector k₁ ν (Real.exp (-v)) *
              arcLineInfiniteDyadicVector k₂ ν (Real.exp (-v))))
      = (Real.exp (-v) * Real.exp (-v * (l₁ + l₂))) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp (-v)) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp (-v))) := by ring
    _ = (Real.exp (-((l₁ + l₂) * v)) * Real.exp ((-v) / 2) * Real.exp ((-v) / 2)) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp (-v)) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp (-v))) := by rw [hexp]
    _ = Real.exp (-((l₁ + l₂) * v)) *
          ((Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k₁ ν (Real.exp (-v))) *
            (Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k₂ ν (Real.exp (-v)))) := by ring
    _ = Real.exp (-((l₁ + l₂) * v)) *
          (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v) := by
        rw [hprof₁, hprof₂]

/-- **Origin–infinity sector reflection duality for the cross-scale inner product
(`k₁, k₂ ≥ 1`, `l₁, l₂ ∈ ℝ`):**
`∫_{x ∈ (0, 1]} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx = ∫_{x > 1} x^{(−l₁) + (−l₂)} V_{k₁}(x) V_{k₂}(x) dx`. -/
theorem setIntegral_Ioc_zero_one_rpow_add_mul_mul_eq_setIntegral_Ioi_one_neg
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (ν : Measure ArcParam) (l₁ l₂ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) =
      ∫ x in Ioi (1 : ℝ),
        x ^ (-l₁ + -l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x) := by
  rw [setIntegral_Ioc_zero_one_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq hk₁ hk₂ ν l₁ l₂,
    setIntegral_Ioi_one_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq hk₁ hk₂ ν (-l₁) (-l₂)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  congr 2; ring

/-- **Integrability of `x ↦ x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x)` on `(0, ∞)` across
`|l₁| < 1/2`, `|l₂| < 1/2` (`k₁, k₂ ≥ 2`).** -/
theorem integrableOn_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      x ^ (l₁ + l₂) *
        (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x))
      (Ioi (0 : ℝ)) := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  rw [integrableOn_Ioi_iff_integrable_exp_mul]
  refine (integrable_exp_add_mul_mul_arcLineInfiniteDyadicProfile hk₁ hk₂ hν hl₁ hl₂).congr
    (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk₁1 ν v,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk₂1 ν v]
  have hexp : Real.exp v * Real.exp (v * (l₁ + l₂)) =
      Real.exp ((l₁ + l₂) * v) * Real.exp (v / 2) * Real.exp (v / 2) := by
    rw [← Real.exp_add, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  calc Real.exp ((l₁ + l₂) * v) *
          ((Real.exp (v / 2) * arcLineInfiniteDyadicVector k₁ ν (Real.exp v)) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k₂ ν (Real.exp v)))
      = (Real.exp ((l₁ + l₂) * v) * Real.exp (v / 2) * Real.exp (v / 2)) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp v)) := by ring
    _ = (Real.exp v * Real.exp (v * (l₁ + l₂))) *
          (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
            arcLineInfiniteDyadicVector k₂ ν (Real.exp v)) := by rw [← hexp]
    _ = Real.exp v *
          (Real.exp (v * (l₁ + l₂)) *
            (arcLineInfiniteDyadicVector k₁ ν (Real.exp v) *
              arcLineInfiniteDyadicVector k₂ ν (Real.exp v))) := by ring

/-- **Functional equation reflection symmetry `(l₁, l₂) ↦ (−l₁, −l₂)` for the cross-scale
inner product (`k₁, k₂ ≥ 2`, `|l₁| < 1/2`, `|l₂| < 1/2`).** -/
theorem setIntegral_Ioi_rpow_neg_add_mul_mul_arcLineInfiniteDyadicVector
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l₁ + -l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) =
      ∫ x in Ioi (0 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x) := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  have h1 := setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one
    (integrableOn_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector hk₁ hk₂ hν hl₁ hl₂)
  have h2 := setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one
    (integrableOn_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector hk₁ hk₂ hν
      (show |-l₁| < 1 / 2 by simpa using hl₁) (show |-l₂| < 1 / 2 by simpa using hl₂))
  have h3 := setIntegral_Ioc_zero_one_rpow_add_mul_mul_eq_setIntegral_Ioi_one_neg hk₁1 hk₂1 ν l₁ l₂
  have h4 := setIntegral_Ioc_zero_one_rpow_add_mul_mul_eq_setIntegral_Ioi_one_neg hk₁1 hk₂1 ν (-l₁) (-l₂)
  rw [neg_neg, neg_neg] at h4
  linarith

/-- **Exact `1/2 - 1/2` origin–infinity equipartition of the critical-line (`l = 0`) cross-scale
Hilbert inner product (`k₁, k₂ ≥ 2`).** -/
theorem setIntegral_Ioi_one_mul_eq_half_setIntegral_Ioi_mul
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    (∫ x in Ioi (1 : ℝ),
        arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x) =
      (1 / 2 : ℝ) *
        ∫ x in Ioi (0 : ℝ),
          arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  have h0 : |(0 : ℝ)| < 1 / 2 := by norm_num
  have hsum := setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one
    (integrableOn_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector hk₁ hk₂ hν h0 h0)
  have hsymm := setIntegral_Ioc_zero_one_rpow_add_mul_mul_eq_setIntegral_Ioi_one_neg hk₁1 hk₂1 ν 0 0
  simp only [add_zero, neg_zero, Real.rpow_zero, one_mul] at hsum hsymm
  linarith

/-! ### Exact strip-weighted polarization identity and arithmetic-mean cross-scale bound -/

/-- **Exact strip-weighted polarization identity on `ℝ` (`k₁, k₂ ≥ 2`, `|l| < 1/2`):**
`∫_ℝ e^{2lv} (Φ_{k₁}(v) − Φ_{k₂}(v))² dv = E_{k₁}(l) − 2 ⟨Φ_{k₁}, Φ_{k₂}⟩_l + E_{k₂}(l)`. -/
theorem integral_exp_two_mul_sub_sq_arcLineInfiniteDyadicProfile_eq
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ v : ℝ,
        Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) =
      (∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
        2 * (∫ v : ℝ,
          Real.exp (2 * l * v) *
            (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)) +
        (∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
  have hI₁ := integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk₁ hν hl
  have hI₂ := integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk₂ hν hl
  have hI₁₂ := integrable_exp_two_mul_mul_arcLineInfiniteDyadicProfile hk₁ hk₂ hν hl
  have hfun : (fun v : ℝ =>
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) =
      fun v : ℝ =>
        (Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2 -
          2 * (Real.exp (2 * l * v) *
            (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))) +
          Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2 := by
    funext v; ring
  have hsub : Integrable (fun v : ℝ =>
      Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2 -
        2 * (Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))) :=
    hI₁.sub (hI₁₂.const_mul 2)
  rw [hfun, integral_add hsub hI₂, integral_sub hI₁ (hI₁₂.const_mul 2), integral_const_mul]

/-- **Exact strip-weighted polarization identity on `(0, ∞)` (`k₁, k₂ ≥ 2`, `|l| < 1/2`):**
`∫_{x > 0} x^{2l} (V_{k₁}(x) − V_{k₂}(x))² dx = E_{k₁}(l) − 2 ⟨V_{k₁}, V_{k₂}⟩_l + E_{k₂}(l)`. -/
theorem setIntegral_Ioi_rpow_two_mul_sub_sq_arcLineInfiniteDyadicVector_eq
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) *
          (arcLineInfiniteDyadicVector k₁ ν x - arcLineInfiniteDyadicVector k₂ ν x) ^ 2) =
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) -
        2 * (∫ x in Ioi (0 : ℝ),
          x ^ (2 * l) *
            (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) +
        (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k₂ ν x) ^ 2) := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  have hlhs : (∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) *
          (arcLineInfiniteDyadicVector k₁ ν x - arcLineInfiniteDyadicVector k₂ ν x) ^ 2) =
      ∫ v : ℝ,
        Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2 := by
    rw [setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [mul_sub, exp_half_mul_arcLineInfiniteDyadicVector hk₁1 ν v,
      exp_half_mul_arcLineInfiniteDyadicVector hk₂1 ν v]
  have h12 : (∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) =
      ∫ v : ℝ,
        Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v) := by
    have h := setIntegral_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq hk₁1 hk₂1 ν l l
    rwa [← two_mul] at h
  rw [hlhs, h12,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk₁1 ν l,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk₂1 ν l,
    integral_exp_two_mul_sub_sq_arcLineInfiniteDyadicProfile_eq hk₁ hk₂ hν hl]

/-- **Scale-independent uniform bound on the two-point cross-scale inner product across
`|l₁| < 1/4`, `|l₂| < 1/4` (`k₁, k₂ ≥ 2`):**
`|∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx| ≤ 1361250 · (ν.real univ)² / (1/2 − |l₁ + l₂|)`. -/
theorem abs_setIntegral_Ioi_rpow_add_mul_mul_le_uniform
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l₁ l₂ : ℝ} (hl : |l₁ + l₂| < 1 / 2) :
    |∫ x in Ioi (0 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)| ≤
      1361250 * (ν.real univ) ^ 2 / (1 / 2 - |l₁ + l₂|) := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  have hcl : 0 < 1 / 2 - |l₁ + l₂| := sub_pos.mpr hl
  rw [setIntegral_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq hk₁1 hk₂1 ν l₁ l₂]
  set B := 680625 * (ν.real univ) ^ 2
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 2 - |l₁ + l₂|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hcl).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.exp ((l₁ + l₂) * v) *
        (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hcl] at h1
    calc |∫ v : ℝ,
            Real.exp ((l₁ + l₂) * v) *
              (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)|
        ≤ B * (2 / (1 / 2 - |l₁ + l₂|)) := h1
      _ = 1361250 * (ν.real univ) ^ 2 / (1 / 2 - |l₁ + l₂|) := by dsimp [B]; ring
  · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    have hexp : Real.exp ((l₁ + l₂) * v) ≤ Real.exp (|l₁ + l₂| * |v|) := by
      rw [Real.exp_le_exp, ← abs_mul]
      exact le_abs_self _
    have hprof := abs_mul_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk₁ hk₂ hν v
    calc Real.exp ((l₁ + l₂) * v) *
            |arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v|
        ≤ Real.exp (|l₁ + l₂| * |v|) * (B * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul hexp hprof (abs_nonneg _) (Real.exp_pos _).le
      _ = B * (Real.exp (|l₁ + l₂| * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
      _ = B * Real.exp (-((1 / 2 - |l₁ + l₂|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-! ### General two-scale, two-point Cauchy–Schwarz inequality and global multiplicative log-convexity -/

/-- **General two-scale, two-point Cauchy–Schwarz inequality on `ℝ`
(`k₁, k₂ ≥ 2`, `|l₁| < 1/2`, `|l₂| < 1/2`):**
`(∫_ℝ e^{(l₁ + l₂)v} Φ_{k₁}(v) Φ_{k₂}(v) dv)² ≤ (∫_ℝ e^{2 l₁ v} (Φ_{k₁}(v))² dv) · (∫_ℝ e^{2 l₂ v} (Φ_{k₂}(v))² dv)`. -/
theorem sq_integral_exp_add_mul_mul_le
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ v : ℝ,
        Real.exp ((l₁ + l₂) * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)) ^ 2 ≤
      (∫ v : ℝ, Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) *
        (∫ v : ℝ, Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
  set M0 := ∫ v : ℝ, Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2
  set M1 := ∫ v : ℝ,
    Real.exp ((l₁ + l₂) * v) *
      (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)
  set M2 := ∫ v : ℝ, Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2
  have hI0 := integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk₂ hν hl₂
  have hI1 := integrable_exp_add_mul_mul_arcLineInfiniteDyadicProfile hk₁ hk₂ hν hl₁ hl₂
  have hI2 := integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk₁ hν hl₁
  have hexpand : ∀ t : ℝ,
      (∫ v : ℝ,
        (t * (Real.exp (l₁ * v) * arcLineInfiniteDyadicProfile k₁ ν v) -
          M1 * (Real.exp (l₂ * v) * arcLineInfiniteDyadicProfile k₂ ν v)) ^ 2) =
        t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    have hfun : (fun v : ℝ =>
        (t * (Real.exp (l₁ * v) * arcLineInfiniteDyadicProfile k₁ ν v) -
          M1 * (Real.exp (l₂ * v) * arcLineInfiniteDyadicProfile k₂ ν v)) ^ 2) =
        fun v : ℝ =>
          (t ^ 2 * (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
            (2 * t * M1) *
              (Real.exp ((l₁ + l₂) * v) *
                (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))) +
            M1 ^ 2 * (Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
      funext v
      have hexp1 : (Real.exp (l₁ * v)) ^ 2 = Real.exp (2 * l₁ * v) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hexp2 : (Real.exp (l₂ * v)) ^ 2 = Real.exp (2 * l₂ * v) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hexp12 : Real.exp (l₁ * v) * Real.exp (l₂ * v) = Real.exp ((l₁ + l₂) * v) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (t * (Real.exp (l₁ * v) * arcLineInfiniteDyadicProfile k₁ ν v) -
              M1 * (Real.exp (l₂ * v) * arcLineInfiniteDyadicProfile k₂ ν v)) ^ 2
          = t ^ 2 * ((Real.exp (l₁ * v)) ^ 2 * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
              (2 * t * M1) *
                ((Real.exp (l₁ * v) * Real.exp (l₂ * v)) *
                  (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)) +
              M1 ^ 2 * ((Real.exp (l₂ * v)) ^ 2 * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
            ring
        _ = (t ^ 2 * (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
              (2 * t * M1) *
                (Real.exp ((l₁ + l₂) * v) *
                  (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))) +
              M1 ^ 2 * (Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
            rw [hexp1, hexp2, hexp12]
    have hsub : Integrable (fun v : ℝ =>
        t ^ 2 * (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
          (2 * t * M1) *
            (Real.exp ((l₁ + l₂) * v) *
              (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))) :=
      (hI2.const_mul (t ^ 2)).sub (hI1.const_mul (2 * t * M1))
    rw [hfun, integral_add hsub (hI0.const_mul (M1 ^ 2)),
      integral_sub (hI2.const_mul (t ^ 2)) (hI1.const_mul (2 * t * M1)),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have h_any_t : ∀ t : ℝ, 0 ≤ t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    rw [← hexpand t]
    exact integral_nonneg fun _ => sq_nonneg _
  have hM0_nn : 0 ≤ M0 :=
    integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  rcases eq_or_lt_of_le hM0_nn with hM0_zero | hM0_pos
  · have hM1_zero : M1 = 0 := by
      by_contra hne
      have ht := h_any_t (M1 ^ 2 / (M2 + 1))
      rw [← hM0_zero, mul_zero, add_zero] at ht
      have hM2_nn : 0 ≤ M2 :=
        integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
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
        M0 * (M2 * M0 - M1 ^ 2) := by ring
    rw [hfactor] at hnn
    have hsub : 0 ≤ M2 * M0 - M1 ^ 2 := nonneg_of_mul_nonneg_right hnn hM0_pos
    linarith

/-- **General two-scale, two-point Cauchy–Schwarz inequality on `(0, ∞)`
(`k₁, k₂ ≥ 2`, `|l₁| < 1/2`, `|l₂| < 1/2`):**
`(∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx)² ≤ E_{k₁}(l₁) · E_{k₂}(l₂)`. -/
theorem sq_setIntegral_Ioi_rpow_add_mul_mul_le
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) ^ 2 ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) *
        (∫ x in Ioi (0 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k₂ ν x) ^ 2) := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  rw [setIntegral_Ioi_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq hk₁1 hk₂1 ν l₁ l₂,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk₁1 ν l₁,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk₂1 ν l₂]
  exact sq_integral_exp_add_mul_mul_le hk₁ hk₂ hν hl₁ hl₂

/-- **General two-scale, two-point Cauchy–Schwarz inequality on the infinity sector `(1, ∞)`
(`k₁, k₂ ≥ 2`, `|l₁| < 1/2`, `|l₂| < 1/2`):**
`(∫_{x > 1} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx)² ≤ E_{k₁}^{(1, ∞)}(l₁) · E_{k₂}^{(1, ∞)}(l₂)`. -/
theorem sq_setIntegral_Ioi_one_rpow_add_mul_mul_le
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) ^ 2 ≤
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) *
        (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k₂ ν x) ^ 2) := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  rw [setIntegral_Ioi_one_rpow_add_mul_mul_arcLineInfiniteDyadicVector_eq hk₁1 hk₂1 ν l₁ l₂,
    setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk₁1 ν l₁,
    setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk₂1 ν l₂]
  set M0 := ∫ v in Ioi (0 : ℝ), Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2
  set M1 := ∫ v in Ioi (0 : ℝ),
    Real.exp ((l₁ + l₂) * v) *
      (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)
  set M2 := ∫ v in Ioi (0 : ℝ), Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2
  have hI0 := (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk₂ hν hl₂).integrableOn
    (s := Ioi (0 : ℝ))
  have hI1 := (integrable_exp_add_mul_mul_arcLineInfiniteDyadicProfile hk₁ hk₂ hν hl₁ hl₂).integrableOn
    (s := Ioi (0 : ℝ))
  have hI2 := (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk₁ hν hl₁).integrableOn
    (s := Ioi (0 : ℝ))
  have hexpand : ∀ t : ℝ,
      (∫ v in Ioi (0 : ℝ),
        (t * (Real.exp (l₁ * v) * arcLineInfiniteDyadicProfile k₁ ν v) -
          M1 * (Real.exp (l₂ * v) * arcLineInfiniteDyadicProfile k₂ ν v)) ^ 2) =
        t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    have hfun : (fun v : ℝ =>
        (t * (Real.exp (l₁ * v) * arcLineInfiniteDyadicProfile k₁ ν v) -
          M1 * (Real.exp (l₂ * v) * arcLineInfiniteDyadicProfile k₂ ν v)) ^ 2) =
        fun v : ℝ =>
          (t ^ 2 * (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
            (2 * t * M1) *
              (Real.exp ((l₁ + l₂) * v) *
                (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))) +
            M1 ^ 2 * (Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
      funext v
      have hexp1 : (Real.exp (l₁ * v)) ^ 2 = Real.exp (2 * l₁ * v) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hexp2 : (Real.exp (l₂ * v)) ^ 2 = Real.exp (2 * l₂ * v) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hexp12 : Real.exp (l₁ * v) * Real.exp (l₂ * v) = Real.exp ((l₁ + l₂) * v) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (t * (Real.exp (l₁ * v) * arcLineInfiniteDyadicProfile k₁ ν v) -
              M1 * (Real.exp (l₂ * v) * arcLineInfiniteDyadicProfile k₂ ν v)) ^ 2
          = t ^ 2 * ((Real.exp (l₁ * v)) ^ 2 * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
              (2 * t * M1) *
                ((Real.exp (l₁ * v) * Real.exp (l₂ * v)) *
                  (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)) +
              M1 ^ 2 * ((Real.exp (l₂ * v)) ^ 2 * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
            ring
        _ = (t ^ 2 * (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
              (2 * t * M1) *
                (Real.exp ((l₁ + l₂) * v) *
                  (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v))) +
              M1 ^ 2 * (Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) := by
            rw [hexp1, hexp2, hexp12]
    have hsub : IntegrableOn
        (fun v : ℝ =>
          t ^ 2 * (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k₁ ν v) ^ 2) -
            (2 * t * M1) *
              (Real.exp ((l₁ + l₂) * v) *
                (arcLineInfiniteDyadicProfile k₁ ν v * arcLineInfiniteDyadicProfile k₂ ν v)))
        (Ioi (0 : ℝ)) volume :=
      (hI2.const_mul (t ^ 2)).sub (hI1.const_mul (2 * t * M1))
    rw [hfun, integral_add hsub (hI0.const_mul (M1 ^ 2)),
      integral_sub (hI2.const_mul (t ^ 2)) (hI1.const_mul (2 * t * M1)),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have h_any_t : ∀ t : ℝ, 0 ≤ t ^ 2 * M2 - 2 * t * M1 * M1 + M1 ^ 2 * M0 := by
    intro t
    rw [← hexpand t]
    exact setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hM0_nn : 0 ≤ M0 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  rcases eq_or_lt_of_le hM0_nn with hM0_zero | hM0_pos
  · have hM1_zero : M1 = 0 := by
      by_contra hne
      have ht := h_any_t (M1 ^ 2 / (M2 + 1))
      rw [← hM0_zero, mul_zero, add_zero] at ht
      have hM2_nn : 0 ≤ M2 :=
        setIntegral_nonneg measurableSet_Ioi fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
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
        M0 * (M2 * M0 - M1 ^ 2) := by ring
    rw [hfactor] at hnn
    have hsub : 0 ≤ M2 * M0 - M1 ^ 2 := nonneg_of_mul_nonneg_right hnn hM0_pos
    linarith

/-- **Global multiplicative log-convexity of the full strip-weighted Hilbert energy `E_k(l)`
across `(−1/2, 1/2)` (`k ≥ 2`):**
For all `l₁, l₂ ∈ (−1/2, 1/2)`, `(E_k((l₁ + l₂) / 2))² ≤ E_k(l₁) · E_k(l₂)`. -/
theorem sq_setIntegral_Ioi_rpow_two_mul_midpoint_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ^ 2 ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) *
        (∫ x in Ioi (0 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have heq : (∫ x in Ioi (0 : ℝ),
        x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi (0 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k ν x * arcLineInfiniteDyadicVector k ν x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [← sq]; congr 2; ring
  rw [heq]
  exact sq_setIntegral_Ioi_rpow_add_mul_mul_le hk hk hν hl₁ hl₂

/-- **Global multiplicative log-convexity of the infinity-sector Hilbert energy `E_k^{(1, ∞)}(l)`
across `(−1/2, 1/2)` (`k ≥ 2`):**
For all `l₁, l₂ ∈ (−1/2, 1/2)`, `(E_k^{(1, ∞)}((l₁ + l₂) / 2))² ≤ E_k^{(1, ∞)}(l₁) · E_k^{(1, ∞)}(l₂)`. -/
theorem sq_setIntegral_Ioi_one_rpow_two_mul_midpoint_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ^ 2 ≤
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) *
        (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have heq : (∫ x in Ioi (1 : ℝ),
        x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi (1 : ℝ),
        x ^ (l₁ + l₂) *
          (arcLineInfiniteDyadicVector k ν x * arcLineInfiniteDyadicVector k ν x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [← sq]; congr 2; ring
  rw [heq]
  exact sq_setIntegral_Ioi_one_rpow_add_mul_mul_le hk hk hν hl₁ hl₂

/-- **Global multiplicative log-convexity of the origin-sector Hilbert energy `E_k^{(0, 1]}(l)`
across `(−1/2, 1/2)` (`k ≥ 2`):**
For all `l₁, l₂ ∈ (−1/2, 1/2)`, `(E_k^{(0, 1]}((l₁ + l₂) / 2))² ≤ E_k^{(0, 1]}(l₁) · E_k^{(0, 1]}(l₂)`. -/
theorem sq_setIntegral_Ioc_zero_one_rpow_two_mul_midpoint_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ^ 2 ≤
      (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) *
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν ((l₁ + l₂) / 2),
    setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν l₁,
    setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν l₂]
  have hmid : -((l₁ + l₂) / 2) = (-l₁ + -l₂) / 2 := by ring
  rw [hmid]
  exact sq_setIntegral_Ioi_one_rpow_two_mul_midpoint_le hk hν
    (by simpa using hl₁) (by simpa using hl₂)

/-- **Master theorem for the cross-scale two-point strip-weighted Hilbert pairing, polarization,
Cauchy–Schwarz Gram positivity, and global multiplicative log-convexity:**
There exists a concrete non-zero finite Borel measure `ν` on `ArcParam` such that for all integers
`k₁, k₂ ≥ 2` and all `|l₁| < 1/2`, `|l₂| < 1/2`:
1. **Functional equation reflection symmetry and `1/2 - 1/2` origin–infinity equipartition:**
   `∫_{x > 0} x^{−l₁ − l₂} V_{k₁}(x) V_{k₂}(x) dx = ∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx`
   and `∫_{x > 1} V_{k₁}(x) V_{k₂}(x) dx = (1/2) ∫_{x > 0} V_{k₁}(x) V_{k₂}(x) dx`.
2. **Exact strip-weighted polarization identity (`l = l₁`):**
   `∫_{x > 0} x^{2 l₁} (V_{k₁}(x) − V_{k₂}(x))² dx = E_{k₁}(l₁) − 2 ⟨V_{k₁}, V_{k₂}⟩_{l₁} + E_{k₂}(l₁)`.
3. **General two-scale, two-point Cauchy–Schwarz inequality:**
   `(∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx)² ≤ E_{k₁}(l₁) · E_{k₂}(l₂)`.
4. **Global multiplicative log-convexity of the full and half-line sector Hilbert energies:**
   `(E_{k₁}((l₁ + l₂)/2))² ≤ E_{k₁}(l₁) · E_{k₁}(l₂)` and
   `(E_{k₁}^{(1, ∞)}((l₁ + l₂)/2))² ≤ E_{k₁}^{(1, ∞)}(l₁) · E_{k₁}^{(1, ∞)}(l₂)` and
   `(E_{k₁}^{(0, 1]}((l₁ + l₂)/2))² ≤ E_{k₁}^{(0, 1]}(l₁) · E_{k₁}^{(0, 1]}(l₂)`. -/
theorem exists_dyadic_crossScale_hilbertPairing_arcWitness :
    ∃ (ν : Measure ArcParam) (_ : IsFiniteMeasure ν),
      ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ m : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m * t) = 0) ∧
      (∀ ⦃k₁ k₂ : ℕ⦄, 2 ≤ k₁ → 2 ≤ k₂ →
        ((∫ x in Ioi (1 : ℝ),
            arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x) =
          (1 / 2 : ℝ) *
            ∫ x in Ioi (0 : ℝ),
              arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x) ∧
        (∀ ⦃l₁ l₂ : ℝ⦄, |l₁| < 1 / 2 → |l₂| < 1 / 2 →
          (∫ x in Ioi (0 : ℝ),
              x ^ (-l₁ + -l₂) *
                (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) =
            (∫ x in Ioi (0 : ℝ),
              x ^ (l₁ + l₂) *
                (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) ∧
          (∫ x in Ioi (0 : ℝ),
              x ^ (2 * l₁) *
                (arcLineInfiniteDyadicVector k₁ ν x - arcLineInfiniteDyadicVector k₂ ν x) ^ 2) =
            (∫ x in Ioi (0 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) -
              2 * (∫ x in Ioi (0 : ℝ),
                x ^ (2 * l₁) *
                  (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) +
              (∫ x in Ioi (0 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₂ ν x) ^ 2) ∧
          (∫ x in Ioi (0 : ℝ),
              x ^ (l₁ + l₂) *
                (arcLineInfiniteDyadicVector k₁ ν x * arcLineInfiniteDyadicVector k₂ ν x)) ^ 2 ≤
            (∫ x in Ioi (0 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) *
              (∫ x in Ioi (0 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k₂ ν x) ^ 2) ∧
          (∫ x in Ioi (0 : ℝ),
              x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) ^ 2 ≤
            (∫ x in Ioi (0 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) *
              (∫ x in Ioi (0 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) ∧
          (∫ x in Ioi (1 : ℝ),
              x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) ^ 2 ≤
            (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) *
              (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) ∧
          (∫ x in Ioc (0 : ℝ) 1,
              x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) ^ 2 ≤
            (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2) *
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k₁ ν x) ^ 2))) := by
  obtain ⟨ν, hfin, hne, hsymm, hblind_whittaker, _⟩ := exists_arcWitness
  have hblind : ∀ m : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m * t) = 0 := fun m => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker m).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsymm, hblind, fun k₁ k₂ hk₁ hk₂ => ?_⟩
  refine ⟨setIntegral_Ioi_one_mul_eq_half_setIntegral_Ioi_mul hk₁ hk₂ hsymm,
    fun l₁ l₂ hl₁ hl₂ =>
      ⟨setIntegral_Ioi_rpow_neg_add_mul_mul_arcLineInfiniteDyadicVector hk₁ hk₂ hsymm hl₁ hl₂,
       setIntegral_Ioi_rpow_two_mul_sub_sq_arcLineInfiniteDyadicVector_eq hk₁ hk₂ hsymm hl₁,
       sq_setIntegral_Ioi_rpow_add_mul_mul_le hk₁ hk₂ hsymm hl₁ hl₂,
       sq_setIntegral_Ioi_rpow_two_mul_midpoint_le hk₁ hsymm hl₁ hl₂,
       sq_setIntegral_Ioi_one_rpow_two_mul_midpoint_le hk₁ hsymm hl₁ hl₂,
       sq_setIntegral_Ioc_zero_one_rpow_two_mul_midpoint_le hk₁ hsymm hl₁ hl₂⟩⟩

end

end RHTower
