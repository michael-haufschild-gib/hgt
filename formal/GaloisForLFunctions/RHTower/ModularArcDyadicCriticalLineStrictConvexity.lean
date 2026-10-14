import GaloisForLFunctions.RHTower.ModularArcDyadicTwoVariableLipschitzRegularity

/-!
# Strict midpoint convexity of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy, the `2 sinh²(lv)` excess identity, strict uniqueness of the critical-line minimum (`l = 0`), and `O(l²)` stationary curvature

In `ModularArcDyadicStripWeightedHilbertMinimum`, we proved the non-strict Critical-Line Minimum
Principle
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx ≤ ∫_{x > 0} x^{2l} · (arcLineInfiniteDyadicVector k ν x)² dx`
for all `|l| < 1/2`.

In this module we establish the **exact midpoint-convexity defect law**, **strict midpoint
convexity** across the open critical strip `(−1/2, 1/2)`, **strict uniqueness of the critical-line
minimum `l = 0`**, and the **scale-independent quadratic `O(l²)` stationary bound** near `l = 0`:

1. **Exact midpoint-convexity defect and critical-line `2 sinh²(lv)` excess identities
   (`exp_two_mul_add_div_two_sub`, `cosh_two_mul_sub_one`,
   `integral_exp_two_mul_sq_midpoint_defect_eq`,
   `setIntegral_Ioi_rpow_two_mul_sq_midpoint_defect_eq`,
   `integral_exp_two_mul_sq_sub_sq_arcLineInfiniteDyadicProfile_eq`,
   `setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_eq`):**
   - For every `l₁, l₂ ∈ (−1/2, 1/2)` (`|l₁| < 1/2`, `|l₂| < 1/2`),
     `(E_k(l₁) + E_k(l₂)) / 2 − E_k((l₁ + l₂) / 2) = (1/2) ∫_ℝ (e^{l₁ v} − e^{l₂ v})² (Φ_k(v))² dv = (1/2) ∫_{x > 0} (x^{l₁} − x^{l₂})² (V_k(x))² dx`.
   - At `l₁ = l`, `l₂ = −l` (`|l| < 1/2`), whose midpoint is the critical line `0`,
     `E_k(l) − E_k(0) = ∫_{x > 0} x^{2l} (V_k(x))² dx − ∫_{x > 0} (V_k(x))² dx = 2 ∫_ℝ (sinh(lv))² (Φ_k(v))² dv = (1/2) ∫_{x > 0} (x^l − x^{−l})² (V_k(x))² dx`.
2. **Strict midpoint convexity across `(−1/2, 1/2)` and strict uniqueness of the critical-line
   minimum `l = 0` (`integral_sq_exp_sub_exp_mul_sq_arcLineInfiniteDyadicProfile_pos`,
   `setIntegral_Ioi_rpow_two_mul_sq_midpoint_lt_of_ne`,
   `setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_lt_rpow_two_mul_of_ne_zero`,
   `setIntegral_Ioi_rpow_two_mul_sq_eq_sq_iff`):**
   - Whenever `l₁ ≠ l₂` in `(−1/2, 1/2)`, strictly `E_k((l₁ + l₂)/2) < (E_k(l₁) + E_k(l₂)) / 2`.
   - Whenever `l ∈ (−1/2, 1/2)` with `l ≠ 0`, strictly `E_k(0) < E_k(l)`.
   - Across `|l| < 1/2`, `∫_{x > 0} x^{2l} (V_k(x))² dx = ∫_{x > 0} (V_k(x))² dx ↔ l = 0`:
     the critical line `l = 0` (`Re(s) = 1/2`) is the **unique global minimizer** of the
     strip-weighted `L²` Hilbert energy.
3. **Scale-independent quadratic `O(l²)` upper bound and stationary first derivative at `l = 0`
   (`abs_sinh_le_abs_mul_exp_abs`, `two_mul_sq_sinh_mul_le_exp`,
   `setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_le_sq`,
   `tendsto_div_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero`,
   `exists_dyadic_criticalLine_strictConvexity_arcWitness`):**
   - For every `k ≥ 2` and `|l| < 1/8`,
     `0 ≤ ∫_{x > 0} x^{2l} (V_k(x))² dx − ∫_{x > 0} (V_k(x))² dx ≤ (87120000 · (ν.real univ)² / (1/8 − |l|)) · l²`.
   - Consequently `(E_k(l) − E_k(0)) / l → 0` as `l → 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Pointwise algebraic identities for midpoint convexity and critical-line `2 sinh²(lv)` excess -/

/-- **Pointwise exponential midpoint-convexity defect identity:**
For all `l₁, l₂, v ∈ ℝ`,
`(exp(2 l₁ v) + exp(2 l₂ v)) / 2 − exp(2 ((l₁ + l₂) / 2) v) = (1 / 2) · (exp(l₁ v) − exp(l₂ v))²`. -/
theorem exp_two_mul_add_div_two_sub (l₁ l₂ v : ℝ) :
    (Real.exp (2 * l₁ * v) + Real.exp (2 * l₂ * v)) / 2 -
        Real.exp (2 * ((l₁ + l₂) / 2) * v) =
      (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 := by
  have h1 : Real.exp (2 * l₁ * v) = (Real.exp (l₁ * v)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (2 * l₂ * v) = (Real.exp (l₂ * v)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (2 * ((l₁ + l₂) / 2) * v) = Real.exp (l₁ * v) * Real.exp (l₂ * v) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2, h3]; ring

/-- **Pointwise `cosh(2lv) − 1 = 2 sinh²(lv)` excess identity:**
For all `l, v ∈ ℝ`,
`cosh(2 l v) − 1 = 2 · (sinh(l v))²` and `2 · (sinh(l v))² = (1 / 2) · (exp(l v) − exp(−(l v)))²`. -/
theorem cosh_two_mul_sub_one (l v : ℝ) :
    Real.cosh (2 * l * v) - 1 = 2 * (Real.sinh (l * v)) ^ 2 := by
  have h1 : Real.exp (2 * l * v) = (Real.exp (l * v)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(2 * l * v)) = (Real.exp (-(l * v))) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hprod : Real.exp (l * v) * Real.exp (-(l * v)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [Real.cosh_eq, Real.sinh_eq, h1, h2]
  linear_combination hprod

/-- Pointwise identity `2 · (sinh(l v))² = (1 / 2) · (exp(l v) − exp((−l) v))²`. -/
theorem two_mul_sq_sinh_eq_half_sq_exp_sub (l v : ℝ) :
    2 * (Real.sinh (l * v)) ^ 2 =
      (1 / 2 : ℝ) * (Real.exp (l * v) - Real.exp ((-l) * v)) ^ 2 := by
  rw [Real.sinh_eq, neg_mul]
  ring

/-! ### Integrability and exact midpoint-convexity defect / critical-line excess identities -/

/-- Integrability of `(1/2) · (exp(l₁ v) − exp(l₂ v))² · (arcLineInfiniteDyadicProfile k ν v)²`
across `|l₁| < 1/2`, `|l₂| < 1/2` (`k ≥ 2`). -/
theorem integrable_half_sq_exp_sub_exp_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    Integrable (fun v : ℝ =>
      (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  have hmid : |(l₁ + l₂) / 2| < 1 / 2 := by
    calc |(l₁ + l₂) / 2|
        = |l₁ + l₂| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (|l₁| + |l₂|) / 2 := div_le_div_of_nonneg_right (abs_add_le l₁ l₂) (by norm_num)
      _ < 1 / 2 := by linarith
  have heq : (fun v : ℝ =>
      (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ =>
        (1 / 2 : ℝ) *
          (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
          Real.exp (2 * ((l₁ + l₂) / 2) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
    funext v
    have hpt := exp_two_mul_add_div_two_sub l₁ l₂ v
    linear_combination (arcLineInfiniteDyadicProfile k ν v) ^ 2 * hpt.symm
  rw [heq]
  exact (((integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₁).add
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₂)).const_mul _).sub
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hmid)

/-- **Exact midpoint-convexity defect identity on the logarithmic axis `v ∈ ℝ` (`k ≥ 2`):**
For every `|l₁| < 1/2` and `|l₂| < 1/2`,
`((∫ e^{2 l₁ v} Φ_k(v)² dv) + (∫ e^{2 l₂ v} Φ_k(v)² dv)) / 2 − ∫ e^{2 ((l₁ + l₂)/2) v} Φ_k(v)² dv = ∫_ℝ (1/2) (e^{l₁ v} − e^{l₂ v})² Φ_k(v)² dv`. -/
theorem integral_exp_two_mul_sq_midpoint_defect_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    ((∫ v : ℝ, Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) +
        (∫ v : ℝ, Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) / 2 -
      (∫ v : ℝ, Real.exp (2 * ((l₁ + l₂) / 2) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
    ∫ v : ℝ,
      (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hmid : |(l₁ + l₂) / 2| < 1 / 2 := by
    calc |(l₁ + l₂) / 2|
        = |l₁ + l₂| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (|l₁| + |l₂|) / 2 := div_le_div_of_nonneg_right (abs_add_le l₁ l₂) (by norm_num)
      _ < 1 / 2 := by linarith
  have hI1 := integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₁
  have hI2 := integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₂
  have hIm := integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hmid
  have hIsum : Integrable (fun v : ℝ =>
      Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 +
        Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) volume := hI1.add hI2
  have heq : (fun v : ℝ =>
      (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ =>
        (Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) / 2 -
          Real.exp (2 * ((l₁ + l₂) / 2) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
    funext v
    have hpt := exp_two_mul_add_div_two_sub l₁ l₂ v
    linear_combination (arcLineInfiniteDyadicProfile k ν v) ^ 2 * hpt.symm
  rw [heq, integral_sub (hIsum.div_const 2) hIm, integral_div, integral_add hI1 hI2]

/-- **Exact midpoint-convexity defect identity for the strip-weighted `L²((0, ∞), x^{2l} dx)`
Hilbert energy (`k ≥ 2`, `|l₁| < 1/2`, `|l₂| < 1/2`):**
`((∫_{x > 0} x^{2 l₁} V_k(x)² dx) + (∫_{x > 0} x^{2 l₂} V_k(x)² dx)) / 2 − ∫_{x > 0} x^{2 ((l₁ + l₂)/2)} V_k(x)² dx = ∫_ℝ (1/2) (e^{l₁ v} − e^{l₂ v})² Φ_k(v)² dv`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_midpoint_defect_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    ((∫ x in Ioi 0, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) +
        (∫ x in Ioi 0, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) / 2 -
      (∫ x in Ioi 0, x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
    ∫ v : ℝ,
      (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l₁,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l₂,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν ((l₁ + l₂) / 2),
    integral_exp_two_mul_sq_midpoint_defect_eq hk hν hl₁ hl₂]

/-- **Exact `2 sinh²(lv)` excess identity on the logarithmic axis `v ∈ ℝ` (`|l| < 1/2`, `k ≥ 2`):**
`∫_ℝ e^{2lv} Φ_k(v)² dv − ∫_ℝ Φ_k(v)² dv = ∫_ℝ 2 (sinh(lv))² Φ_k(v)² dv`. -/
theorem integral_exp_two_mul_sq_sub_sq_arcLineInfiniteDyadicProfile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
        (∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∫ v : ℝ, 2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hneg : |-l| < 1 / 2 := by simpa using hl
  have hmid := integral_exp_two_mul_sq_midpoint_defect_eq hk hν hl hneg
  rw [integral_exp_two_neg_mul_sq_arcLineInfiniteDyadicProfile k ν l,
    add_neg_cancel, zero_div, mul_zero] at hmid
  have h0 : (∫ v : ℝ, Real.exp (0 * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
    simp
  have h1 : (∫ v : ℝ, Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
      (∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∫ v : ℝ, (1 / 2 : ℝ) * (Real.exp (l * v) - Real.exp (-l * v)) ^ 2 *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by linarith
  rw [h1]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [← two_mul_sq_sinh_eq_half_sq_exp_sub l v]

/-- **Exact `2 sinh²(lv)` excess identity for the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert
energy relative to the critical line `l = 0` (`|l| < 1/2`, `k ≥ 2`):**
`∫_{x > 0} x^{2l} V_k(x)² dx − ∫_{x > 0} V_k(x)² dx = ∫_ℝ 2 (sinh(lv))² Φ_k(v)² dv`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v : ℝ, 2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l,
    setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_eq hk1 ν,
    integral_exp_two_mul_sq_sub_sq_arcLineInfiniteDyadicProfile_eq hk hν hl]

/-! ### Strict midpoint convexity across `(−1/2, 1/2)` and strict uniqueness of the critical-line minimum (`l = 0`) -/

/-- **Strict positivity of the midpoint-convexity defect whenever `l₁ ≠ l₂` in `(−1/2, 1/2)` (`k ≥ 2`):**
For any `|l₁| < 1/2` and `|l₂| < 1/2` with `l₁ ≠ l₂`,
`0 < ∫_ℝ (1/2) · (exp(l₁ v) − exp(l₂ v))² · (arcLineInfiniteDyadicProfile k ν v)² dv`. -/
theorem integral_half_sq_exp_sub_exp_mul_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) (hne : l₁ ≠ l₂) :
    0 < ∫ v : ℝ,
      (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  set f := fun v : ℝ =>
    (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 *
      (arcLineInfiniteDyadicProfile k ν v) ^ 2
  have hnn_pt : ∀ v : ℝ, 0 ≤ f v := fun v => by
    dsimp [f]; positivity
  have hnn : 0 ≤ᵐ[volume] f := Eventually.of_forall hnn_pt
  have hint_nn : 0 ≤ ∫ v : ℝ, f v := integral_nonneg hnn_pt
  rcases hint_nn.eq_or_lt with hzero | hlt
  · exfalso
    have hae : f =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn
        (integrable_half_sq_exp_sub_exp_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₁ hl₂)).mp
        hzero.symm
    have hsq_ae : (fun v : ℝ => (arcLineInfiniteDyadicProfile k ν v) ^ 2) =ᵐ[volume] 0 := by
      filter_upwards [hae, Measure.ae_ne volume (0 : ℝ)] with v hv hv0
      dsimp [f, Pi.zero_apply] at hv ⊢
      have hmul_ne : l₁ * v ≠ l₂ * v := fun h => hne (mul_right_cancel₀ hv0 h)
      have hexp_ne : Real.exp (l₁ * v) - Real.exp (l₂ * v) ≠ 0 :=
        sub_ne_zero.mpr (Real.exp_injective.ne hmul_ne)
      have hcoef_ne : (1 / 2 : ℝ) * (Real.exp (l₁ * v) - Real.exp (l₂ * v)) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hexp_ne)
      exact (mul_eq_zero.mp hv).resolve_left hcoef_ne
    have hpos := integral_sq_arcLineInfiniteDyadicProfile_pos hk hν hpd
    have hf0 : (∫ v : ℝ, (arcLineInfiniteDyadicProfile k ν v) ^ 2) = 0 := by
      rw [integral_congr_ae hsq_ae]
      simp
    linarith
  · exact hlt

/-- **Strict midpoint convexity of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy across
`(−1/2, 1/2)` (`k ≥ 2`):**
For any `|l₁| < 1/2` and `|l₂| < 1/2` with `l₁ ≠ l₂`,
`∫_{x > 0} x^{2 ((l₁ + l₂)/2)} V_k(x)² dx < ((∫_{x > 0} x^{2 l₁} V_k(x)² dx) + (∫_{x > 0} x^{2 l₂} V_k(x)² dx)) / 2`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_midpoint_lt_of_ne
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) (hne : l₁ ≠ l₂) :
    (∫ x in Ioi 0, x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      ((∫ x in Ioi 0, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) +
          (∫ x in Ioi 0, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) / 2 := by
  have hdef := setIntegral_Ioi_rpow_two_mul_sq_midpoint_defect_eq hk hν hl₁ hl₂
  have hpos := integral_half_sq_exp_sub_exp_mul_sq_arcLineInfiniteDyadicProfile_pos
    hk hν hpd hl₁ hl₂ hne
  linarith

/-- **Strict off-critical-line excess of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy
(`|l| < 1/2`, `l ≠ 0`, `k ≥ 2`):**
For every `l ∈ (−1/2, 1/2)` with `l ≠ 0`, strictly
`∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx < ∫_{x > 0} x^{2l} · (arcLineInfiniteDyadicVector k ν x)² dx`. -/
theorem setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_lt_rpow_two_mul_of_ne_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) (hl0 : l ≠ 0) :
    (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hne : l ≠ -l := fun h => hl0 (by linarith)
  have hmid := setIntegral_Ioi_rpow_two_mul_sq_midpoint_lt_of_ne
    hk hν hpd hl (by simpa using hl) hne
  rw [setIntegral_Ioi_rpow_two_neg_mul_sq_arcLineInfiniteDyadicVector hk1 ν l,
    add_neg_cancel, zero_div, mul_zero] at hmid
  have hzero : (∫ x in Ioi 0, x ^ (0 : ℝ) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
    simp
  linarith

/-- **Strict uniqueness of the critical-line minimum (`|l| < 1/2`, `k ≥ 2`):**
Across the entire open critical strip `l ∈ (−1/2, 1/2)`,
`∫_{x > 0} x^{2l} · (arcLineInfiniteDyadicVector k ν x)² dx = ∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx ↔ l = 0`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_eq_sq_iff
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
        (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ↔
      l = 0 := by
  constructor
  · intro heq
    by_contra hl0
    have hlt := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_lt_rpow_two_mul_of_ne_zero
      hk hν hpd hl hl0
    linarith
  · rintro rfl
    simp

/-! ### Scale-independent quadratic `O(l²)` upper bound and stationary first derivative at `l = 0` -/

/-- **Elementary hyperbolic sine bound:**
For every `u ∈ ℝ`, `|sinh u| ≤ |u| · exp |u|`. -/
theorem abs_sinh_le_abs_mul_exp_abs (u : ℝ) :
    |Real.sinh u| ≤ |u| * Real.exp |u| := by
  have h := abs_exp_sub_exp_le_of_abs_le (le_refl |u|) (by simp : |-u| ≤ |u|)
  have hdiff : |u - -u| = 2 * |u| := by
    rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hdiff] at h
  rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Pointwise quadratic-exponential bound on `2 (sinh(lv))²`:
For all `l, v ∈ ℝ`,
`2 · (sinh(l v))² ≤ 128 · l² · exp((2 |l| + 1/4) |v|)`. -/
theorem two_mul_sq_sinh_mul_le_exp (l v : ℝ) :
    2 * (Real.sinh (l * v)) ^ 2 ≤
      128 * l ^ 2 * Real.exp ((2 * |l| + 1 / 4) * |v|) := by
  have hsinh := abs_sinh_le_abs_mul_exp_abs (l * v)
  rw [abs_mul] at hsinh
  have hsq1 : (Real.sinh (l * v)) ^ 2 ≤
      (|l| * |v| * Real.exp (|l| * |v|)) ^ 2 := by
    calc (Real.sinh (l * v)) ^ 2
        = |Real.sinh (l * v)| * |Real.sinh (l * v)| := by rw [← sq, sq_abs]
      _ ≤ (|l| * |v| * Real.exp (|l| * |v|)) * (|l| * |v| * Real.exp (|l| * |v|)) :=
          mul_le_mul hsinh hsinh (abs_nonneg _) (by positivity)
      _ = (|l| * |v| * Real.exp (|l| * |v|)) ^ 2 := (sq _).symm
  have hv8 := abs_le_eight_mul_exp_eighth v
  have hv_sq : |v| ^ 2 ≤ 64 * Real.exp ((1 / 4 : ℝ) * |v|) := by
    calc |v| ^ 2
        = |v| * |v| := sq |v|
      _ ≤ (8 * Real.exp ((1 / 8 : ℝ) * |v|)) * (8 * Real.exp ((1 / 8 : ℝ) * |v|)) :=
          mul_le_mul hv8 hv8 (abs_nonneg v) (by positivity)
      _ = 64 * (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp ((1 / 8 : ℝ) * |v|)) := by ring
      _ = 64 * Real.exp ((1 / 4 : ℝ) * |v|) := by rw [← Real.exp_add]; congr 2; ring
  calc 2 * (Real.sinh (l * v)) ^ 2
      ≤ 2 * (|l| * |v| * Real.exp (|l| * |v|)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq1 (by norm_num)
    _ = 2 * l ^ 2 * |v| ^ 2 * (Real.exp (|l| * |v|) * Real.exp (|l| * |v|)) := by
        rw [mul_pow, mul_pow, sq_abs l, sq (Real.exp _)]; ring
    _ ≤ 2 * l ^ 2 * (64 * Real.exp ((1 / 4 : ℝ) * |v|)) *
          (Real.exp (|l| * |v|) * Real.exp (|l| * |v|)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hv_sq (by positivity)) (by positivity)
    _ = 128 * l ^ 2 *
          (Real.exp ((1 / 4 : ℝ) * |v|) * (Real.exp (|l| * |v|) * Real.exp (|l| * |v|))) := by ring
    _ = 128 * l ^ 2 * Real.exp ((2 * |l| + 1 / 4) * |v|) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

/-- **Scale-independent quadratic `O(l²)` upper bound on the off-critical-line Hilbert energy
excess (`|l| < 1/8`, `k ≥ 2`):**
For every `k ≥ 2` and `|l| < 1/8`,
`∫_{x > 0} x^{2l} (arcLineInfiniteDyadicVector k ν x)² dx − ∫_{x > 0} (arcLineInfiniteDyadicVector k ν x)² dx ≤ (87120000 · (ν.real univ)² / (1/8 − |l|)) · l²`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
      (87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * l ^ 2 := by
  have hl_half : |l| < 1 / 2 := by linarith
  have hcl : 0 < 1 / 4 - 2 * |l| := by linarith
  rw [setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_eq hk hν hl_half]
  set B := 87120000 * (ν.real univ) ^ 2 * l ^ 2
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
      hk hν hl_half (by simpa using hl_half)
  have hmono := integral_mono hInt
    ((integrable_rexp_neg_mul_abs hcl).const_mul B)
    (fun v => ?_)
  · rw [integral_const_mul, integral_rexp_neg_mul_abs hcl] at hmono
    have h2div : 2 / (1 / 4 - 2 * |l|) = 1 / (1 / 8 - |l|) := by
      have hne1 : 1 / 4 - 2 * |l| ≠ 0 := ne_of_gt hcl
      have hne2 : 1 / 8 - |l| ≠ 0 := ne_of_gt (sub_pos.mpr hl)
      rw [div_eq_div_iff hne1 hne2]
      ring
    calc (∫ v : ℝ, 2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
        ≤ B * (2 / (1 / 4 - 2 * |l|)) := hmono
      _ = (87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * l ^ 2 := by
          rw [h2div]; dsimp [B]; ring
  · calc 2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2
        ≤ (128 * l ^ 2 * Real.exp ((2 * |l| + 1 / 4) * |v|)) *
            (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul (two_mul_sq_sinh_mul_le_exp l v)
            (sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v)
            (sq_nonneg _) (by positivity)
      _ = B * (Real.exp ((2 * |l| + 1 / 4) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 4 - 2 * |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-- **Vanishing first-order divided difference at the critical line `l → 0` (`k ≥ 2`):**
`((∫_{x > 0} x^{2l} V_k(x)² dx) − (∫_{x > 0} V_k(x)² dx)) / l → 0` as `l → 0`. -/
theorem tendsto_div_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      ((∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
      (𝓝 0) (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hupper : Tendsto (fun l : ℝ =>
      (87120000 * (ν.real univ) ^ 2 / (1 / 16 : ℝ)) * |l|) (𝓝 0) (𝓝 0) := by
    have h0 : (0 : ℝ) = (87120000 * (ν.real univ) ^ 2 / (1 / 16 : ℝ)) * |(0 : ℝ)| := by simp
    nth_rw 2 [h0]
    exact (continuous_abs.tendsto (0 : ℝ)).const_mul _
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hupper
  have hmem : {l : ℝ | |l| < 1 / 16} ∈ 𝓝 (0 : ℝ) := by
    have : Ioo (-(1 / 16 : ℝ)) (1 / 16) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with l hl
    exact abs_lt.mpr hl
  filter_upwards [hmem] with l (hl16 : |l| < 1 / 16)
  have hl8 : |l| < 1 / 8 := by linarith
  have hl2 : |l| < 1 / 2 := by linarith
  rw [sub_zero, Real.norm_eq_abs, abs_div]
  have hnn : 0 ≤ (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) :=
    sub_nonneg.mpr (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul hk hν hl2)
  rw [abs_of_nonneg hnn]
  rcases eq_or_ne l 0 with rfl | hl0
  · simp
  · have habs_pos : 0 < |l| := abs_pos.mpr hl0
    have hquad := setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_le_sq hk hν hl8
    have hdiv := div_le_div_of_nonneg_right hquad habs_pos.le
    have hcancel : (87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * l ^ 2 / |l| =
        (87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * |l| := by
      rw [← sq_abs l, sq |l|, ← mul_assoc, mul_div_cancel_right₀ _ (ne_of_gt habs_pos)]
    rw [hcancel] at hdiv
    have hden : 87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|) ≤
        87120000 * (ν.real univ) ^ 2 / (1 / 16 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    exact hdiv.trans (mul_le_mul_of_nonneg_right hden habs_pos.le)

/-! ### Master unconditional theorem for strict midpoint convexity and strict uniqueness of the critical-line minimum -/

/-- **Master unconditional theorem for the strict midpoint convexity, `2 sinh²(lv)` excess law,
strict uniqueness of the critical-line minimum `l = 0`, and quadratic `O(l²)` stationary curvature
of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy.** -/
theorem exists_dyadic_criticalLine_strictConvexity_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ l₁ l₂ : ℝ, |l₁| < 1 / 2 → |l₂| < 1 / 2 → l₁ ≠ l₂ →
          (∫ x in Ioi 0, x ^ (2 * ((l₁ + l₂) / 2)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            ((∫ x in Ioi 0, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) +
                (∫ x in Ioi 0, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) / 2) ∧
        (∀ l : ℝ, |l| < 1 / 2 →
          (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) =
            ∫ v : ℝ, 2 * (Real.sinh (l * v)) ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        (∀ l : ℝ, |l| < 1 / 2 → l ≠ 0 →
          (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ l : ℝ, |l| < 1 / 2 →
          ((∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
              (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ↔ l = 0)) ∧
        (∀ l : ℝ, |l| < 1 / 8 →
          (∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
            (87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * l ^ 2) ∧
        Tendsto (fun l : ℝ =>
          ((∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
          (𝓝 0) (𝓝 0) ∧
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
  · exact ⟨fun l₁ l₂ hl₁ hl₂ hne =>
        setIntegral_Ioi_rpow_two_mul_sq_midpoint_lt_of_ne hk hsym hpd hl₁ hl₂ hne,
      fun l hl =>
        setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_eq hk hsym hl,
      fun l hl hl0 =>
        setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_lt_rpow_two_mul_of_ne_zero hk hsym hpd hl hl0,
      fun l hl => setIntegral_Ioi_rpow_two_mul_sq_eq_sq_iff hk hsym hpd hl,
      fun l hl =>
        setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_le_sq hk hsym hl,
      tendsto_div_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero hk hsym,
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
