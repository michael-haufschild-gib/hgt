import GaloisForLFunctions.RHTower.ModularArcDyadicStripWeightedHilbertMinimum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Scale-independent joint two-variable `(l, τ)`-Lipschitz regularity of the critical-strip oscillatory Mellin transform, doubly-exponential Lipschitz tail laws, and strip-weighted `L²` energy Lipschitz regularity

In `ModularArcDyadicStripOscillatoryMellin`, `ModularArcDyadicJointExponentialTail`, and
`ModularArcDyadicStripWeightedHilbertMinimum`, we established the pointwise bounds and tail laws
for the two-variable oscillatory Mellin transform
`M_k(l, τ) = ∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx`
and the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy
`E_k(l) = ∫_{x > 0} x^{2l} · (arcLineInfiniteDyadicVector k ν x)² dx`.

In this module we prove **scale-independent Lipschitz regularity** in both horizontal strip
abscissa `l` and vertical height `τ ∈ ℝ`:

1. **Elementary exponential-difference and cosine-difference kernel bounds
   (`abs_le_inv_mul_exp_mul`, `abs_exp_sub_exp_le_of_abs_le`,
   `abs_exp_mul_sub_exp_mul_le`, `abs_cos_mul_sub_cos_mul_le`,
   `abs_exp_mul_cos_sub_exp_mul_cos_le`, `abs_exp_mul_cos_sub_exp_mul_cos_le_eight_exp`):**
   - For every `c > 0` and `v ∈ ℝ`, `|v| ≤ (1 / c) · exp(c |v|)`.
   - For `|a| ≤ M` and `|b| ≤ M`, `|exp a − exp b| ≤ |a − b| · exp M`.
   - For `|l₁| ≤ σ` and `|l₂| ≤ σ` and all `τ₁, τ₂, v ∈ ℝ`,
     `|e^{l₁ v} cos(τ₁ v) − e^{l₂ v} cos(τ₂ v)| ≤ (|l₁ − l₂| + |τ₁ − τ₂|) · |v| · e^{σ|v|} ≤ 8 (|l₁ − l₂| + |τ₁ − τ₂|) · e^{(σ + 1/8)|v|}`.
2. **Scale-independent joint two-variable `(l, τ)`-Lipschitz regularity of `M_k(l, τ)`
   (`abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_le`,
   `abs_arcLineInfiniteDyadicCosTransform_sub_le`,
   `abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_sub_le`):**
   For every `k ≥ 2`, `σ < 1/8`, `|l₁| ≤ σ`, `|l₂| ≤ σ`, and `τ₁, τ₂ ∈ ℝ`,
   `|M_k(l₁, τ₁) − M_k(l₂, τ₂)| ≤ (13200 · ν.real univ / (1/8 − σ)) · (|l₁ − l₂| + |τ₁ − τ₂|)`
   (with Lipschitz constant completely independent of `k ≥ 2` and `τ₁, τ₂ ∈ ℝ`).
   On the critical line `l = 0`,
   `|arcLineInfiniteDyadicCosTransform k ν τ₁ − arcLineInfiniteDyadicCosTransform k ν τ₂| ≤ 105600 · ν.real univ · |τ₁ − τ₂|`.
3. **Doubly-exponential `O((k^{2^{r₀}})⁻¹)` joint two-variable Lipschitz seminorm tail bound
   (`abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_succ_lipschitz_le`):**
   For the tail difference `Δ_{k, r₀}(l, τ) := M_k(l, τ) − M_{k, r₀ + 1}(l, τ)`,
   `|Δ_{k, r₀}(l₁, τ₁) − Δ_{k, r₀}(l₂, τ₂)| ≤ (52800 · ν.real univ / (1/8 − σ)) · (k^{2^{r₀}})⁻¹ · (|l₁ − l₂| + |τ₁ − τ₂|)`.
4. **Scale-independent Lipschitz regularity of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert
   energy (`abs_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_le`,
   `exists_dyadic_twoVariable_lipschitzRegularity_arcWitness`):**
   For every `k ≥ 2`, `σ < 1/8`, `|l₁| ≤ σ`, and `|l₂| ≤ σ`,
   `|∫_{x > 0} x^{2 l₁} (V_k(x))² dx − ∫_{x > 0} x^{2 l₂} (V_k(x))² dx| ≤ (5445000 · (ν.real univ)² / (1/8 − σ)) · |l₁ − l₂|`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Elementary exponential-difference and cosine-difference kernel bounds -/

/-- **Linear-by-exponential domination (`c > 0`):**
For every `c > 0` and `v ∈ ℝ`, `|v| ≤ (1 / c) · exp(c |v|)`. -/
theorem abs_le_inv_mul_exp_mul {c : ℝ} (hc : 0 < c) (v : ℝ) :
    |v| ≤ (1 / c) * Real.exp (c * |v|) := by
  have h1 : c * |v| ≤ Real.exp (c * |v|) :=
    le_trans (by linarith) (Real.add_one_le_exp (c * |v|))
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
  simpa [one_div, inv_mul_cancel_left₀ (ne_of_gt hc)] using h2

/-- Specialization of `abs_le_inv_mul_exp_mul` at `c = 1/8`:
`|v| ≤ 8 · exp((1/8) |v|)`. -/
theorem abs_le_eight_mul_exp_eighth (v : ℝ) :
    |v| ≤ 8 * Real.exp ((1 / 8 : ℝ) * |v|) := by
  have h := abs_le_inv_mul_exp_mul (by norm_num : (0 : ℝ) < 1 / 8) v
  linarith

/-- Specialization of `abs_le_inv_mul_exp_mul` at `c = 1/4`:
`|v| ≤ 4 · exp((1/4) |v|)`. -/
theorem abs_le_four_mul_exp_quarter (v : ℝ) :
    |v| ≤ 4 * Real.exp ((1 / 4 : ℝ) * |v|) := by
  have h := abs_le_inv_mul_exp_mul (by norm_num : (0 : ℝ) < 1 / 4) v
  linarith

/-- Helper: if `a ≤ b` and `b ≤ M`, then `exp b − exp a ≤ (b − a) · exp M`. -/
private theorem exp_sub_exp_le_of_le {a b M : ℝ} (hab : a ≤ b) (hbM : b ≤ M) :
    Real.exp b - Real.exp a ≤ (b - a) * Real.exp M := by
  have h1 : (a - b) + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp (a - b)
  have h2 : ((a - b) + 1) * Real.exp b ≤ Real.exp (a - b) * Real.exp b :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos b).le
  rw [← Real.exp_add, sub_add_cancel] at h2
  have h3 : Real.exp b - Real.exp a ≤ (b - a) * Real.exp b := by linarith
  exact h3.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbM) (sub_nonneg.mpr hab))

/-- **Elementary exponential Lipschitz bound on `[-M, M]`:**
For any `a, b, M ∈ ℝ` with `|a| ≤ M` and `|b| ≤ M`,
`|exp a − exp b| ≤ |a − b| · exp M`. -/
theorem abs_exp_sub_exp_le_of_abs_le {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |Real.exp a - Real.exp b| ≤ |a - b| * Real.exp M := by
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact exp_sub_exp_le_of_le hab (le_trans (le_abs_self b) hb)
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact exp_sub_exp_le_of_le hba (le_trans (le_abs_self a) ha)

/-- **Horizontal exponential kernel difference bound:**
For any `l₁, l₂, σ, v ∈ ℝ` with `|l₁| ≤ σ` and `|l₂| ≤ σ`,
`|exp(l₁ v) − exp(l₂ v)| ≤ |l₁ − l₂| · |v| · exp(σ |v|)`. -/
theorem abs_exp_mul_sub_exp_mul_le
    {l₁ l₂ σ : ℝ} (hl₁ : |l₁| ≤ σ) (hl₂ : |l₂| ≤ σ) (v : ℝ) :
    |Real.exp (l₁ * v) - Real.exp (l₂ * v)| ≤
      |l₁ - l₂| * |v| * Real.exp (σ * |v|) := by
  have ha : |l₁ * v| ≤ σ * |v| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hl₁ (abs_nonneg v)
  have hb : |l₂ * v| ≤ σ * |v| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hl₂ (abs_nonneg v)
  have h := abs_exp_sub_exp_le_of_abs_le ha hb
  have hdiff : |l₁ * v - l₂ * v| = |l₁ - l₂| * |v| := by
    rw [← sub_mul, abs_mul]
  rwa [hdiff] at h

/-- **Vertical cosine kernel difference bound:**
For any `τ₁, τ₂, v ∈ ℝ`,
`|cos(τ₁ v) − cos(τ₂ v)| ≤ |τ₁ − τ₂| · |v|`. -/
theorem abs_cos_mul_sub_cos_mul_le (τ₁ τ₂ v : ℝ) :
    |Real.cos (τ₁ * v) - Real.cos (τ₂ * v)| ≤ |τ₁ - τ₂| * |v| := by
  have h := Real.abs_cos_sub_cos_le (τ₁ * v) (τ₂ * v)
  have hdiff : |τ₁ * v - τ₂ * v| = |τ₁ - τ₂| * |v| := by
    rw [← sub_mul, abs_mul]
  rwa [hdiff] at h

/-- **Joint two-variable `(l, τ)` kernel difference bound:**
For any `l₁, l₂, σ, τ₁, τ₂, v ∈ ℝ` with `|l₁| ≤ σ` and `|l₂| ≤ σ`,
`|exp(l₁ v) cos(τ₁ v) − exp(l₂ v) cos(τ₂ v)| ≤ (|l₁ − l₂| + |τ₁ − τ₂|) · |v| · exp(σ |v|)`. -/
theorem abs_exp_mul_cos_sub_exp_mul_cos_le
    {l₁ l₂ σ : ℝ} (hl₁ : |l₁| ≤ σ) (hl₂ : |l₂| ≤ σ) (τ₁ τ₂ v : ℝ) :
    |Real.exp (l₁ * v) * Real.cos (τ₁ * v) - Real.exp (l₂ * v) * Real.cos (τ₂ * v)| ≤
      (|l₁ - l₂| + |τ₁ - τ₂|) * |v| * Real.exp (σ * |v|) := by
  have hsplit : Real.exp (l₁ * v) * Real.cos (τ₁ * v) - Real.exp (l₂ * v) * Real.cos (τ₂ * v) =
      (Real.exp (l₁ * v) - Real.exp (l₂ * v)) * Real.cos (τ₁ * v) +
        Real.exp (l₂ * v) * (Real.cos (τ₁ * v) - Real.cos (τ₂ * v)) := by ring
  rw [hsplit]
  have htri := abs_add_le
    ((Real.exp (l₁ * v) - Real.exp (l₂ * v)) * Real.cos (τ₁ * v))
    (Real.exp (l₂ * v) * (Real.cos (τ₁ * v) - Real.cos (τ₂ * v)))
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)] at htri
  have hterm1 : |Real.exp (l₁ * v) - Real.exp (l₂ * v)| * |Real.cos (τ₁ * v)| ≤
      |l₁ - l₂| * |v| * Real.exp (σ * |v|) := by
    calc |Real.exp (l₁ * v) - Real.exp (l₂ * v)| * |Real.cos (τ₁ * v)|
        ≤ (|l₁ - l₂| * |v| * Real.exp (σ * |v|)) * 1 :=
          mul_le_mul (abs_exp_mul_sub_exp_mul_le hl₁ hl₂ v) (Real.abs_cos_le_one _)
            (abs_nonneg _) (by positivity)
      _ = |l₁ - l₂| * |v| * Real.exp (σ * |v|) := mul_one _
  have hexp2 : Real.exp (l₂ * v) ≤ Real.exp (σ * |v|) := by
    refine (le_trans (le_abs_self _) (abs_exp_mul_le_exp_abs_mul l₂ v)).trans ?_
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hl₂ (abs_nonneg v))
  have hterm2 : Real.exp (l₂ * v) * |Real.cos (τ₁ * v) - Real.cos (τ₂ * v)| ≤
      |τ₁ - τ₂| * |v| * Real.exp (σ * |v|) := by
    calc Real.exp (l₂ * v) * |Real.cos (τ₁ * v) - Real.cos (τ₂ * v)|
        ≤ Real.exp (σ * |v|) * (|τ₁ - τ₂| * |v|) :=
          mul_le_mul hexp2 (abs_cos_mul_sub_cos_mul_le τ₁ τ₂ v)
            (abs_nonneg _) (Real.exp_pos _).le
      _ = |τ₁ - τ₂| * |v| * Real.exp (σ * |v|) := by ring
  linarith

/-- **Pure-exponential joint two-variable `(l, τ)` kernel difference bound:**
For any `l₁, l₂, σ, τ₁, τ₂, v ∈ ℝ` with `|l₁| ≤ σ` and `|l₂| ≤ σ`,
`|exp(l₁ v) cos(τ₁ v) − exp(l₂ v) cos(τ₂ v)| ≤ 8 (|l₁ − l₂| + |τ₁ − τ₂|) · exp((σ + 1/8) |v|)`. -/
theorem abs_exp_mul_cos_sub_exp_mul_cos_le_eight_exp
    {l₁ l₂ σ : ℝ} (hl₁ : |l₁| ≤ σ) (hl₂ : |l₂| ≤ σ) (τ₁ τ₂ v : ℝ) :
    |Real.exp (l₁ * v) * Real.cos (τ₁ * v) - Real.exp (l₂ * v) * Real.cos (τ₂ * v)| ≤
      8 * (|l₁ - l₂| + |τ₁ - τ₂|) * Real.exp ((σ + 1 / 8) * |v|) := by
  have h1 := abs_exp_mul_cos_sub_exp_mul_cos_le hl₁ hl₂ τ₁ τ₂ v
  have h2 := abs_le_eight_mul_exp_eighth v
  have hsum_nn : 0 ≤ |l₁ - l₂| + |τ₁ - τ₂| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |Real.exp (l₁ * v) * Real.cos (τ₁ * v) - Real.exp (l₂ * v) * Real.cos (τ₂ * v)|
      ≤ (|l₁ - l₂| + |τ₁ - τ₂|) * |v| * Real.exp (σ * |v|) := h1
    _ ≤ (|l₁ - l₂| + |τ₁ - τ₂|) * (8 * Real.exp ((1 / 8 : ℝ) * |v|)) * Real.exp (σ * |v|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hsum_nn) (Real.exp_pos _).le
    _ = 8 * (|l₁ - l₂| + |τ₁ - τ₂|) *
          (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (σ * |v|)) := by ring
    _ = 8 * (|l₁ - l₂| + |τ₁ - τ₂|) * Real.exp ((σ + 1 / 8) * |v|) := by
        rw [← Real.exp_add]; congr 2; ring

/-! ### Scale-independent joint two-variable `(l, τ)`-Lipschitz regularity of the critical-strip oscillatory Mellin transform -/

/-- **Scale-independent joint two-variable `(l, τ)`-Lipschitz bound for the critical-strip
oscillatory Mellin transform (`k ≥ 2`, `σ < 1/8`):**
For every `k ≥ 2`, `σ < 1/8`, `|l₁| ≤ σ`, `|l₂| ≤ σ`, and `τ₁, τ₂ ∈ ℝ`,
`|∫_{x > 0} x^{l₁ − 1/2} cos(τ₁ log x) V_k(x) dx − ∫_{x > 0} x^{l₂ − 1/2} cos(τ₂ log x) V_k(x) dx| ≤ (13200 · ν.real univ / (1/8 − σ)) · (|l₁ − l₂| + |τ₁ − τ₂|)`. -/
theorem abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {σ l₁ l₂ : ℝ} (hσ : σ < 1 / 8)
    (hl₁ : |l₁| ≤ σ) (hl₂ : |l₂| ≤ σ) (τ₁ τ₂ : ℝ) :
    |(∫ x in Ioi 0, x ^ (l₁ - 1 / 2) * Real.cos (τ₁ * Real.log x) *
          arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi 0, x ^ (l₂ - 1 / 2) * Real.cos (τ₂ * Real.log x) *
          arcLineInfiniteDyadicVector k ν x)| ≤
      (13200 * ν.real univ / (1 / 8 - σ)) * (|l₁ - l₂| + |τ₁ - τ₂|) := by
  have hk1 : 1 ≤ k := by omega
  have hl₁_half : |l₁| < 1 / 2 := by linarith
  have hl₂_half : |l₂| < 1 / 2 := by linarith
  have hcσ : 0 < 1 / 8 - σ := sub_pos.mpr hσ
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l₁ τ₁,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l₂ τ₂,
    ← integral_sub
      (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₁_half τ₁)
      (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₂_half τ₂)]
  set B := 6600 * ν.real univ * (|l₁ - l₂| + |τ₁ - τ₂|)
  have h1 := abs_integral_le_integral_abs
    (μ := volume)
    (f := fun v : ℝ =>
      Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v)
  have h2 := integral_mono
    (((integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₁_half τ₁).sub
      (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₂_half τ₂)).abs)
    ((integrable_rexp_neg_mul_abs hcσ).const_mul B)
    (fun v => ?_)
  · dsimp only [Pi.sub_apply] at h2
    rw [integral_const_mul, integral_rexp_neg_mul_abs hcσ] at h2
    calc |∫ v : ℝ,
            Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v|
        ≤ ∫ v : ℝ,
            |Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v| := h1
      _ ≤ B * (2 / (1 / 8 - σ)) := h2
      _ = (13200 * ν.real univ / (1 / 8 - σ)) * (|l₁ - l₂| + |τ₁ - τ₂|) := by
          dsimp [B]; ring
  · dsimp only [Pi.sub_apply]
    rw [← sub_mul, abs_mul]
    calc |Real.exp (l₁ * v) * Real.cos (τ₁ * v) - Real.exp (l₂ * v) * Real.cos (τ₂ * v)| *
          |arcLineInfiniteDyadicProfile k ν v|
        ≤ (8 * (|l₁ - l₂| + |τ₁ - τ₂|) * Real.exp ((σ + 1 / 8) * |v|)) *
            (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul (abs_exp_mul_cos_sub_exp_mul_cos_le_eight_exp hl₁ hl₂ τ₁ τ₂ v)
            (abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v)
            (abs_nonneg _) (by positivity)
      _ = B * (Real.exp ((σ + 1 / 8) * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 8 - σ) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-- **Global scale-independent Lipschitz continuity of `arcLineInfiniteDyadicCosTransform k ν` on
the critical line `τ ∈ ℝ` (`k ≥ 2`):**
For all `τ₁, τ₂ ∈ ℝ`,
`|arcLineInfiniteDyadicCosTransform k ν τ₁ − arcLineInfiniteDyadicCosTransform k ν τ₂| ≤ 105600 · ν.real univ · |τ₁ − τ₂|`. -/
theorem abs_arcLineInfiniteDyadicCosTransform_lipschitz_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ₁ τ₂ : ℝ) :
    |arcLineInfiniteDyadicCosTransform k ν τ₁ -
        arcLineInfiniteDyadicCosTransform k ν τ₂| ≤
      105600 * ν.real univ * |τ₁ - τ₂| := by
  rw [← setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq hk hν τ₁,
    ← setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq hk hν τ₂]
  have h := abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_le
    hk hν (by norm_num : (0 : ℝ) < 1 / 8)
    (by simp : |(0 : ℝ)| ≤ 0) (by simp : |(0 : ℝ)| ≤ 0) τ₁ τ₂
  simp only [zero_sub, sub_zero, abs_zero, zero_add] at h ⊢
  linarith

/-- **Scale-independent horizontal Lipschitz continuity of the real-axis Mellin integral on
`|l| ≤ σ < 1/8` (`k ≥ 2`):**
For every `σ < 1/8`, `|l₁| ≤ σ`, and `|l₂| ≤ σ`,
`|∫_{x > 0} x^{l₁ − 1/2} V_k(x) dx − ∫_{x > 0} x^{l₂ − 1/2} V_k(x) dx| ≤ (13200 · ν.real univ / (1/8 − σ)) · |l₁ − l₂|`. -/
theorem abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_sub_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {σ l₁ l₂ : ℝ} (hσ : σ < 1 / 8)
    (hl₁ : |l₁| ≤ σ) (hl₂ : |l₂| ≤ σ) :
    |(∫ x in Ioi 0, x ^ (l₁ - 1 / 2) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi 0, x ^ (l₂ - 1 / 2) * arcLineInfiniteDyadicVector k ν x)| ≤
      (13200 * ν.real univ / (1 / 8 - σ)) * |l₁ - l₂| := by
  rw [← setIntegral_Ioi_rpow_mul_cos_zero_log_mul_arcLineInfiniteDyadicVector k ν l₁,
    ← setIntegral_Ioi_rpow_mul_cos_zero_log_mul_arcLineInfiniteDyadicVector k ν l₂]
  have h := abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_le
    hk hν hσ hl₁ hl₂ 0 0
  simpa using h

/-! ### Doubly-exponential `O((k^{2^{r₀}})⁻¹)` joint two-variable Lipschitz seminorm tail bound -/

/-- **Doubly-exponential `O((k^{2^{r₀}})⁻¹)` joint `(l, τ)`-Lipschitz tail bound (`k ≥ 2`, `σ < 1/8`):**
Let `Δ_{k, r₀}(l, τ) := ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_{k, r₀+1}(x) dx`.
For every `r₀ ∈ ℕ`, `σ < 1/8`, `|l₁| ≤ σ`, `|l₂| ≤ σ`, and `τ₁, τ₂ ∈ ℝ`,
`|Δ_{k, r₀}(l₁, τ₁) − Δ_{k, r₀}(l₂, τ₂)| ≤ (52800 · ν.real univ / (1/8 − σ)) · (k^{2^{r₀}})⁻¹ · (|l₁ − l₂| + |τ₁ − τ₂|)`. -/
theorem abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_succ_lipschitz_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {σ l₁ l₂ : ℝ} (hσ : σ < 1 / 8)
    (hl₁ : |l₁| ≤ σ) (hl₂ : |l₂| ≤ σ) (τ₁ τ₂ : ℝ) :
    |((∫ x in Ioi 0, x ^ (l₁ - 1 / 2) * Real.cos (τ₁ * Real.log x) *
            arcLineInfiniteDyadicVector k ν x) -
          (∫ x in Ioi 0, x ^ (l₁ - 1 / 2) * Real.cos (τ₁ * Real.log x) *
            arcLineDyadicTowerVector k (r₀ + 1) ν x)) -
        ((∫ x in Ioi 0, x ^ (l₂ - 1 / 2) * Real.cos (τ₂ * Real.log x) *
            arcLineInfiniteDyadicVector k ν x) -
          (∫ x in Ioi 0, x ^ (l₂ - 1 / 2) * Real.cos (τ₂ * Real.log x) *
            arcLineDyadicTowerVector k (r₀ + 1) ν x))| ≤
      (52800 * ν.real univ / (1 / 8 - σ)) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
        (|l₁ - l₂| + |τ₁ - τ₂|) := by
  have hk1 : 1 ≤ k := by omega
  have hl₁_half : |l₁| < 1 / 2 := by linarith
  have hl₂_half : |l₂| < 1 / 2 := by linarith
  have hcσ : 0 < 1 / 8 - σ := sub_pos.mpr hσ
  have hI1 : Integrable (fun v : ℝ =>
      Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v) :=
    (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₁_half τ₁).sub
      (integrable_exp_mul_cos_mul_arcLineDyadicTowerProfile hk (r₀ + 1) hν hl₁_half τ₁)
  have hI2 : Integrable (fun v : ℝ =>
      Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v) :=
    (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₂_half τ₂).sub
      (integrable_exp_mul_cos_mul_arcLineDyadicTowerProfile hk (r₀ + 1) hν hl₂_half τ₂)
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l₁ τ₁,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_eq_profile hk1 (r₀ + 1) ν l₁ τ₁,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l₂ τ₂,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_eq_profile hk1 (r₀ + 1) ν l₂ τ₂,
    ← integral_sub
      (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₁_half τ₁)
      (integrable_exp_mul_cos_mul_arcLineDyadicTowerProfile hk (r₀ + 1) hν hl₁_half τ₁),
    ← integral_sub
      (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl₂_half τ₂)
      (integrable_exp_mul_cos_mul_arcLineDyadicTowerProfile hk (r₀ + 1) hν hl₂_half τ₂),
    ← integral_sub hI1 hI2]
  set B := 26400 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (|l₁ - l₂| + |τ₁ - τ₂|)
  have h1 := abs_integral_le_integral_abs
    (μ := volume)
    (f := fun v : ℝ =>
      (Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v) -
        (Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v))
  have h2 := integral_mono ((hI1.sub hI2).abs)
    ((integrable_rexp_neg_mul_abs hcσ).const_mul B)
    (fun v => ?_)
  · dsimp only [Pi.sub_apply] at h2
    rw [integral_const_mul, integral_rexp_neg_mul_abs hcσ] at h2
    calc |∫ v : ℝ,
            (Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
                Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v) -
              (Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v -
                Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v)|
        ≤ ∫ v : ℝ,
            |(Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
                Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v) -
              (Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v -
                Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v)| := h1
      _ ≤ B * (2 / (1 / 8 - σ)) := h2
      _ = (52800 * ν.real univ / (1 / 8 - σ)) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
            (|l₁ - l₂| + |τ₁ - τ₂|) := by dsimp [B]; ring
  · dsimp only [Pi.sub_apply]
    have hfac :
        (Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineInfiniteDyadicProfile k ν v -
            Real.exp (l₁ * v) * Real.cos (τ₁ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v) -
          (Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineInfiniteDyadicProfile k ν v -
            Real.exp (l₂ * v) * Real.cos (τ₂ * v) * arcLineDyadicTowerProfile k (r₀ + 1) ν v) =
        (Real.exp (l₁ * v) * Real.cos (τ₁ * v) - Real.exp (l₂ * v) * Real.cos (τ₂ * v)) *
          (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v) := by ring
    rw [hfac, abs_mul]
    have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
    calc |Real.exp (l₁ * v) * Real.cos (τ₁ * v) - Real.exp (l₂ * v) * Real.cos (τ₂ * v)| *
          |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k (r₀ + 1) ν v|
        ≤ (8 * (|l₁ - l₂| + |τ₁ - τ₂|) * Real.exp ((σ + 1 / 8) * |v|)) *
            (3300 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
              Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul (abs_exp_mul_cos_sub_exp_mul_cos_le_eight_exp hl₁ hl₂ τ₁ τ₂ v)
            (abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk r₀ hν v)
            (abs_nonneg _) (by positivity)
      _ = B * (Real.exp ((σ + 1 / 8) * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 8 - σ) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-! ### Scale-independent Lipschitz regularity of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert energy -/

/-- **Scale-independent Lipschitz regularity of the strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert
energy across `|l| ≤ σ < 1/8` (`k ≥ 2`):**
For every `k ≥ 2`, `σ < 1/8`, `|l₁| ≤ σ`, and `|l₂| ≤ σ`,
`|∫_{x > 0} x^{2 l₁} (arcLineInfiniteDyadicVector k ν x)² dx − ∫_{x > 0} x^{2 l₂} (arcLineInfiniteDyadicVector k ν x)² dx| ≤ (5445000 · (ν.real univ)² / (1/8 − σ)) · |l₁ − l₂|`. -/
theorem abs_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {σ l₁ l₂ : ℝ} (hσ : σ < 1 / 8)
    (hl₁ : |l₁| ≤ σ) (hl₂ : |l₂| ≤ σ) :
    |(∫ x in Ioi 0, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi 0, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2)| ≤
      (5445000 * (ν.real univ) ^ 2 / (1 / 8 - σ)) * |l₁ - l₂| := by
  have hk1 : 1 ≤ k := by omega
  have hl₁_half : |l₁| < 1 / 2 := by linarith
  have hl₂_half : |l₂| < 1 / 2 := by linarith
  have hcσ : 0 < 1 / 4 - 2 * σ := by linarith
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l₁,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l₂,
    ← integral_sub
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₁_half)
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₂_half)]
  set B := 5445000 * (ν.real univ) ^ 2 * |l₁ - l₂|
  have h1 := abs_integral_le_integral_abs
    (μ := volume)
    (f := fun v : ℝ =>
      Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
        Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
  have h2 := integral_mono
    (((integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₁_half).sub
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₂_half)).abs)
    ((integrable_rexp_neg_mul_abs hcσ).const_mul B)
    (fun v => ?_)
  · dsimp only [Pi.sub_apply] at h2
    rw [integral_const_mul, integral_rexp_neg_mul_abs hcσ] at h2
    have h2div : 2 / (1 / 4 - 2 * σ) = 1 / (1 / 8 - σ) := by
      have hne1 : 1 / 4 - 2 * σ ≠ 0 := ne_of_gt hcσ
      have hne2 : 1 / 8 - σ ≠ 0 := ne_of_gt (sub_pos.mpr hσ)
      rw [div_eq_div_iff hne1 hne2]
      ring
    calc |∫ v : ℝ,
            Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
              Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2|
        ≤ ∫ v : ℝ,
            |Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
              Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2| := h1
      _ ≤ B * (2 / (1 / 4 - 2 * σ)) := h2
      _ = (5445000 * (ν.real univ) ^ 2 / (1 / 8 - σ)) * |l₁ - l₂| := by
          rw [h2div]; dsimp [B]; ring
  · dsimp only [Pi.sub_apply]
    rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (arcLineInfiniteDyadicProfile k ν v))]
    have h2l₁ : |2 * l₁| ≤ 2 * σ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have h2l₂ : |2 * l₂| ≤ 2 * σ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hexp_diff : |Real.exp (2 * l₁ * v) - Real.exp (2 * l₂ * v)| ≤
        8 * |l₁ - l₂| * Real.exp ((2 * σ + 1 / 4) * |v|) := by
      have hsub := abs_exp_mul_sub_exp_mul_le h2l₁ h2l₂ v
      have h2sub : |2 * l₁ - 2 * l₂| = 2 * |l₁ - l₂| := by
        rw [show 2 * l₁ - 2 * l₂ = 2 * (l₁ - l₂) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [h2sub] at hsub
      have hv4 := abs_le_four_mul_exp_quarter v
      calc |Real.exp (2 * l₁ * v) - Real.exp (2 * l₂ * v)|
          ≤ 2 * |l₁ - l₂| * |v| * Real.exp ((2 * σ) * |v|) := hsub
        _ ≤ 2 * |l₁ - l₂| * (4 * Real.exp ((1 / 4 : ℝ) * |v|)) *
              Real.exp ((2 * σ) * |v|) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hv4 (by positivity)) (Real.exp_pos _).le
        _ = 8 * |l₁ - l₂| *
              (Real.exp ((1 / 4 : ℝ) * |v|) * Real.exp ((2 * σ) * |v|)) := by ring
        _ = 8 * |l₁ - l₂| * Real.exp ((2 * σ + 1 / 4) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    calc |Real.exp (2 * l₁ * v) - Real.exp (2 * l₂ * v)| *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2
        ≤ (8 * |l₁ - l₂| * Real.exp ((2 * σ + 1 / 4) * |v|)) *
            (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul hexp_diff (sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v)
            (sq_nonneg _) (by positivity)
      _ = B * (Real.exp ((2 * σ + 1 / 4) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 4 - 2 * σ) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-! ### Master unconditional theorem for two-variable `(l, τ)`-Lipschitz regularity -/

/-- **Master unconditional theorem for the scale-independent two-variable `(l, τ)`-Lipschitz
regularity of the critical-strip oscillatory Mellin transform, doubly-exponential Lipschitz tail
approximation, and strip-weighted `L²` Hilbert energy Lipschitz regularity.** -/
theorem exists_dyadic_twoVariable_lipschitzRegularity_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ σ l₁ l₂ : ℝ, σ < 1 / 8 → |l₁| ≤ σ → |l₂| ≤ σ → ∀ τ₁ τ₂ : ℝ,
          |(∫ x in Ioi 0, x ^ (l₁ - 1 / 2) * Real.cos (τ₁ * Real.log x) *
                arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi 0, x ^ (l₂ - 1 / 2) * Real.cos (τ₂ * Real.log x) *
                arcLineInfiniteDyadicVector k ν x)| ≤
            (13200 * ν.real univ / (1 / 8 - σ)) * (|l₁ - l₂| + |τ₁ - τ₂|)) ∧
        (∀ τ₁ τ₂ : ℝ,
          |arcLineInfiniteDyadicCosTransform k ν τ₁ -
              arcLineInfiniteDyadicCosTransform k ν τ₂| ≤
            105600 * ν.real univ * |τ₁ - τ₂|) ∧
        (∀ r₀ : ℕ, ∀ σ l₁ l₂ : ℝ, σ < 1 / 8 → |l₁| ≤ σ → |l₂| ≤ σ → ∀ τ₁ τ₂ : ℝ,
          |((∫ x in Ioi 0, x ^ (l₁ - 1 / 2) * Real.cos (τ₁ * Real.log x) *
                  arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi 0, x ^ (l₁ - 1 / 2) * Real.cos (τ₁ * Real.log x) *
                  arcLineDyadicTowerVector k (r₀ + 1) ν x)) -
              ((∫ x in Ioi 0, x ^ (l₂ - 1 / 2) * Real.cos (τ₂ * Real.log x) *
                  arcLineInfiniteDyadicVector k ν x) -
                (∫ x in Ioi 0, x ^ (l₂ - 1 / 2) * Real.cos (τ₂ * Real.log x) *
                  arcLineDyadicTowerVector k (r₀ + 1) ν x))| ≤
            (52800 * ν.real univ / (1 / 8 - σ)) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
              (|l₁ - l₂| + |τ₁ - τ₂|)) ∧
        (∀ σ l₁ l₂ : ℝ, σ < 1 / 8 → |l₁| ≤ σ → |l₂| ≤ σ →
          |(∫ x in Ioi 0, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi 0, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2)| ≤
            (5445000 * (ν.real univ) ^ 2 / (1 / 8 - σ)) * |l₁ - l₂|) ∧
        (∀ l : ℝ, |l| < 1 / 2 →
          0 < (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
          (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2) ≤
            ∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
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
  · exact ⟨fun σ l₁ l₂ hσ hl₁ hl₂ τ₁ τ₂ =>
        abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_le
          hk hsym hσ hl₁ hl₂ τ₁ τ₂,
      fun τ₁ τ₂ => abs_arcLineInfiniteDyadicCosTransform_lipschitz_le hk hsym τ₁ τ₂,
      fun r₀ σ l₁ l₂ hσ hl₁ hl₂ τ₁ τ₂ =>
        abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_sub_succ_lipschitz_le
          hk r₀ hsym hσ hl₁ hl₂ τ₁ τ₂,
      fun σ l₁ l₂ hσ hl₁ hl₂ =>
        abs_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_le
          hk hsym hσ hl₁ hl₂,
      fun l hl => ⟨setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hsym hpd,
        setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul hk hsym hl⟩,
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
