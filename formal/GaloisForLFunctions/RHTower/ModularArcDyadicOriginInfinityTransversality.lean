import GaloisForLFunctions.RHTower.ModularArcDyadicOriginInfinityEquipartition

/-!
# Sector monotonicity, imbalance–excess dominance, and critical-line transversality of the origin–infinity dyadic Hilbert energy

In `ModularArcDyadicOriginInfinityEquipartition`, we decomposed the strip-weighted Hilbert energy
`E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx` into the origin sector `E_k^{(0, 1]}(l)` (`Ioc 0 1`) and
the infinity sector `E_k^{(1, ∞)}(l)` (`Ioi 1`), proved the `2 sinh(2lv)` imbalance identity
`Δ_k(l) := E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l) = ∫_{v > 0} 2 sinh(2lv) (Φ_k(v))² dv`, and showed that
`E_k^{(0, 1]}(l) = E_k^{(1, ∞)}(l) ↔ l = 0` across `|l| < 1/2`.

In this module we establish the **strict monotonicity** of both half-line energies and of the
origin–infinity imbalance `Δ_k(l)` across `(−1/2, 1/2)`, the **exact dominance of the
origin–infinity imbalance `|Δ_k(l)|` over the critical-line excess `E_k(l) − E_k(0)`**, and the
**strictly positive transversal first derivative** of `Δ_k(l)` (and opposite non-zero derivatives of
the two half-line sectors) at the critical line `l = 0`:

1. **Strict monotonicity of `E_k^{(1, ∞)}(l)`, `E_k^{(0, 1]}(l)`, and `Δ_k(l)` across `(−1/2, 1/2)`
   (`setIntegral_Ioi_one_rpow_two_mul_sq_lt_of_lt`,
   `setIntegral_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt`,
   `setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt`,
   `setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq_iff`):**
   For every `−1/2 < l₁ < l₂ < 1/2`:
   - `E_k^{(1, ∞)}(l₁) < E_k^{(1, ∞)}(l₂)` (strictly increasing on `(1, ∞)`),
   - `E_k^{(0, 1]}(l₂) < E_k^{(0, 1]}(l₁)` (strictly decreasing on `(0, 1]`),
   - `Δ_k(l₁) < Δ_k(l₂)` (strictly increasing imbalance across `(−1/2, 1/2)`), and hence
     `Δ_k(l₁) = Δ_k(l₂) ↔ l₁ = l₂` on `(−1/2, 1/2)`.
2. **Exact imbalance–excess gap identity and strict dominance `0 < E_k(l) − E_k(0) < |Δ_k(l)|`
   (`abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq`,
   `abs_imbalance_sub_excess_eq_two_mul_origin_depletion`,
   `setIntegral_Ioi_rpow_two_mul_sq_sub_sq_lt_abs_imbalance_of_ne_zero`):**
   - For every `|l| < 1/2`,
     `|Δ_k(l)| − (E_k(l) − E_k(0)) = 2 (E_k^{(0, 1]}(0) − E_k^{(0, 1]}(|l|)) = ∫_{v > 0} 2(1 − e^{−2|l|v}) (Φ_k(v))² dv ≥ 0`.
   - Whenever `l ∈ (−1/2, 1/2)` with `l ≠ 0`, strictly
     `0 < E_k(l) − E_k(0) < |E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)|`.
3. **Sector linear-Taylor positivity, quadratic `O(l²)` remainder bounds, and transversal
   critical-line derivatives at `l = 0`
   (`integrableOn_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile`,
   `setIntegral_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile_pos`,
   `two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioi_one`,
   `abs_imbalance_sub_four_mul_le_excess`,
   `tendsto_div_setIntegral_Ioi_one_sub_sq_nhds_zero`,
   `tendsto_div_setIntegral_Ioc_zero_one_sub_sq_nhds_zero`,
   `tendsto_div_imbalance_nhds_zero`,
   `exists_dyadic_originInfinity_transversality_arcWitness`):**
   - Across `|l| < 1/2`, both sector linear Taylor remainders are non-negative and sum to the
     total critical-line excess `E_k(l) − E_k(0)`:
     `0 ≤ E_k^{(1, ∞)}(l) − E_k^{(1, ∞)}(0) − 2l ∫_{v > 0} v (Φ_k(v))² dv ≤ E_k(l) − E_k(0)` and
     `0 ≤ E_k^{(0, 1]}(l) − E_k^{(0, 1]}(0) + 2l ∫_{v > 0} v (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`.
   - Consequently `|Δ_k(l) − 4l ∫_{v > 0} v (Φ_k(v))² dv| ≤ E_k(l) − E_k(0) ≤ (87120000 · (ν.real univ)² / (1/8 − |l|)) · l²`
     for `|l| < 1/8`, and as `l → 0`:
     - `(E_k^{(1, ∞)}(l) − E_k^{(1, ∞)}(0)) / l → 2 ∫_{v > 0} v (Φ_k(v))² dv > 0`,
     - `(E_k^{(0, 1]}(l) − E_k^{(0, 1]}(0)) / l → −2 ∫_{v > 0} v (Φ_k(v))² dv < 0`,
     - `(E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)) / l → 4 ∫_{v > 0} v (Φ_k(v))² dv > 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Strict monotonicity of the half-line energies and of the origin–infinity imbalance across `(−1/2, 1/2)` -/

/-- **Infinity-sector difference identity (`|l₁| < 1/2`, `|l₂| < 1/2`, `k ≥ 2`):**
`∫_{x > 1} x^{2 l₂} (V_k(x))² dx − ∫_{x > 1} x^{2 l₁} (V_k(x))² dx = ∫_{v > 0} (e^{2 l₂ v} − e^{2 l₁ v}) (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_one_rpow_two_mul_sq_sub_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      ∫ v in Ioi (0 : ℝ),
        (Real.exp (2 * l₂ * v) - Real.exp (2 * l₁ * v)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l₂,
    setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l₁,
    ← integral_sub
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₂).integrableOn
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₁).integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  ring

/-- **Strict monotonicity (increasing) of the infinity-sector Hilbert energy on `(−1/2, 1/2)`:**
Whenever `−1/2 < l₁ < l₂ < 1/2`,
`∫_{x > 1} x^{2 l₁} (V_k(x))² dx < ∫_{x > 1} x^{2 l₂} (V_k(x))² dx`. -/
theorem setIntegral_Ioi_one_rpow_two_mul_sq_lt_of_lt
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) (hlt : l₁ < l₂) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      ∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  rw [← sub_pos, setIntegral_Ioi_one_rpow_two_mul_sq_sub_eq hk hν hl₁ hl₂]
  have hf_int : IntegrableOn (fun v : ℝ => (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) :=
    (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn
  have hwf_int : IntegrableOn
      (fun v : ℝ =>
        (Real.exp (2 * l₂ * v) - Real.exp (2 * l₁ * v)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) := by
    have heq : (fun v : ℝ =>
        (Real.exp (2 * l₂ * v) - Real.exp (2 * l₁ * v)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ =>
          Real.exp (2 * l₂ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
            Real.exp (2 * l₁ * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
      funext v; ring
    rw [heq]
    exact (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₂).integrableOn.sub
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl₁).integrableOn
  exact setIntegral_Ioi_pos_of_pos_mul hf_int hwf_int
    (fun _ _ => sq_nonneg _)
    (fun v hv => sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (by linarith) hv)))
    (setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos)

/-- **Strict monotonicity (decreasing) of the origin-sector Hilbert energy on `(−1/2, 1/2)`:**
Whenever `−1/2 < l₁ < l₂ < 1/2`,
`∫_{x ∈ (0, 1]} x^{2 l₂} (V_k(x))² dx < ∫_{x ∈ (0, 1]} x^{2 l₁} (V_k(x))² dx`. -/
theorem setIntegral_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) (hlt : l₁ < l₂) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν l₂,
    setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν l₁]
  exact setIntegral_Ioi_one_rpow_two_mul_sq_lt_of_lt hk hν hpos
    (by simpa using hl₂) (by simpa using hl₁) (by linarith)

/-- **Strict monotonicity (increasing) of the origin–infinity energy imbalance across `(−1/2, 1/2)`:**
Whenever `−1/2 < l₁ < l₂ < 1/2`,
`E_k^{(1, ∞)}(l₁) − E_k^{(0, 1]}(l₁) < E_k^{(1, ∞)}(l₂) − E_k^{(0, 1]}(l₂)`. -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) (hlt : l₁ < l₂) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have h1 := setIntegral_Ioi_one_rpow_two_mul_sq_lt_of_lt hk hν hpos hl₁ hl₂ hlt
  have h2 := setIntegral_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt hk hν hpos hl₁ hl₂ hlt
  linarith

/-- **Injectivity characterization of the origin–infinity energy imbalance across `(−1/2, 1/2)`:**
For all `l₁, l₂ ∈ (−1/2, 1/2)`,
`E_k^{(1, ∞)}(l₁) − E_k^{(0, 1]}(l₁) = E_k^{(1, ∞)}(l₂) − E_k^{(0, 1]}(l₂) ↔ l₁ = l₂`. -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq_iff
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l₁ l₂ : ℝ} (hl₁ : |l₁| < 1 / 2) (hl₂ : |l₂| < 1 / 2) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ↔
      l₁ = l₂ := by
  constructor
  · intro heq
    rcases lt_trichotomy l₁ l₂ with hlt | rfl | hgt
    · exact absurd heq
        (setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt hk hν hpos hl₁ hl₂ hlt).ne
    · rfl
    · exact absurd heq.symm
        (setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt hk hν hpos hl₂ hl₁ hgt).ne
  · rintro rfl
    rfl

/-! ### Exact imbalance–excess gap identity and strict dominance `0 < E_k(l) − E_k(0) < |Δ_k(l)|` -/

/-- **Odd reflection symmetry `l ↦ −l` of the origin–infinity energy imbalance (`k ≥ 1`):**
`E_k^{(1, ∞)}(−l) − E_k^{(0, 1]}(−l) = −(E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l))`. -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_neg_mul_sq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi (1 : ℝ), x ^ (2 * (-l)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * (-l)) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
      -((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  have h1 := setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk ν l
  have h2 := setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk ν (-l)
  rw [neg_neg] at h2
  linarith

/-- **Absolute-value reduction `l ↦ |l|` for the magnitude of the origin–infinity energy imbalance
(`|l| < 1/2`, `k ≥ 2`):**
`|E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)| = E_k^{(1, ∞)}(|l|) − E_k^{(0, 1]}(|l|)`. -/
theorem abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)| =
      (∫ x in Ioi (1 : ℝ), x ^ (2 * |l|) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * |l|) * (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have hnn : 0 ≤ (∫ x in Ioi (1 : ℝ), x ^ (2 * |l|) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * |l|) * (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
    rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hν (by simpa using hl)]
    refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
    have hv0 : 0 ≤ v := le_of_lt hv
    have h0 : 0 ≤ 2 * |l| * v := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr h0)) (sq_nonneg _)
  rcases le_total 0 l with hl0 | hl0
  · rw [abs_of_nonneg hl0] at hnn ⊢
    exact abs_of_nonneg hnn
  · rw [abs_of_nonpos hl0] at hnn ⊢
    rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_neg_mul_sq hk1 ν l] at hnn ⊢
    rw [← abs_neg, abs_of_nonneg hnn]

/-- **Exact Imbalance–Excess Gap Identity (`|l| < 1/2`, `k ≥ 2`):**
For every `l ∈ (−1/2, 1/2)`,
`|E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)| − (E_k(l) − E_k(0)) = 2 (E_k^{(0, 1]}(0) − E_k^{(0, 1]}(|l|))`. -/
theorem abs_imbalance_sub_excess_eq_two_mul_origin_depletion
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)| -
      ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) =
      2 * ((∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * |l|) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  have hk1 : 1 ≤ k := by omega
  rw [abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hν hl,
    ← setIntegral_Ioi_rpow_two_abs_mul_sq_arcLineInfiniteDyadicVector hk1 ν l,
    ← setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν (by simpa using hl)]
  have h0 := setIntegral_Ioc_zero_one_sq_eq_half_setIntegral_Ioi_sq hk hν
  linarith

/-- **Strict Dominance of the Origin–Infinity Imbalance over the Critical-Line Excess
(`|l| < 1/2`, `l ≠ 0`, `k ≥ 2`):**
Whenever `l ∈ (−1/2, 1/2)` and `l ≠ 0`,
`0 < E_k(l) − E_k(0) < |E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)|`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_sub_sq_lt_abs_imbalance_of_ne_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) (hl0 : l ≠ 0) :
    (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) <
      |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)| := by
  rw [← sub_pos, abs_imbalance_sub_excess_eq_two_mul_origin_depletion hk hν hl]
  have hlt := setIntegral_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt hk hν hpos
    (l₁ := 0) (l₂ := |l|) (by norm_num) (by simpa using hl) (abs_pos.mpr hl0)
  simp only [mul_zero, Real.rpow_zero, one_mul] at hlt
  linarith

/-! ### Sector linear-Taylor positivity, quadratic `O(l²)` remainder bounds, and transversal critical-line derivatives at `l = 0` -/

/-- Integrability of `v ↦ |v| · (arcLineInfiniteDyadicProfile k ν v)²` on `ℝ` (`k ≥ 2`). -/
theorem integrable_abs_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Integrable (fun v : ℝ => |v| * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  set B := 4 * (680625 * (ν.real univ) ^ 2)
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul B).mono'
    (continuous_abs.mul
      ((continuous_arcLineInfiniteDyadicProfile hk ν).pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hnn : 0 ≤ |v| * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
    mul_nonneg (abs_nonneg v) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc |v| * (arcLineInfiniteDyadicProfile k ν v) ^ 2
      ≤ (4 * Real.exp ((1 / 4 : ℝ) * |v|)) *
          (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
        mul_le_mul (abs_le_four_mul_exp_quarter v)
          (sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v)
          (sq_nonneg _) (by positivity)
    _ = B * (Real.exp ((1 / 4 : ℝ) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by
        dsimp [B]; ring
    _ = B * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- Integrability of `v ↦ v · (arcLineInfiniteDyadicProfile k ν v)²` on `(0, ∞)` (`k ≥ 2`). -/
theorem integrableOn_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    IntegrableOn (fun v : ℝ => v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) (Ioi (0 : ℝ)) := by
  refine (integrable_abs_mul_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn.congr_fun
    (fun v hv => ?_) measurableSet_Ioi
  dsimp only
  rw [abs_of_pos hv]

/-- **Strict positivity of the first logarithmic energy moment `∫_{v > 0} v (Φ_k(v))² dv > 0`
(`k ≥ 2`).** -/
theorem setIntegral_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    0 < ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
  setIntegral_Ioi_pos_of_pos_mul
    (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn
    (integrableOn_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile hk hν)
    (fun _ _ => sq_nonneg _)
    (fun _ hv => hv)
    (setIntegral_Ioi_zero_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos)

/-- **Linear lower bound for the infinity-sector energy across `|l| < 1/2` (`k ≥ 2`):**
`2 l ∫_{v > 0} v (Φ_k(v))² dv ≤ E_k^{(1, ∞)}(l) − E_k^{(1, ∞)}(0)`. -/
theorem two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioi_one
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have h1 := setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l
  have h0 := setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν 0
  simp only [mul_zero, zero_mul, Real.rpow_zero, Real.exp_zero, one_mul] at h0
  rw [h1, h0, ← integral_const_mul,
    ← integral_sub (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl).integrableOn
      (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn]
  refine setIntegral_mono_on
    ((integrableOn_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile hk hν).const_mul (2 * l))
    ((integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl).integrableOn.sub
      (integrable_sq_arcLineInfiniteDyadicProfile hk hν).integrableOn)
    measurableSet_Ioi fun v _ => ?_
  have hexp : 2 * l * v ≤ Real.exp (2 * l * v) - 1 := by
    have := Real.add_one_le_exp (2 * l * v)
    linarith
  calc 2 * l * (v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      = (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by ring
    _ ≤ (Real.exp (2 * l * v) - 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
        mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
    _ = Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
          (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by ring

/-- **Linear lower bound for the origin-sector energy across `|l| < 1/2` (`k ≥ 2`):**
`−2 l ∫_{v > 0} v (Φ_k(v))² dv ≤ E_k^{(0, 1]}(l) − E_k^{(0, 1]}(0)`. -/
theorem neg_two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioc_zero_one
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    -(2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) ≤
      (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have h := two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioi_one hk hν (l := -l) (by simpa using hl)
  rw [← setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν l,
    ← setIntegral_Ioc_zero_one_sq_eq_setIntegral_Ioi_one_sq hk1 ν] at h
  linarith

/-- **Quadratic remainder bound for the infinity-sector linear Taylor expansion (`|l| < 1/2`):**
`0 ≤ (E_k^{(1, ∞)}(l) − E_k^{(1, ∞)}(0)) − 2 l ∫_{v > 0} v (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`. -/
theorem sub_Ioi_one_sub_two_mul_le_excess
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
      2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have h0 : |(0 : ℝ)| < 1 / 2 := by norm_num
  have hsum_l := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν hl
  have hsum_0 := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν h0
  simp only [mul_zero, Real.rpow_zero, one_mul] at hsum_0
  have hneg := neg_two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioc_zero_one hk hν hl
  linarith

/-- **Quadratic remainder bound for the origin-sector linear Taylor expansion (`|l| < 1/2`):**
`0 ≤ (E_k^{(0, 1]}(l) − E_k^{(0, 1]}(0)) + 2 l ∫_{v > 0} v (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`. -/
theorem sub_Ioc_zero_one_add_two_mul_le_excess
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    ((∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2)) +
      2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have h0 : |(0 : ℝ)| < 1 / 2 := by norm_num
  have hsum_l := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν hl
  have hsum_0 := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν h0
  simp only [mul_zero, Real.rpow_zero, one_mul] at hsum_0
  have hpos := two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioi_one hk hν hl
  linarith

/-- **Exact domination of the origin–infinity imbalance linear Taylor remainder by the
critical-line excess (`|l| < 1/2`, `k ≥ 2`):**
`|(E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)) − 4 l ∫_{v > 0} v (Φ_k(v))² dv| ≤ E_k(l) − E_k(0)`. -/
theorem abs_imbalance_sub_four_mul_le_excess
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    |((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
      4 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)| ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have h0 : |(0 : ℝ)| < 1 / 2 := by norm_num
  have hsum_l := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν hl
  have hsum_0 := setIntegral_Ioc_zero_one_add_Ioi_one_rpow_two_mul_sq_eq hk hν h0
  simp only [mul_zero, Real.rpow_zero, one_mul] at hsum_0
  have heq0 := setIntegral_Ioc_zero_one_sq_eq_setIntegral_Ioi_one_sq hk1 ν
  have h1 := two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioi_one hk hν hl
  have h2 := neg_two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioc_zero_one hk hν hl
  rw [abs_le]
  constructor <;> linarith

/-- **Scale-independent quadratic `O(l²)` linear-approximation bound for the origin–infinity
imbalance (`|l| < 1/8`, `k ≥ 2`):**
`|(E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)) − 4 l ∫_{v > 0} v (Φ_k(v))² dv| ≤ (87120000 · (ν.real univ)² / (1/8 − |l|)) · l²`. -/
theorem abs_imbalance_sub_four_mul_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    |((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
      4 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)| ≤
      (87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * l ^ 2 :=
  (abs_imbalance_sub_four_mul_le_excess hk hν (by linarith)).trans
    (setIntegral_Ioi_rpow_two_mul_sq_sub_sq_arcLineInfiniteDyadicVector_le_sq hk hν hl)

/-- **Strictly positive first-order critical-line derivative of the infinity-sector energy
(`k ≥ 2`):**
`((∫_{x > 1} x^{2l} V_k(x)² dx) − (∫_{x > 1} V_k(x)² dx)) / l → 2 ∫_{v > 0} v (Φ_k(v))² dv > 0`
as `l → 0`. -/
theorem tendsto_div_setIntegral_Ioi_one_sub_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
      (𝓝[≠] 0)
      (𝓝 (2 * ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun l : ℝ =>
      ‖((∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l‖)
      (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero] using
      (tendsto_div_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero hk hν).norm
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (h0.mono_left nhdsWithin_le_nhds)
  have hmem : {l : ℝ | |l| < 1 / 2 ∧ l ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := by
    refine inter_mem (mem_nhdsWithin_of_mem_nhds ?_) self_mem_nhdsWithin
    have : Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with l hl
    exact abs_lt.mpr hl
  filter_upwards [hmem] with l ⟨hl, hl0⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hdiv :
      ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l -
        2 * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      (((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
        2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) / l := by
    field_simp
  rw [hdiv, abs_div, abs_div]
  have hnn : 0 ≤
      ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (1 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
        2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) :=
    sub_nonneg.mpr (two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioi_one hk hν hl)
  have hle := sub_Ioi_one_sub_two_mul_le_excess hk hν hl
  rw [abs_of_nonneg hnn, abs_of_nonneg (le_trans hnn hle)]
  exact div_le_div_of_nonneg_right hle (abs_nonneg l)

/-- **Strictly negative first-order critical-line derivative of the origin-sector energy
(`k ≥ 2`):**
`((∫_{x ∈ (0, 1]} x^{2l} V_k(x)² dx) − (∫_{x ∈ (0, 1]} V_k(x)² dx)) / l → −2 ∫_{v > 0} v (Φ_k(v))² dv < 0`
as `l → 0`. -/
theorem tendsto_div_setIntegral_Ioc_zero_one_sub_sq_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      ((∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
      (𝓝[≠] 0)
      (𝓝 (-(2 * ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun l : ℝ =>
      ‖((∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l‖)
      (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero] using
      (tendsto_div_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero hk hν).norm
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (h0.mono_left nhdsWithin_le_nhds)
  have hmem : {l : ℝ | |l| < 1 / 2 ∧ l ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := by
    refine inter_mem (mem_nhdsWithin_of_mem_nhds ?_) self_mem_nhdsWithin
    have : Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with l hl
    exact abs_lt.mpr hl
  filter_upwards [hmem] with l ⟨hl, hl0⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hdiv :
      ((∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l -
        (-(2 * ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) =
      (((∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2)) +
        2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) / l := by
    field_simp; ring
  rw [hdiv, abs_div, abs_div]
  have hnn : 0 ≤
      ((∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, (arcLineInfiniteDyadicVector k ν x) ^ 2)) +
        2 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    have := neg_two_mul_setIntegral_Ioi_zero_mul_sq_le_sub_Ioc_zero_one hk hν hl
    linarith
  have hle := sub_Ioc_zero_one_add_two_mul_le_excess hk hν hl
  rw [abs_of_nonneg hnn, abs_of_nonneg (le_trans hnn hle)]
  exact div_le_div_of_nonneg_right hle (abs_nonneg l)

/-- **Strictly positive transversal critical-line derivative of the origin–infinity energy
imbalance (`k ≥ 2`):**
`((∫_{x > 1} x^{2l} V_k(x)² dx) − (∫_{x ∈ (0, 1]} x^{2l} V_k(x)² dx)) / l → 4 ∫_{v > 0} v (Φ_k(v))² dv > 0`
as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_imbalance_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
      (𝓝[≠] 0)
      (𝓝 (4 * ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun l : ℝ =>
      ‖((∫ x in Ioi 0, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi 0, (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l‖)
      (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero] using
      (tendsto_div_setIntegral_Ioi_rpow_two_mul_sq_sub_sq_nhds_zero hk hν).norm
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (h0.mono_left nhdsWithin_le_nhds)
  have hmem : {l : ℝ | |l| < 1 / 2 ∧ l ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := by
    refine inter_mem (mem_nhdsWithin_of_mem_nhds ?_) self_mem_nhdsWithin
    have : Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with l hl
    exact abs_lt.mpr hl
  filter_upwards [hmem] with l ⟨hl, hl0⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hdiv :
      ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l -
        4 * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      (((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
        4 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) / l := by
    field_simp
  rw [hdiv, abs_div, abs_div]
  have hle := abs_imbalance_sub_four_mul_le_excess hk hν hl
  rw [abs_of_nonneg (le_trans (abs_nonneg _) hle)]
  exact div_le_div_of_nonneg_right hle (abs_nonneg l)

/-- **Master theorem for the sector monotonicity, imbalance–excess dominance, and critical-line
transversality of the infinite-horizon dyadic Hilbert energy:**
There exists a concrete non-zero finite Borel measure `ν` on `ArcParam` such that for every integer
`k ≥ 2`, `V_k = arcLineInfiniteDyadicVector k ν` and `Φ_k = arcLineInfiniteDyadicProfile k ν`
satisfy:
1. **Strict sector monotonicity and imbalance injectivity on `(−1/2, 1/2)`:**
   For all `l₁, l₂ ∈ (−1/2, 1/2)`:
   - `l₁ < l₂ → E_k^{(1, ∞)}(l₁) < E_k^{(1, ∞)}(l₂)` and `E_k^{(0, 1]}(l₂) < E_k^{(0, 1]}(l₁)`,
   - `l₁ < l₂ → E_k^{(1, ∞)}(l₁) − E_k^{(0, 1]}(l₁) < E_k^{(1, ∞)}(l₂) − E_k^{(0, 1]}(l₂)`,
   - `E_k^{(1, ∞)}(l₁) − E_k^{(0, 1]}(l₁) = E_k^{(1, ∞)}(l₂) − E_k^{(0, 1]}(l₂) ↔ l₁ = l₂`.
2. **Strict dominance of the origin–infinity imbalance over the critical-line excess:**
   For every `l ∈ (−1/2, 1/2)` with `l ≠ 0`,
   `0 < E_k(l) − E_k(0) < |E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)|`.
3. **Quadratic `O(l²)` linear-Taylor remainder bound and strictly positive transversal critical-line
   derivative at `l = 0`:**
   - `0 < ∫_{v > 0} v (Φ_k(v))² dv`,
   - For all `|l| < 1/8`,
     `|(E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)) − 4 l ∫_{v > 0} v (Φ_k(v))² dv| ≤ (87120000 · (ν.real univ)² / (1/8 − |l|)) · l²`,
   - As `l → 0` (`l ≠ 0`),
     `(E_k^{(1, ∞)}(l) − E_k^{(0, 1]}(l)) / l → 4 ∫_{v > 0} v (Φ_k(v))² dv > 0`. -/
theorem exists_dyadic_originInfinity_transversality_arcWitness :
    ∃ (ν : Measure ArcParam) (_ : IsFiniteMeasure ν),
      ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0) ∧
      (∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l₁ l₂ : ℝ⦄, |l₁| < 1 / 2 → |l₂| < 1 / 2 → l₁ < l₂ →
          (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
          (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
          (∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) ∧
        (∀ ⦃l₁ l₂ : ℝ⦄, |l₁| < 1 / 2 → |l₂| < 1 / 2 →
          ((∫ x in Ioi (1 : ℝ), x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₁) * (arcLineInfiniteDyadicVector k ν x) ^ 2) =
            (∫ x in Ioi (1 : ℝ), x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l₂) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ↔
            l₁ = l₂)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 → l ≠ 0 →
          0 < (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
          (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) <
            |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)|) ∧
        (0 < ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 →
          |((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) -
            4 * l * (∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2)| ≤
            (87120000 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * l ^ 2) ∧
        Tendsto (fun l : ℝ =>
          ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) / l)
          (𝓝[≠] 0)
          (𝓝 (4 * ∫ v in Ioi (0 : ℝ), v * (arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
  obtain ⟨ν, hfin, hne, hsymm, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsymm, hblind, fun k hk => ?_⟩
  refine ⟨fun l₁ l₂ hl₁ hl₂ hlt =>
      ⟨setIntegral_Ioi_one_rpow_two_mul_sq_lt_of_lt hk hsymm hpd hl₁ hl₂ hlt,
        setIntegral_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt hk hsymm hpd hl₁ hl₂ hlt,
        setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_lt_of_lt hk hsymm hpd hl₁ hl₂ hlt⟩,
    fun l₁ l₂ hl₁ hl₂ =>
      setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq_iff hk hsymm hpd hl₁ hl₂,
    fun l hl hl0 =>
      ⟨sub_pos.mpr
          (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_lt_rpow_two_mul_of_ne_zero
            hk hsymm hpd hl hl0),
        setIntegral_Ioi_rpow_two_mul_sq_sub_sq_lt_abs_imbalance_of_ne_zero hk hsymm hpd hl hl0⟩,
    setIntegral_Ioi_zero_mul_sq_arcLineInfiniteDyadicProfile_pos hk hsymm hpd,
    fun l hl => abs_imbalance_sub_four_mul_le_sq hk hsymm hl,
    tendsto_div_imbalance_nhds_zero hk hsymm⟩

end

end RHTower
