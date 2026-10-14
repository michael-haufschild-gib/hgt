import GaloisForLFunctions.RHTower.ModularArcDyadicLogarithmicMomentHierarchy

/-!
# Origin–infinity oscillatory Mellin imbalance, the Mellin–Hilbert Rayleigh quotient, quantitative off-line suppression, and two-sided infinite-order strip-edge vanishing

In `ModularArcDyadicFullStripFunctionalSymmetry` and `ModularArcDyadicStripOscillatoryMellin`, we
established the linear Mellin functional
`M_k(l) = ∫_{x > 0} x^{l − 1/2} V_k(x) dx = ∫_ℝ e^{lv} Φ_k(v) dv`
and the two-variable oscillatory Mellin transform
`M_k(l, τ) = ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx`
across the open critical strip `|l| < 1/2`. In `ModularArcDyadicStripWeightedHilbertMinimum`,
`ModularArcDyadicCriticalLineStrictConvexity`, and `ModularArcDyadicCriticalLineQuadraticCoercivity`,
we established the quadratic strip-weighted Hilbert energy
`E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx = ∫_ℝ e^{2lv} (Φ_k(v))² dv`.

In this module we unify the linear Mellin and quadratic Hilbert theories across the open critical
strip `|l| < 1/2`:

1. **Origin–infinity oscillatory Mellin imbalance (`setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq`,
   `setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_cos_log`,
   `setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log`,
   `abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_le`):**
   - Across `|l| < 1/2` and `τ ∈ ℝ`, the difference between the `(1, ∞)` and `(0, 1]` oscillatory
     Mellin integrals obeys the exact `2 sinh(lv) cos(τv)` representation:
     `∫_{x > 1} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_{v > 0} 2 sinh(lv) cos(τv) Φ_k(v) dv`.
   - It is odd in `l`, even in `τ`, vanishes identically on the critical line `l = 0` for all
     `τ ∈ ℝ`, and satisfies the height-uniform linear `O(|l|)` bound
     `≤ (26400 · ν.real univ / (1/8 − |l|)) · |l|` on `|l| < 1/8`.
2. **Mellin–Hilbert ratio `R_k(l) = M_k(l) / E_k(l)` and Rayleigh quotient
   `Q_k(l) = (M_k(l))² / E_k(l)` across `|l| < 1/2`
   (`arcLineInfiniteDyadicMellinHilbertRatio`, `arcLineInfiniteDyadicRayleighQuotient`,
   `arcLineInfiniteDyadicMellinHilbertRatio_neg`, `arcLineInfiniteDyadicRayleighQuotient_neg`,
   `arcLineInfiniteDyadicMellinHilbertRatio_pos`, `arcLineInfiniteDyadicRayleighQuotient_pos`):**
   - Both `R_k(l)` and `Q_k(l)` are invariant under functional-equation reflection `l ↦ −l` and
     strictly positive across the entire open critical strip `|l| < 1/2`.
3. **Strict off-critical-line denominator suppression and quadratic coercivity lower bounds on the
   suppression gap (`arcLineInfiniteDyadicMellinHilbertRatio_le_div_unweighted`,
   `arcLineInfiniteDyadicMellinHilbertRatio_lt_div_unweighted_of_ne_zero`,
   `arcLineInfiniteDyadicRayleighQuotient_le_div_unweighted`,
   `arcLineInfiniteDyadicRayleighQuotient_lt_div_unweighted_of_ne_zero`,
   `two_mul_sq_mul_le_mellinHilbertRatio_suppression`,
   `two_mul_sq_mul_le_rayleighQuotient_suppression`):**
   - For every `l ≠ 0` in `(−1/2, 1/2)`, normalizing by the strip-weighted Hilbert energy `E_k(l)`
     strictly suppresses the ratio relative to the critical-line Hilbert energy `E_k(0)`:
     `R_k(l) < M_k(l) / E_k(0)` and `Q_k(l) < (M_k(l))² / E_k(0)`.
   - The suppression gaps are bounded below across all `|l| < 1/2` by:
     `(2 l² · M_k(l) · ∫_ℝ v² (Φ_k(v))² dv) / (E_k(0) · E_k(l)) ≤ M_k(l) / E_k(0) − R_k(l)` and
     `(2 l² · (M_k(l))² · ∫_ℝ v² (Φ_k(v))² dv) / (E_k(0) · E_k(l)) ≤ (M_k(l))² / E_k(0) − Q_k(l)`.
4. **Two-sided infinite-order (`O((1/2 − |l|)^{N+1})` and `O((1/2 − |l|)^{2N+2})` for all `N ∈ ℕ`)
   strip-edge vanishing of `R_k(l)` and `Q_k(l)`
   (`arcLineInfiniteDyadicMellinHilbertRatio_le_pow_sub_abs`,
   `arcLineInfiniteDyadicRayleighQuotient_le_pow_sub_abs`,
   `tendsto_div_pow_mellinHilbertRatio_nhdsWithin_half`,
   `tendsto_div_pow_mellinHilbertRatio_nhdsWithin_neg_half`,
   `tendsto_div_pow_rayleighQuotient_nhdsWithin_half`,
   `tendsto_div_pow_rayleighQuotient_nhdsWithin_neg_half`,
   `exists_dyadic_mellinHilbert_rayleighRatio_arcWitness`):**
   - For every `N ∈ ℕ`, `R_k(l) / (1/2 ∓ l)^N → 0` and `Q_k(l) / (1/2 ∓ l)^N → 0` as `l → (1/2)⁻`
     and as `l → (−1/2)⁺`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Origin–infinity oscillatory Mellin imbalance -/

/-- **Exact `2 sinh(lv) cos(τv)` representation of the origin–infinity oscillatory Mellin imbalance
(`|l| < 1/2`, `τ ∈ ℝ`, `k ≥ 2`):**
`∫_{x > 1} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_{v > 0} 2 sinh(lv) cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ),
        2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hk1 : 1 ≤ k := by omega
  have hnl : |-l| < 1 / 2 := by simpa using hl
  have hI_pos := (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl τ).integrableOn
    (s := Ioi (0 : ℝ))
  have hI_neg : IntegrableOn
      (fun v : ℝ => Real.exp (-(l * v)) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
    refine ((integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hnl τ).integrableOn
      (s := Ioi (0 : ℝ))).congr_fun (fun v _ => ?_) measurableSet_Ioi
    dsimp only; rw [neg_mul]
  rw [setIntegral_Ioi_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq hk1 ν l τ,
    setIntegral_Ioc_zero_one_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq hk1 ν l τ,
    ← integral_sub hI_pos hI_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [Real.sinh_eq]
  ring

/-- **Odd reflection antisymmetry `l ↦ −l` of the origin–infinity oscillatory Mellin imbalance
(`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_neg_mul_cos_log
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      -((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have h1 := setIntegral_Ioc_zero_one_rpow_mul_cos_log_eq_setIntegral_Ioi_one_neg hk ν l τ
  have h2 := setIntegral_Ioc_zero_one_rpow_mul_cos_log_eq_setIntegral_Ioi_one_neg hk ν (-l) τ
  rw [neg_neg] at h2
  linarith

/-- **Identical vanishing of the origin–infinity oscillatory Mellin imbalance on the critical line
`l = 0` for all vertical frequencies `τ ∈ ℝ` (`k ≥ 1`).** -/
theorem setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      0 := by
  rw [zero_sub, setIntegral_Ioc_zero_one_cos_log_eq_setIntegral_Ioi_one hk ν τ, sub_self]

/-- **Height-uniform and scale-independent linear `O(|l|)` bound on the origin–infinity oscillatory
Mellin imbalance across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`|∫_{x > 1} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx| ≤ (26400 · ν.real univ / (1/8 − |l|)) · |l|`. -/
theorem abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
      (26400 * ν.real univ / (1 / 8 - |l|)) * |l| := by
  have hl_half : |l| < 1 / 2 := by linarith
  have hcl : 0 < 1 / 8 - |l| := sub_pos.mpr hl
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half τ]
  set B := 13200 * ν.real univ * |l|
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hcl).const_mul B
  have hpt : ∀ v : ℝ,
      |2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
        B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
    intro v
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hsinh : |Real.sinh (l * v)| ≤ 8 * |l| * Real.exp ((|l| + 1 / 8) * |v|) := by
      have h1 := abs_sinh_le_abs_mul_exp_abs (l * v)
      rw [abs_mul] at h1
      have hv8 := abs_le_eight_mul_exp_eighth v
      calc |Real.sinh (l * v)|
          ≤ (|l| * |v|) * Real.exp (|l| * |v|) := h1
        _ ≤ (|l| * (8 * Real.exp ((1 / 8 : ℝ) * |v|))) * Real.exp (|l| * |v|) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hv8 (abs_nonneg l)) (Real.exp_pos _).le
        _ = 8 * |l| * (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (|l| * |v|)) := by ring
        _ = 8 * |l| * Real.exp ((|l| + 1 / 8) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    have hcos : |Real.cos (τ * v)| ≤ 1 := Real.abs_cos_le_one (τ * v)
    have hprof := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
    have hsc : 2 * |Real.sinh (l * v)| * |Real.cos (τ * v)| ≤
        16 * |l| * Real.exp ((|l| + 1 / 8) * |v|) := by
      calc 2 * |Real.sinh (l * v)| * |Real.cos (τ * v)|
          ≤ (2 * (8 * |l| * Real.exp ((|l| + 1 / 8) * |v|))) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsinh (by norm_num)) hcos
              (abs_nonneg _) (by positivity)
        _ = 16 * |l| * Real.exp ((|l| + 1 / 8) * |v|) := by ring
    calc 2 * |Real.sinh (l * v)| * |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
        ≤ (16 * |l| * Real.exp ((|l| + 1 / 8) * |v|)) *
            (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul hsc hprof (abs_nonneg _) (by positivity)
      _ = B * (Real.exp ((|l| + 1 / 8) * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ => 2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
    (hdom.integrableOn (s := Ioi (0 : ℝ)))
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hpt v)
  rw [Real.norm_eq_abs] at h1
  have h2 : (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l|) * |v|))) ≤
      ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l|) * |v|)) :=
    setIntegral_le_integral hdom (Eventually.of_forall fun v => by positivity)
  have h2_eq : (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l|) * |v|))) = B * (2 / (1 / 8 - |l|)) := by
    rw [integral_const_mul, integral_rexp_neg_mul_abs hcl]
  rw [h2_eq] at h2
  have h3 : B * (2 / (1 / 8 - |l|)) = (26400 * ν.real univ / (1 / 8 - |l|)) * |l| := by
    dsimp [B]; ring
  linarith

/-! ### Mellin–Hilbert ratio `R_k(l)` and Rayleigh quotient `Q_k(l)` across the open critical strip `|l| < 1/2` -/

/-- **The strip-normalized Mellin–Hilbert ratio `R_k(l) = M_k(l) / E_k(l)`:**
the ratio of the linear Mellin functional `∫_{x > 0} x^{l − 1/2} V_k(x) dx` to the strip-weighted
quadratic Hilbert energy `∫_{x > 0} x^{2l} (V_k(x))² dx`. -/
def arcLineInfiniteDyadicMellinHilbertRatio (k : ℕ) (ν : Measure ArcParam) (l : ℝ) : ℝ :=
  (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
    (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)

/-- **The strip-normalized Mellin–Hilbert Rayleigh quotient `Q_k(l) = (M_k(l))² / E_k(l)`:**
the squared linear Mellin functional divided by the strip-weighted quadratic Hilbert energy. -/
def arcLineInfiniteDyadicRayleighQuotient (k : ℕ) (ν : Measure ArcParam) (l : ℝ) : ℝ :=
  (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
    (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)

/-- Algebraic factorization `Q_k(l) = M_k(l) · R_k(l)`. -/
theorem arcLineInfiniteDyadicRayleighQuotient_eq_mul_ratio
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    arcLineInfiniteDyadicRayleighQuotient k ν l =
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) *
        arcLineInfiniteDyadicMellinHilbertRatio k ν l := by
  unfold arcLineInfiniteDyadicRayleighQuotient arcLineInfiniteDyadicMellinHilbertRatio
  ring

/-- **Functional equation reflection symmetry `l ↦ −l` (`s ↔ 1 − s`) for `R_k(l)` (`k ≥ 1`).** -/
theorem arcLineInfiniteDyadicMellinHilbertRatio_neg
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    arcLineInfiniteDyadicMellinHilbertRatio k ν (-l) =
      arcLineInfiniteDyadicMellinHilbertRatio k ν l := by
  unfold arcLineInfiniteDyadicMellinHilbertRatio
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_arcLineInfiniteDyadicVector hk ν l,
    setIntegral_Ioi_rpow_two_neg_mul_sq_arcLineInfiniteDyadicVector hk ν l]

/-- **Functional equation reflection symmetry `l ↦ −l` (`s ↔ 1 − s`) for `Q_k(l)` (`k ≥ 1`).** -/
theorem arcLineInfiniteDyadicRayleighQuotient_neg
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    arcLineInfiniteDyadicRayleighQuotient k ν (-l) =
      arcLineInfiniteDyadicRayleighQuotient k ν l := by
  unfold arcLineInfiniteDyadicRayleighQuotient
  rw [setIntegral_Ioi_rpow_neg_sub_half_mul_arcLineInfiniteDyadicVector hk ν l,
    setIntegral_Ioi_rpow_two_neg_mul_sq_arcLineInfiniteDyadicVector hk ν l]

/-- **Strict interior positivity of the Mellin–Hilbert ratio `R_k(l) > 0` across the entire open
critical strip `|l| < 1/2` (`k ≥ 2`).** -/
theorem arcLineInfiniteDyadicMellinHilbertRatio_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    0 < arcLineInfiniteDyadicMellinHilbertRatio k ν l :=
  div_pos
    (setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hν hpd hl)
    (setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl)

/-- **Strict interior positivity of the Mellin–Hilbert Rayleigh quotient `Q_k(l) > 0` across the
entire open critical strip `|l| < 1/2` (`k ≥ 2`).** -/
theorem arcLineInfiniteDyadicRayleighQuotient_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    0 < arcLineInfiniteDyadicRayleighQuotient k ν l :=
  div_pos
    (sq_pos_of_pos
      (setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hν hpd hl))
    (setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl)

/-! ### Off-critical-line denominator suppression and quadratic coercivity lower bounds on the suppression gap -/

/-- Non-negativity of `M_k(l) = ∫_{x > 0} x^{l − 1/2} V_k(x) dx` across `|l| < 1/2` (`k ≥ 2`). -/
theorem setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nonneg_of_abs_lt_half
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    0 ≤ ∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_of_abs_lt_half hk hν hl]
  exact arcLineInfiniteDyadicLaplaceTransform_nonneg hk1 hν (abs_nonneg l) hl

/-- **Exact algebraic identity for the off-line suppression gap of `R_k(l)` (`k ≥ 2`, `|l| < 1/2`):**
`M_k(l) / E_k(0) − R_k(l) = M_k(l) · (E_k(l) − E_k(0)) / (E_k(0) · E_k(l))`. -/
theorem div_unweighted_sub_mellinHilbertRatio_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      arcLineInfiniteDyadicMellinHilbertRatio k ν l =
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) /
        ((∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) *
          (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  unfold arcLineInfiniteDyadicMellinHilbertRatio
  set M := ∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x
  set E0 := ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2
  set El := ∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2
  have hE0 : E0 ≠ 0 :=
    ne_of_gt (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd)
  have hEl : El ≠ 0 :=
    ne_of_gt (setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl)
  field_simp

/-- **Exact algebraic identity for the off-line suppression gap of `Q_k(l)` (`k ≥ 2`, `|l| < 1/2`):**
`(M_k(l))² / E_k(0) − Q_k(l) = (M_k(l))² · (E_k(l) − E_k(0)) / (E_k(0) · E_k(l))`. -/
theorem div_unweighted_sub_rayleighQuotient_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      arcLineInfiniteDyadicRayleighQuotient k ν l =
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 *
        ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) /
        ((∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) *
          (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  unfold arcLineInfiniteDyadicRayleighQuotient
  set M := ∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x
  set E0 := ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2
  set El := ∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2
  have hE0 : E0 ≠ 0 :=
    ne_of_gt (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd)
  have hEl : El ≠ 0 :=
    ne_of_gt (setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl)
  field_simp

/-- **Global quadratic coercivity lower bound on the off-line suppression gap of `R_k(l)`
(`|l| < 1/2`, `k ≥ 2`):**
`(2 l² · M_k(l) · ∫_ℝ v² (Φ_k(v))² dv) / (E_k(0) · E_k(l)) ≤ M_k(l) / E_k(0) − R_k(l)`. -/
theorem two_mul_sq_mul_le_mellinHilbertRatio_suppression
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (2 * l ^ 2 * (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) *
        (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) /
      ((∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) *
        (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) ≤
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      arcLineInfiniteDyadicMellinHilbertRatio k ν l := by
  rw [div_unweighted_sub_mellinHilbertRatio_eq hk hν hpd hl]
  have hM_nn := setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nonneg_of_abs_lt_half hk hν hl
  have hcoerc := two_mul_sq_mul_integral_sq_mul_sq_le_excess hk hν hl
  have hE0 := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd
  have hEl := setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl
  refine div_le_div_of_nonneg_right ?_ (mul_pos hE0 hEl).le
  calc 2 * l ^ 2 * (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) *
          (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      = (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) *
          (2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by ring
    _ ≤ (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
            (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoerc hM_nn

/-- **Global quadratic coercivity lower bound on the off-line suppression gap of `Q_k(l)`
(`|l| < 1/2`, `k ≥ 2`):**
`(2 l² · (M_k(l))² · ∫_ℝ v² (Φ_k(v))² dv) / (E_k(0) · E_k(l)) ≤ (M_k(l))² / E_k(0) − Q_k(l)`. -/
theorem two_mul_sq_mul_le_rayleighQuotient_suppression
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    (2 * l ^ 2 * (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 *
        (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) /
      ((∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) *
        (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) ≤
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) -
      arcLineInfiniteDyadicRayleighQuotient k ν l := by
  rw [div_unweighted_sub_rayleighQuotient_eq hk hν hpd hl]
  have hcoerc := two_mul_sq_mul_integral_sq_mul_sq_le_excess hk hν hl
  have hE0 := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd
  have hEl := setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl
  refine div_le_div_of_nonneg_right ?_ (mul_pos hE0 hEl).le
  calc 2 * l ^ 2 * (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 *
          (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      = (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 *
          (2 * l ^ 2 * (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by ring
    _ ≤ (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 *
          ((∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
            (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoerc (sq_nonneg _)

/-- **Denominator suppression inequality for `R_k(l)` across `|l| < 1/2` (`k ≥ 2`):**
`R_k(l) ≤ M_k(l) / E_k(0)`. -/
theorem arcLineInfiniteDyadicMellinHilbertRatio_le_div_unweighted
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    arcLineInfiniteDyadicMellinHilbertRatio k ν l ≤
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  unfold arcLineInfiniteDyadicMellinHilbertRatio
  exact div_le_div_of_nonneg_left
    (setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nonneg_of_abs_lt_half hk hν hl)
    (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd)
    (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul hk hν hl)

/-- **Strict off-critical-line denominator suppression for `R_k(l)` (`|l| < 1/2`, `l ≠ 0`, `k ≥ 2`):**
`R_k(l) < M_k(l) / E_k(0)`. -/
theorem arcLineInfiniteDyadicMellinHilbertRatio_lt_div_unweighted_of_ne_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) (hl0 : l ≠ 0) :
    arcLineInfiniteDyadicMellinHilbertRatio k ν l <
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [← sub_pos, div_unweighted_sub_mellinHilbertRatio_eq hk hν hpd hl]
  have hM := setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hν hpd hl
  have hEx := sub_pos.mpr
    (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_lt_rpow_two_mul_of_ne_zero hk hν hpd hl hl0)
  have hE0 := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd
  have hEl := setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl
  exact div_pos (mul_pos hM hEx) (mul_pos hE0 hEl)

/-- **Denominator suppression inequality for `Q_k(l)` across `|l| < 1/2` (`k ≥ 2`):**
`Q_k(l) ≤ (M_k(l))² / E_k(0)`. -/
theorem arcLineInfiniteDyadicRayleighQuotient_le_div_unweighted
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    arcLineInfiniteDyadicRayleighQuotient k ν l ≤
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  unfold arcLineInfiniteDyadicRayleighQuotient
  exact div_le_div_of_nonneg_left
    (sq_nonneg _)
    (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd)
    (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_le_rpow_two_mul hk hν hl)

/-- **Strict off-critical-line denominator suppression for `Q_k(l)` (`|l| < 1/2`, `l ≠ 0`, `k ≥ 2`):**
`Q_k(l) < (M_k(l))² / E_k(0)`. -/
theorem arcLineInfiniteDyadicRayleighQuotient_lt_div_unweighted_of_ne_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) (hl0 : l ≠ 0) :
    arcLineInfiniteDyadicRayleighQuotient k ν l <
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [← sub_pos, div_unweighted_sub_rayleighQuotient_eq hk hν hpd hl]
  have hM := sq_pos_of_pos
    (setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hν hpd hl)
  have hEx := sub_pos.mpr
    (setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_lt_rpow_two_mul_of_ne_zero hk hν hpd hl hl0)
  have hE0 := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd
  have hEl := setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_pos hk hν hpd hl
  exact div_pos (mul_pos hM hEx) (mul_pos hE0 hEl)

/-! ### Two-sided infinite-order strip-edge vanishing of `R_k(l)` and `Q_k(l)` -/

/-- **Two-sided infinite-order (`O((1/2 − |l|)^{N+1})` for all `N ∈ ℕ`) strip-edge upper bound for
the Mellin–Hilbert ratio `R_k(l)` across `|l| < 1/2` (`k ≥ 2`).** -/
theorem arcLineInfiniteDyadicMellinHilbertRatio_le_pow_sub_abs
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    arcLineInfiniteDyadicMellinHilbertRatio k ν l ≤
      ((10 * ν.real univ * dyadicStripConst k N) /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) *
        (1 / 2 - |l|) ^ (N + 1) := by
  have hle := arcLineInfiniteDyadicMellinHilbertRatio_le_div_unweighted hk hν hpd hl
  have hM_nn := setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nonneg_of_abs_lt_half hk hν hl
  have hedge := abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_abs hk N hν hl
  rw [abs_of_nonneg hM_nn] at hedge
  have hE0 := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd
  calc arcLineInfiniteDyadicMellinHilbertRatio k ν l
      ≤ (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := hle
    _ ≤ ((10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - |l|) ^ (N + 1)) /
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) :=
        div_le_div_of_nonneg_right hedge hE0.le
    _ = ((10 * ν.real univ * dyadicStripConst k N) /
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) *
          (1 / 2 - |l|) ^ (N + 1) := by ring

/-- **Two-sided infinite-order (`O((1/2 − |l|)^{2N+2})` for all `N ∈ ℕ`) strip-edge upper bound for
the Mellin–Hilbert Rayleigh quotient `Q_k(l)` across `|l| < 1/2` (`k ≥ 2`).** -/
theorem arcLineInfiniteDyadicRayleighQuotient_le_pow_sub_abs
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl : |l| < 1 / 2) :
    arcLineInfiniteDyadicRayleighQuotient k ν l ≤
      ((10 * ν.real univ * dyadicStripConst k N) ^ 2 /
        (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) *
        (1 / 2 - |l|) ^ (2 * N + 2) := by
  have hle := arcLineInfiniteDyadicRayleighQuotient_le_div_unweighted hk hν hpd hl
  have hedge := abs_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_le_pow_sub_abs hk N hν hl
  have hsq : (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 ≤
      (10 * ν.real univ * dyadicStripConst k N) ^ 2 * (1 / 2 - |l|) ^ (2 * N + 2) := by
    calc (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2
        = |∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x| *
            |∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x| := by
            rw [← sq, sq_abs]
      _ ≤ ((10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - |l|) ^ (N + 1)) *
            ((10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - |l|) ^ (N + 1)) :=
          mul_le_mul hedge hedge (abs_nonneg _)
            (le_trans (abs_nonneg _) hedge)
      _ = (10 * ν.real univ * dyadicStripConst k N) ^ 2 *
            ((1 / 2 - |l|) ^ (N + 1) * (1 / 2 - |l|) ^ (N + 1)) := by ring
      _ = (10 * ν.real univ * dyadicStripConst k N) ^ 2 * (1 / 2 - |l|) ^ (2 * N + 2) := by
          rw [← pow_add]; congr 2; omega
  have hE0 := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd
  calc arcLineInfiniteDyadicRayleighQuotient k ν l
      ≤ (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) := hle
    _ ≤ ((10 * ν.real univ * dyadicStripConst k N) ^ 2 * (1 / 2 - |l|) ^ (2 * N + 2)) /
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) :=
        div_le_div_of_nonneg_right hsq hE0.le
    _ = ((10 * ν.real univ * dyadicStripConst k N) ^ 2 /
          (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2)) *
          (1 / 2 - |l|) ^ (2 * N + 2) := by ring

/-- **Infinite-order divided-difference vanishing of `R_k(l)` at the right strip edge
`l → (1/2)⁻` (`Re(s) → 1⁻`, `k ≥ 2`, `N ∈ ℕ`).** -/
theorem tendsto_div_pow_mellinHilbertRatio_nhdsWithin_half
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    Tendsto (fun l : ℝ =>
      arcLineInfiniteDyadicMellinHilbertRatio k ν l / (1 / 2 - l) ^ N)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set E0 := ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2
  have hE0 : 0 < E0 := setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_pos hk hν hpd
  have hlim : Tendsto (fun l : ℝ =>
      ‖(∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
        (1 / 2 - l) ^ N‖ / E0)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
    simpa using ((tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin
      hk N hν).norm).div_const E0
  refine squeeze_zero_norm' ?_ hlim
  have hev : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hev] with l hl
  have hl_abs : |l| < 1 / 2 := by rw [abs_of_pos hl.1]; exact hl.2
  have hsub_pos : 0 < 1 / 2 - l := sub_pos.mpr hl.2
  have hR_pos := arcLineInfiniteDyadicMellinHilbertRatio_pos hk hν hpd hl_abs
  have hR_le := arcLineInfiniteDyadicMellinHilbertRatio_le_div_unweighted hk hν hpd hl_abs
  have hM_pos := setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hν hpd hl_abs
  rw [Real.norm_of_nonneg (div_pos hR_pos (pow_pos hsub_pos N)).le,
    Real.norm_of_nonneg (div_pos hM_pos (pow_pos hsub_pos N)).le]
  calc arcLineInfiniteDyadicMellinHilbertRatio k ν l / (1 / 2 - l) ^ N
      ≤ ((∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / E0) /
          (1 / 2 - l) ^ N :=
        div_le_div_of_nonneg_right hR_le (pow_pos hsub_pos N).le
    _ = ((∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
          (1 / 2 - l) ^ N) / E0 := by ring

/-- **Infinite-order divided-difference vanishing of `R_k(l)` at the left strip edge
`l → (−1/2)⁺` (`Re(s) → 0⁺`, `k ≥ 2`, `N ∈ ℕ`).** -/
theorem tendsto_div_pow_mellinHilbertRatio_nhdsWithin_neg_half
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    Tendsto (fun l : ℝ =>
      arcLineInfiniteDyadicMellinHilbertRatio k ν l / (1 / 2 + l) ^ N)
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
  have hright := (tendsto_div_pow_mellinHilbertRatio_nhdsWithin_half hk N hν hpd).comp hmap
  refine hright.congr' (Eventually.of_forall fun l => ?_)
  dsimp only [Function.comp_apply]
  rw [arcLineInfiniteDyadicMellinHilbertRatio_neg hk1 ν l, sub_neg_eq_add]

/-- **Infinite-order divided-difference vanishing of `Q_k(l)` at the right strip edge
`l → (1/2)⁻` (`Re(s) → 1⁻`, `k ≥ 2`, `N ∈ ℕ`).** -/
theorem tendsto_div_pow_rayleighQuotient_nhdsWithin_half
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    Tendsto (fun l : ℝ =>
      arcLineInfiniteDyadicRayleighQuotient k ν l / (1 / 2 - l) ^ N)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  have hR := tendsto_div_pow_mellinHilbertRatio_nhdsWithin_half hk N hν hpd
  have hM := tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin hk 0 hν
  have hprod : Tendsto (fun l : ℝ =>
      ((∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
        (1 / 2 - l) ^ 0) *
      (arcLineInfiniteDyadicMellinHilbertRatio k ν l / (1 / 2 - l) ^ N))
      (𝓝[<] (1 / 2)) (𝓝 0) := by
    simpa using hM.mul hR
  refine hprod.congr' (Eventually.of_forall fun l => ?_)
  dsimp only
  rw [pow_zero, div_one, arcLineInfiniteDyadicRayleighQuotient_eq_mul_ratio, mul_div_assoc]

/-- **Infinite-order divided-difference vanishing of `Q_k(l)` at the left strip edge
`l → (−1/2)⁺` (`Re(s) → 0⁺`, `k ≥ 2`, `N ∈ ℕ`).** -/
theorem tendsto_div_pow_rayleighQuotient_nhdsWithin_neg_half
    {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) :
    Tendsto (fun l : ℝ =>
      arcLineInfiniteDyadicRayleighQuotient k ν l / (1 / 2 + l) ^ N)
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
  have hright := (tendsto_div_pow_rayleighQuotient_nhdsWithin_half hk N hν hpd).comp hmap
  refine hright.congr' (Eventually.of_forall fun l => ?_)
  dsimp only [Function.comp_apply]
  rw [arcLineInfiniteDyadicRayleighQuotient_neg hk1 ν l, sub_neg_eq_add]

/-- **Master theorem for the origin–infinity oscillatory Mellin imbalance, Mellin–Hilbert Rayleigh
quotient, quantitative off-line suppression, and two-sided infinite-order strip-edge vanishing:**
There exists a concrete non-zero finite Borel measure `ν` on `ArcParam` such that for every integer
`k ≥ 2`, `V_k = arcLineInfiniteDyadicVector k ν` and `Φ_k = arcLineInfiniteDyadicProfile k ν`
satisfy:
1. **Origin–infinity oscillatory Mellin imbalance and uniform `O(|l|)` bound:**
   For all `|l| < 1/8` and `τ ∈ ℝ`,
   `|∫_{x > 1} x^{l − 1/2} cos(τ log x) V_k(x) dx − ∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx| ≤ (26400 · ν.real univ / (1/8 − |l|)) · |l|`.
2. **Functional equation symmetry `l ↦ −l` and strict interior positivity of `R_k(l)` and `Q_k(l)`:**
   For all `|l| < 1/2`, `R_k(−l) = R_k(l) > 0` and `Q_k(−l) = Q_k(l) > 0`.
3. **Strict off-line denominator suppression and quadratic coercivity lower bound on the gap:**
   For all `|l| < 1/2` with `l ≠ 0`, `R_k(l) < M_k(l) / E_k(0)` and `Q_k(l) < (M_k(l))² / E_k(0)`,
   and for all `|l| < 1/2`,
   `(2 l² · (M_k(l))² · ∫_ℝ v² (Φ_k(v))² dv) / (E_k(0) · E_k(l)) ≤ (M_k(l))² / E_k(0) − Q_k(l)`.
4. **Two-sided infinite-order strip-edge vanishing (`N ∈ ℕ`):**
   `R_k(l) / (1/2 − l)^N → 0` and `Q_k(l) / (1/2 − l)^N → 0` as `l → (1/2)⁻`, and
   `R_k(l) / (1/2 + l)^N → 0` and `Q_k(l) / (1/2 + l)^N → 0` as `l → (−1/2)⁺`. -/
theorem exists_dyadic_mellinHilbert_rayleighRatio_arcWitness :
    ∃ (ν : Measure ArcParam) (_ : IsFiniteMeasure ν),
      ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ m : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m * t) = 0) ∧
      (∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          |(∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
            (26400 * ν.real univ / (1 / 8 - |l|)) * |l|) ∧
        (∀ l : ℝ,
          arcLineInfiniteDyadicMellinHilbertRatio k ν (-l) =
            arcLineInfiniteDyadicMellinHilbertRatio k ν l ∧
          arcLineInfiniteDyadicRayleighQuotient k ν (-l) =
            arcLineInfiniteDyadicRayleighQuotient k ν l) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 →
          0 < arcLineInfiniteDyadicMellinHilbertRatio k ν l ∧
          0 < arcLineInfiniteDyadicRayleighQuotient k ν l ∧
          (2 * l ^ 2 *
              (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 *
              (∫ v : ℝ, v ^ 2 * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) /
            ((∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) *
              (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) ≤
            (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
              (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) -
            arcLineInfiniteDyadicRayleighQuotient k ν l ∧
          (l ≠ 0 →
            arcLineInfiniteDyadicMellinHilbertRatio k ν l <
              (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
                (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
            arcLineInfiniteDyadicRayleighQuotient k ν l <
              (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) ^ 2 /
                (∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2))) ∧
        (∀ N : ℕ,
          Tendsto (fun l : ℝ =>
            arcLineInfiniteDyadicMellinHilbertRatio k ν l / (1 / 2 - l) ^ N)
            (𝓝[<] (1 / 2)) (𝓝 0) ∧
          Tendsto (fun l : ℝ =>
            arcLineInfiniteDyadicMellinHilbertRatio k ν l / (1 / 2 + l) ^ N)
            (𝓝[>] (-1 / 2)) (𝓝 0) ∧
          Tendsto (fun l : ℝ =>
            arcLineInfiniteDyadicRayleighQuotient k ν l / (1 / 2 - l) ^ N)
            (𝓝[<] (1 / 2)) (𝓝 0) ∧
          Tendsto (fun l : ℝ =>
            arcLineInfiniteDyadicRayleighQuotient k ν l / (1 / 2 + l) ^ N)
            (𝓝[>] (-1 / 2)) (𝓝 0))) := by
  obtain ⟨ν, hfin, hne, hsymm, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ m : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m * t) = 0 := fun m => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker m).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsymm, hblind, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  refine ⟨fun l hl τ =>
      abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_le hk hsymm hl τ,
    fun l =>
      ⟨arcLineInfiniteDyadicMellinHilbertRatio_neg hk1 ν l,
       arcLineInfiniteDyadicRayleighQuotient_neg hk1 ν l⟩,
    fun l hl =>
      ⟨arcLineInfiniteDyadicMellinHilbertRatio_pos hk hsymm hpd hl,
       arcLineInfiniteDyadicRayleighQuotient_pos hk hsymm hpd hl,
       two_mul_sq_mul_le_rayleighQuotient_suppression hk hsymm hpd hl,
       fun hl0 =>
         ⟨arcLineInfiniteDyadicMellinHilbertRatio_lt_div_unweighted_of_ne_zero hk hsymm hpd hl hl0,
          arcLineInfiniteDyadicRayleighQuotient_lt_div_unweighted_of_ne_zero hk hsymm hpd hl hl0⟩⟩,
    fun N =>
      ⟨tendsto_div_pow_mellinHilbertRatio_nhdsWithin_half hk N hsymm hpd,
       tendsto_div_pow_mellinHilbertRatio_nhdsWithin_neg_half hk N hsymm hpd,
       tendsto_div_pow_rayleighQuotient_nhdsWithin_half hk N hsymm hpd,
       tendsto_div_pow_rayleighQuotient_nhdsWithin_neg_half hk N hsymm hpd⟩⟩

end

end RHTower
