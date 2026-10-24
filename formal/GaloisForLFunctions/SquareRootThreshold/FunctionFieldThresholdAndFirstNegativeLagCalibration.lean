import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheWeilFloorOfACurveIsItsZeroWidth
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold

/-!
# Function-Field Calibration of the Square-Root Threshold and the First-Negative-Lag Law

Over `𝔽_q`, the scaling surface `D.curveConfig hD` of a curve datum `D` (`q > 1`, `N = 2g`
normalized Frobenius eigenvalues `β_i` closed under conjugation and `β ↦ 1/β`) has the exact lag
formula (`W_curveConfig_lagFormula`):
`W(f, f) = log q · ∑_{m ∈ ℤ} (f ⋆ f̃)(m log q) · t_{|m|}`, where `t_m = D.trace m = Re ∑_i β_i^m`
and `t_0 = N = 2g`.

This module calibrates both pillars of the Square-Root Threshold programme — the **all-test
threshold aperture** and the **one-parameter two-bump lag comb** — on `D.curveConfig hD` and on
the golden fake curve `goldenDatum`:

1. **Calibration of the All-Test Threshold Aperture (`curveConfig_weil_nonneg_iff_negIndex_spanGram_eq_zero`,
   `curveConfig_weil_nonneg_of_le_half_log_q`, `curveConfig_weil_nonneg_iff_unitary_of_card_le`,
   `goldenDatum_weil_nonneg_iff_le_half_log_five`):**
   - For every aperture `a > 0`, all-test Weil positivity on `[-a, a]` holds iff the Frobenius
     window Gram matrix `D.spanGram ⌈2a / log q⌉₊` has zero negative index.
   - Below `a ≤ log q / 2`, every curve datum in the strip is unconditionally Weil-nonnegative on
     `[-a, a]`, whatever its outer eigenvalues (`curveConfig_weil_nonneg_of_le_half_log_q`).
   - Once the window size `⌈2a / log q⌉₊` reaches the number of eigenvalues `N = 2g`
     (`a > (2g − 1) log q / 2`), all-test Weil positivity at aperture `a` holds iff the curve is
     pure (`∀ i, ‖D.β i‖ = 1`), uniformly in the depth (`curveConfig_weil_nonneg_iff_unitary_of_card_le`).
   - On the golden fake curve `goldenDatum` (`q = 5`, `β = (φ, φ⁻¹)`, `N = 2`), all-test Weil
     positivity at aperture `a > 0` holds iff `a ≤ log 5 / 2`
     (`goldenDatum_weil_nonneg_iff_le_half_log_five`).

2. **The SRT Two-Bump Comb on a Curve (`re_W_curveConfig_twoBump_neg_one_nonneg_of_le`,
   `W_curveConfig_twoBump_neg_one_nat_mul`, `re_W_curveConfig_twoBump_neg_one_nat_mul`,
   `W_curveConfig_twoBump_neg_one_gap`):**
   - For `0 < w` and `0 ≤ v ≤ log q − 2w` (aperture `v/2 + w ≤ log q / 2`), the SRT difference
     test `f_v = κ_w(t + v/2) − κ_w(t − v/2)` satisfies `0 ≤ Re W(f_v, f_v)` on every curve datum.
   - For `4w < log q` and `n ≥ 1`, at the `n`-th Frobenius tooth `v = n log q`,
     `W(f_{n log q}, f_{n log q}) = 2 log q · ‖κ_w‖² · (D.trace 0 − D.trace n) = 2 log q · ‖κ_w‖² · (2g − t_n)`.
   - Off the teeth (`v > 2w` and `|v − n log q| > 2w` for all `n ≥ 1`),
     `W(f_v, f_v) = 2 log q · ‖κ_w‖² · D.trace 0 = 4g log q · ‖κ_w‖² > 0`: between the Frobenius
     lags `n log q`, tests of arbitrarily large lag see only `t_0 = 2g`.

3. **Calibration of the First-Negative-Lag Law (`curveConfig_twoBump_neg_one_nat_mul_neg_iff`,
   `curveConfig_lagTest_nonneg_iff_unitary`, `goldenDatum_twoBump_neg_one_nat_mul_neg`,
   `goldenDatum_twoBump_comb_at_threshold`):**
   - The `n`-th tooth `v = n log q` of the SRT difference family is negative iff `2g < t_n`
     (`curveConfig_twoBump_neg_one_nat_mul_neg_iff`).
   - For any narrow nonzero bump `g` (`w < log q`), nonnegativity of the two-bump lag tests
     `g ± g(· − n log q)` across all `n ≥ 1` is equivalent to purity (`∀ i, ‖D.β i‖ = 1`), with
     Turán's power-sum theorem locating a negative tooth in `[M + 1, M + 2g]`
     (`curveConfig_lagTest_nonneg_iff_unitary`).
   - On `goldenDatum`, `φ^n + φ^{−n} > 2` for every `n ≥ 1`, so the pure difference family (`τ = −1`)
     is nonnegative for `0 ≤ v ≤ log 5 − 2w`, strictly negative at **every** tooth `v = n log 5`
     (`n ≥ 1`, starting at `v = log 5`, aperture `log 5 / 2 + w`), and strictly positive in every
     gap (`goldenDatum_twoBump_comb_at_threshold`).
-/

open Complex MeasureTheory Finset Set
open scoped Real ComplexConjugate
open Zeta23 _root_.RHTower GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-! ### 1. Calibration of the all-test threshold aperture on `D.curveConfig` -/

/-- **All-test Weil positivity on a curve is window Gram positivity.** For `a > 0`, every `C²` test
supported in `[-a, a]` has `0 ≤ Re W(f, f)` on `D.curveConfig hD` iff the Frobenius window Gram
`D.spanGram ⌈2a / log q⌉₊` has zero negative index. -/
theorem curveConfig_weil_nonneg_iff_negIndex_spanGram_eq_zero {a : ℝ} (ha : 0 < a) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((D.curveConfig hD).W f f).re) ↔
      hermNegIndex (D.spanGram ⌈2 * a / Real.log D.q⌉₊) = 0 := by
  rw [weil_nonneg_iff_toeplitz_of_lagFormula (D.curveConfig hD) D.log_q_pos
    (fun m : ℤ => (D.trace m.natAbs : ℂ)) (fun f hf hfc => D.W_curveConfig_lagFormula hD hf hfc) ha,
    D.toeplitz_trace_nonneg_iff]

/-- **Universal sub-threshold silence below `log q / 2`.** Every curve datum in the strip is
Weil-nonnegative on all `C²` tests supported in `[-a, a]` for `a ≤ log q / 2`, whether pure or not. -/
theorem curveConfig_weil_nonneg_of_le_half_log_q {a : ℝ} (ha : a ≤ Real.log D.q / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((D.curveConfig hD).W f f).re := by
  have hL := D.log_q_pos
  have hsub : tsupport f ⊆ Icc (-(Real.log D.q / 2)) (Real.log D.q / 2) :=
    hfs.trans (Icc_subset_Icc (by linarith) ha)
  have hn : ⌈2 * (Real.log D.q / 2) / Real.log D.q⌉₊ ≤ 1 :=
    Nat.ceil_le.mpr (by rw [Nat.cast_one, div_le_iff₀ hL]; linarith)
  exact (curveConfig_weil_nonneg_iff_negIndex_spanGram_eq_zero D hD (half_pos hL)).mpr
    (D.negIndex_spanGram_eq_zero_of_le_one hn) f hf hsub

/-- **The Nyquist / square-root threshold of a curve.** Once `⌈2a / log q⌉₊ ≥ Fintype.card ι`
(`a > (2g − 1) log q / 2`, `a > 0`), all-test Weil positivity at aperture `a` holds iff the curve
is pure (`∀ i, ‖D.β i‖ = 1`). -/
theorem curveConfig_weil_nonneg_iff_unitary_of_card_le {a : ℝ} (ha : 0 < a)
    (hcard : Fintype.card ι ≤ ⌈2 * a / Real.log D.q⌉₊) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((D.curveConfig hD).W f f).re) ↔
      (∀ i, ‖D.β i‖ = 1) := by
  rw [curveConfig_weil_nonneg_iff_negIndex_spanGram_eq_zero D hD ha,
    D.pontryagin_law_curve.2 _ hcard, D.unitary_iff_negIndex_spanGram_eq_zero,
    D.pontryagin_law_curve.2 _ le_rfl]

open Real in
/-- **Sharp threshold calibration on the golden fake curve.** For `a > 0`, `goldenDatum` is
Weil-nonnegative on `[-a, a]` iff `a ≤ log 5 / 2`. -/
theorem goldenDatum_weil_nonneg_iff_le_half_log_five {a : ℝ} (ha : 0 < a) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((goldenDatum.curveConfig goldenDatum_strip).W f f).re) ↔
      a ≤ Real.log 5 / 2 := by
  have hq : goldenDatum.q = 5 := rfl
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [curveConfig_weil_nonneg_iff_negIndex_spanGram_eq_zero goldenDatum goldenDatum_strip ha, hq]
  constructor
  · intro h0
    by_contra hgt
    push Not at hgt
    have hn : 2 ≤ ⌈2 * a / Real.log 5⌉₊ := by
      have h1 : ((1 : ℕ) : ℝ) < 2 * a / Real.log 5 := by
        rw [Nat.cast_one, lt_div_iff₀ h5]; linarith
      have := Nat.lt_ceil.mpr h1
      omega
    have h1 := goldenDatum_negIndex_spanGram hn
    omega
  · intro hle
    have hn : ⌈2 * a / Real.log 5⌉₊ ≤ 1 :=
      Nat.ceil_le.mpr (by rw [Nat.cast_one, div_le_iff₀ h5]; linarith)
    exact goldenDatum.negIndex_spanGram_eq_zero_of_le_one hn

/-! ### 2. The SRT two-bump comb on a curve -/

/-- **Sub-threshold silence of the SRT difference family on a curve.** For `0 < w` and
`0 ≤ v ≤ log q − 2w` (aperture `v/2 + w ≤ log q / 2`), the difference test
`twoBump (modScaledBump w 0) v (-1)` has `0 ≤ Re W` on every curve datum in the strip. -/
theorem re_W_curveConfig_twoBump_neg_one_nonneg_of_le {w v : ℝ} (hw : 0 < w) (hv0 : 0 ≤ v)
    (hv : v ≤ Real.log D.q - 2 * w) :
    0 ≤ ((D.curveConfig hD).W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re :=
  curveConfig_weil_nonneg_of_le_half_log_q D hD (a := v / 2 + w) (by linarith)
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (tsupport_twoBump_modScaledBump_subset hw hv0)

/-- **Teeth of the SRT difference family on a curve.** For `0 < w` with `4w < log q` and `n ≥ 1`,
at the `n`-th Frobenius tooth `v = n log q`,
`W(f_{n log q}, f_{n log q}) = 2 log q · ‖κ_w‖² · (D.trace 0 − D.trace n)`. -/
theorem W_curveConfig_twoBump_neg_one_nat_mul {w : ℝ} (hw : 0 < w) (hwL : 4 * w < Real.log D.q)
    {n : ℕ} (hn : 1 ≤ n) :
    (D.curveConfig hD).W (twoBump (modScaledBump w 0) (n * Real.log D.q) (-1))
        (twoBump (modScaledBump w 0) (n * Real.log D.q) (-1)) =
      ((2 * Real.log D.q * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
        (D.trace 0 - D.trace n) : ℝ) : ℂ) := by
  rw [W_lag_nat_mul_of_lagFormula (D.curveConfig hD) (fun m : ℤ => (D.trace m.natAbs : ℂ))
    (fun f hf hfc => D.W_curveConfig_lagFormula hD hf hfc) hw hwL hn]
  simp only [Int.natAbs_zero, Int.natAbs_neg, Int.natAbs_natCast]
  push_cast
  ring

theorem re_W_curveConfig_twoBump_neg_one_nat_mul {w : ℝ} (hw : 0 < w) (hwL : 4 * w < Real.log D.q)
    {n : ℕ} (hn : 1 ≤ n) :
    ((D.curveConfig hD).W (twoBump (modScaledBump w 0) (n * Real.log D.q) (-1))
        (twoBump (modScaledBump w 0) (n * Real.log D.q) (-1))).re =
      2 * Real.log D.q * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * (Fintype.card ι - D.trace n) := by
  rw [W_curveConfig_twoBump_neg_one_nat_mul D hD hw hwL hn, Complex.ofReal_re, D.trace_zero]

/-- **Gaps of the SRT difference family on a curve.** For `0 < w` with `4w < log q`, `v > 2w`, and
`|v − n log q| > 2w` for every `n ≥ 1`,
`W(f_v, f_v) = 2 log q · ‖κ_w‖² · D.trace 0 = 2 log q · ‖κ_w‖² · 2g > 0`. -/
theorem W_curveConfig_twoBump_neg_one_gap {w : ℝ} (hw : 0 < w) (hwL : 4 * w < Real.log D.q)
    {v : ℝ} (hv : 2 * w < v) (hgap : ∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * Real.log D.q|) :
    (D.curveConfig hD).W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)) =
      ((2 * Real.log D.q * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * Fintype.card ι : ℝ) : ℂ) := by
  rw [W_lag_eq_of_gap_of_lagFormula (D.curveConfig hD) (fun m : ℤ => (D.trace m.natAbs : ℂ))
    (fun f hf hfc => D.W_curveConfig_lagFormula hD hf hfc) hw hwL hv hgap]
  simp only [Int.natAbs_zero, D.trace_zero]
  push_cast
  ring

/-! ### 3. Calibration of the first-negative-lag law on a curve and on `goldenDatum` -/

/-- **Tooth negativity criterion for the SRT difference family.** For `0 < w` with `4w < log q` and
`n ≥ 1`, the `n`-th tooth `v = n log q` has negative Weil form iff `Fintype.card ι < D.trace n`. -/
theorem curveConfig_twoBump_neg_one_nat_mul_neg_iff {w : ℝ} (hw : 0 < w)
    (hwL : 4 * w < Real.log D.q) {n : ℕ} (hn : 1 ≤ n) :
    ((D.curveConfig hD).W (twoBump (modScaledBump w 0) (n * Real.log D.q) (-1))
        (twoBump (modScaledBump w 0) (n * Real.log D.q) (-1))).re < 0 ↔
      (Fintype.card ι : ℝ) < D.trace n := by
  rw [re_W_curveConfig_twoBump_neg_one_nat_mul D hD hw hwL hn]
  have hpos : 0 < 2 * Real.log D.q * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 :=
    mul_pos (mul_pos two_pos D.log_q_pos) (integral_norm_sq_modScaledBump_pos hw)
  constructor
  · intro hlt
    by_contra hge
    have hnn : 0 ≤ 2 * Real.log D.q * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) *
        ((Fintype.card ι : ℝ) - D.trace n) :=
      mul_nonneg hpos.le (by linarith)
    linarith
  · intro hlt
    exact mul_neg_of_pos_of_neg hpos (by linarith)

/-- **Purity is lag positivity on `D.curveConfig`.** For a narrow nonzero bump `g` (`w < log q`),
every lag test `lagTest g s (n log q)` (`n ≥ 1`, `s = ±1`) has nonnegative Weil form iff every
eigenvalue lies on the unit circle (`∀ i, ‖D.β i‖ = 1`). -/
theorem curveConfig_lagTest_nonneg_iff_unitary {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(w / 2)) (w / 2)) (hwL : w < Real.log D.q)
    (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) :
    (∀ (n : ℕ) (s : ℝ), 1 ≤ n → (s = 1 ∨ s = -1) →
      0 ≤ ((D.curveConfig hD).W (lagTest g s (n * Real.log D.q))
        (lagTest g s (n * Real.log D.q))).re) ↔
      (∀ i, ‖D.β i‖ = 1) := by
  constructor
  · intro hpos i
    have hle : ∀ j, ‖D.β j‖ ≤ 1 := fun j => by
      by_contra hgt
      push Not at hgt
      obtain ⟨n, hn1, s, hs, hneg⟩ := D.exists_negative_lagTest hD hgt hg hgs hwL hg0
      exact absurd (hpos n s hn1 hs) (not_le.mpr hneg)
    refine le_antisymm (hle i) ?_
    have h := hle (D.reflPerm i)
    rw [D.β_reflPerm, norm_circleReflect] at h
    exact (inv_le_one₀ (norm_pos_iff.mpr (D.β_ne_zero i))).mp h
  · intro hU n s _ _
    exact D.re_W_curveConfig_lagTest_nonneg hD (fun i => (hU i).le) hg hgs hwL s n

open Real in
/-- On `goldenDatum`, `φ^n + φ^{−n} > 2` for every `n ≥ 1`, so **every** tooth `v = n log 5`
(`n ≥ 1`) of the SRT difference family `twoBump (modScaledBump w 0) (n * log 5) (-1)` is strictly
negative (`4w < log 5`). -/
theorem goldenDatum_twoBump_neg_one_nat_mul_neg {w : ℝ} (hw : 0 < w)
    (hwL : 4 * w < Real.log goldenDatum.q) {n : ℕ} (hn : 1 ≤ n) :
    ((goldenDatum.curveConfig goldenDatum_strip).W
      (twoBump (modScaledBump w 0) (n * Real.log goldenDatum.q) (-1))
      (twoBump (modScaledBump w 0) (n * Real.log goldenDatum.q) (-1))).re < 0 := by
  rw [curveConfig_twoBump_neg_one_nat_mul_neg_iff goldenDatum goldenDatum_strip hw hwL hn,
    goldenDatum_trace, Fintype.card_fin]
  push_cast
  have hφ1 : 1 < goldenRatio ^ n := one_lt_pow₀ one_lt_goldenRatio (by omega)
  have hφpos : 0 < goldenRatio ^ n := pow_pos goldenRatio_pos n
  have hsq : 0 < (goldenRatio ^ n - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hinv : (goldenRatio⁻¹) ^ n * goldenRatio ^ n = 1 := by
    rw [inv_pow, inv_mul_cancel₀ hφpos.ne']
  nlinarith [mul_pos hsq (inv_pos.mpr hφpos)]

open Real in
/-- **Threshold-exact comb calibration on the golden fake curve.** For `0 < w` with
`4w < log 5`:
1. **(Silence up to the threshold):** For `0 ≤ v ≤ log 5 − 2w` (aperture `≤ log 5 / 2`),
   `0 ≤ Re W(f_v, f_v)`;
2. **(Every tooth is negative, starting at the threshold):** For every `n ≥ 1`, at `v = n log 5`
   (`v = log 5` has aperture `log 5 / 2 + w`), `Re W(f_{n log 5}, f_{n log 5}) < 0`;
3. **(Positive gaps beyond the threshold):** For every `v > 2w` with `|v − n log 5| > 2w` for all
   `n ≥ 1`, `Re W(f_v, f_v) = 4 log 5 · ‖κ_w‖² > 0`. -/
theorem goldenDatum_twoBump_comb_at_threshold {w : ℝ} (hw : 0 < w)
    (hwL : 4 * w < Real.log goldenDatum.q) :
    (∀ v : ℝ, 0 ≤ v → v ≤ Real.log goldenDatum.q - 2 * w →
      0 ≤ ((goldenDatum.curveConfig goldenDatum_strip).W
        (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re) ∧
    (∀ n : ℕ, 1 ≤ n →
      ((goldenDatum.curveConfig goldenDatum_strip).W
        (twoBump (modScaledBump w 0) (n * Real.log goldenDatum.q) (-1))
        (twoBump (modScaledBump w 0) (n * Real.log goldenDatum.q) (-1))).re < 0) ∧
    (∀ v : ℝ, 2 * w < v → (∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * Real.log goldenDatum.q|) →
      ((goldenDatum.curveConfig goldenDatum_strip).W
        (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re =
      4 * Real.log goldenDatum.q * ∫ t, ‖modScaledBump w 0 t‖ ^ 2) := by
  refine ⟨fun v hv0 hv =>
    re_W_curveConfig_twoBump_neg_one_nonneg_of_le goldenDatum goldenDatum_strip hw hv0 hv,
    fun n hn => goldenDatum_twoBump_neg_one_nat_mul_neg hw hwL hn, fun v hv hgap => ?_⟩
  rw [W_curveConfig_twoBump_neg_one_gap goldenDatum goldenDatum_strip hw hwL hv hgap,
    Fintype.card_fin, Complex.ofReal_re]
  push_cast
  ring

end GaloisForLFunctions.SquareRootThreshold
