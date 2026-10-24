import GaloisForLFunctions.«arithmetic-positivity-theory».FromTheCriticalFamilyToTheReceiver
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentDepthGapClusterAndPolarGraphBridge
import GaloisForLFunctions.SquareRootThreshold.VisibilityTradeoffAndExcludedDepthLaw
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyHorizonLaw
import GaloisForLFunctions.SquareRootThreshold.ZetaAttainedTopIsVisibleAtAnExplicitLag
import GaloisForLFunctions.SquareRootThreshold.ZetaAttainedTopIsVisibleAtALogarithmicLag
import GaloisForLFunctions.SquareRootThreshold.DifferenceLagFamilyPositiveThroughTheFirstPrime
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DoublyLogarithmicVisibilityAndExcludedDepthLaw

/-!
# Quantitative Grid-Tent Detection, Finite-Scale Complex-to-Tent Approximation, and Excluded-Depth Laws at Fixed Aperture

In `FactorialTentActualZetaDetectionAndFullZeroFormBridge` and
`FactorialTentDepthGapClusterAndPolarGraphBridge`, off-line zero detection by single-scale uniform-grid
factorial-tent patterns (`gridTentPattern`) and their smoothed `C_c²` detectors
(`smoothGridTentDetector`) was established qualitatively via `offLine_visible`,
`finiteOffLine_visible`, `attainedDepth_visible`, and `exists_re_W_neg_of_depthGap_deep_zero`.

Meanwhile, `SquareRootThreshold` and `ArithmeticCastelnuovoSeveri` establish quantitative explicit
visibility lags, excluded-depth thresholds, and horizon heights for `zetaZeroConfig.W` on complex
`C_c²` tests supported in `[-R, R]` (reading prime powers up to arithmetic length `X = e^{2R}`), and
`FromTheCriticalFamilyToTheReceiver` establishes the quantitative finite-scale approximation bound
`abs_compactFullWeilEnergy_gridTentPattern_sub_le` at every arithmetic scale `n : ℕ`.

This module unites these two developments to resolve the quantitative detection problem (§7.6 and
§7.8.3):

1. **Quantitative Finite-Scale Complex-to-Grid-Tent Approximation, Unmodulated Odd Reduction, and
   Fixed-Radius Equivalence (`zeta_W_re_eq_compactFullWeilEnergy_re_add_im`,
   `abs_zeta_W_re_sub_gridTentPattern_re_add_im_le`,
   `zeta_W_re_ge_neg_two_gridTentApproximationConstant_of_gridTentPattern_nonneg_at_scale`,
   `exists_real_or_im_gridTentPattern_neg_at_scale_of_zeta_W_re_lt`,
   `zeta_W_re_twoBump_modScaledBump_zero_eq_compactFullWeilEnergy_re`,
   `abs_zeta_W_re_twoBump_modScaledBump_zero_sub_gridTentPattern_le`,
   `zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius`):**
   - For every complex test `f ∈ C_c²(ℝ, ℂ)` vanishing outside `[-R, R]` (`R ≥ 0`), the real zero-side
     Weil form decomposes into the sum of `compactFullWeilEnergy` on the real and imaginary parts
     `f_re, f_im ∈ C_c(ℝ, ℝ)`, and is approximated at every finite scale `n : ℕ` by the sum of the
     two single-scale grid tent patterns `P_re, P_im` within
     `2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) ≤ C / (6(n + 1))`,
     retaining the prime cutoff `compactFullWeilPrimeCutoff (R + 2)` beyond `2(R + 1)`.
   - Consequently, nonnegativity of `P_re` and `P_im` at a **single finite scale `n`** and radius `R`
     certifies `(zetaZeroConfig.W f f).re ≥ -2 * gridTentApproximationConstant R Mg Kg L * d_{n+1}`
     and excludes at scale `n` any zero configuration whose witness `f` has a more negative Weil value.
   - For unmodulated (`c = 0`) difference lag tests `twoBump (modScaledBump w 0) v (-1)`, the test is
     real-valued and odd, so no real/imaginary splitting is needed: a single odd seed `G` supported in
     `[-(v/2 + w), v/2 + w]` approximates `(zetaZeroConfig.W f f).re` within
     `gridTentApproximationConstant (v/2 + w) Mg Kg L * d_{n+1}`, and inherits the unconditional odd
     positivity window `v/2 + w ≤ 353/1000` past the first prime `(log 2)/2`.
   - At any fixed radius `R ≥ 0`, eventual grid-tent nonnegativity on seeds supported in `[-R, R]`
     implies `(zetaZeroConfig.W f f).re ≥ 0` on all `f ∈ C_c²([-R, R], ℂ)`, `ZetaWindowPositive R`,
     `HodgeIndexAtLevel zetaZeroConfig R`, and (for `R > 0`) `ccmRestrictedWeilGroundEnergy ⟨R, hR⟩ ≥ 0`
     and `R ≤ zetaContactAperture`.

2. **Explicit-Lag Quantitative Grid-Tent Detection across the Visibility Hierarchy
   (`gridTent_detected_of_exists_lag_re_W_neg`,
   `gridTent_odd_detected_of_exists_oneParam_lag_re_W_neg`,
   `actual_zeta_oneParam_near_top_detected_by_gridTentPattern`,
   `actual_zeta_oneParam_horizon_detected_by_gridTentPattern`,
   `zeta_gridTentPattern_nonneg_forces_beyond_oneParamHorizon`,
   `actual_zeta_polylog_near_top_detected_by_gridTentPattern`,
   `actual_zeta_loglog_near_top_detected_by_gridTentPattern_of_offLineCopiesLocallyBounded`,
   `actual_zeta_onLineMass_near_top_detected_by_gridTentPattern_of_offLineCopiesLocallyBounded`,
   `actual_zeta_attained_top_detected_by_gridTentPattern_at_explicit_lag`,
   `actual_zeta_attained_top_detected_by_gridTentPattern_at_log_lag`):**
   Transports the entire quantitative lag-visibility hierarchy to `gridTentPattern` and
   `smoothGridTentDetector` at explicit seed radius `R = V / 2 + w`:
   - Unmodulated (`c = 0`) near-top detection at `V ≥ oneParamLag w η z₀.re` by an **odd** seed `G`,
     plus horizon-law detection (`oneParamHorizon`) and contrapositive beyond-horizon forcing.
   - Modulated (`c = z₀.im`) polylogarithmic near-top detection at `V ≥ nearTopLag w z₀.im z₀.re`.
   - Modulated doubly-logarithmic near-top detection under `OffLineCopiesLocallyBounded M` at
     `V ≥ nearTopLogLogLagOffLine M w z₀.im z₀.re = Θ_{M,w}((1 + log log(|z₀.im| + 4)) / z₀.re)` and
     at `V ≥ nearTopLagOffLine M w W_on z₀.re`.
   - Attained-top detection at explicit `O(1/g)` lag (`zeta_attained_top_first_negative_lag`) and at
     logarithmic `O(log(1/g))` lag (`zeta_attained_top_visible_log`).

3. **Quantitative Excluded-Depth Laws, Horizon Heights, and Two-Way Visibility/Height-Reduction
   Duality for `gridTentPattern` at Fixed Aperture `R`
   (`zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg`,
   `zeta_excluded_depth_below_localCount_clusterHorizon_of_gridTentPattern_nonneg`,
   `zeta_oneParam_excluded_depth_of_gridTentPattern_nonneg`,
   `zeta_polylog_near_top_excluded_depth_of_gridTentPattern_nonneg`,
   `zeta_loglog_near_top_excluded_depth_of_gridTentPattern_nonneg_of_offLineCopiesLocallyBounded`,
   `zeta_equalDepthCluster_excluded_depth_of_gridTentPattern_nonneg`,
   `zeta_gridTentPattern_visibility_and_height_reduction_duality`):**
   - At any aperture `R ≥ e⁶` where `gridTentPattern` is eventually nonnegative on seeds in `[-R, R]`,
     every zero `ρ ∈ zetaZeroConfig.carrier` with `2 ≤ |ρ.im| ≤ zetaClusterHorizonHeight A₀ R` has
     depth `|ρ.re - 1/2| < 1/R = 2/log X` unconditionally, and every zero with local count
     `Nd(ρ₀.im - 101, ρ₀.im + 101) ≤ k` and `2 ≤ |ρ₀.im| ≤ clusterHorizonHeight A₀ k R` has depth
     `|ρ₀.re - 1/2| < 1/R`.
   - At any aperture `R` above the coherence drift, eventual grid-tent nonnegativity on `[-R, R]`
     excludes `1/(2(R - w))`-near-top zeros of depth `≥ oneParamExcludedDepth w η (2(R - w))`,
     `≥ nearTopExcludedDepth w z₀.im (2(R - w))`, and (under `OffLineCopiesLocallyBounded M`)
     `≥ nearTopLogLogExcludedDepthOffLine M w z₀.im (2(R - w))`, as well as equal-depth `k`-pair
     clusters of depth `≥ equalDepthClusterExcludedDepth zetaZeroConfig b δ γ c ℓ w R`.
   - Pairs the forward aperture-to-zero depth exclusion below `zetaClusterHorizonHeight A₁ R` with the
     converse zero-to-aperture finite-scale `gridTentPattern` floor reduction from zeros up to
     `zetaHorizonHeight A₀ R`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators ENNReal CompactlySupported ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Quantitative Finite-Scale Complex-to-Grid-Tent Approximation, Unmodulated Odd Reduction, and Fixed-Radius Equivalence -/

/-- **Real-and-Imaginary Decomposition of `(zetaZeroConfig.W f f).re` into `compactFullWeilEnergy`.**
For every complex test `f ∈ C_c²(ℝ, ℂ)`, the real part of the zero-side Weil form of `ζ` equals the
sum of `compactFullWeilEnergy` (and of `fullZeroForm`) on its real and imaginary parts. -/
theorem zeta_W_re_eq_compactFullWeilEnergy_re_add_im {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    let f_re : C_c(ℝ, ℝ) :=
      ⟨⟨fun x => (f x).re, (Complex.reCLM.contDiff.comp hf).continuous⟩,
        hfc.comp_left Complex.zero_re⟩
    let f_im : C_c(ℝ, ℝ) :=
      ⟨⟨fun x => (f x).im, (Complex.imCLM.contDiff.comp hf).continuous⟩,
        hfc.comp_left Complex.zero_im⟩
    (zetaZeroConfig.W f f).re =
      compactFullWeilEnergy f_re + compactFullWeilEnergy f_im ∧
    (zetaZeroConfig.W f f).re =
      fullZeroForm (fun x => (f x).re) + fullZeroForm (fun x => (f x).im) := by
  dsimp only
  set f_re : C_c(ℝ, ℝ) :=
    ⟨⟨fun x => (f x).re, (Complex.reCLM.contDiff.comp hf).continuous⟩,
      hfc.comp_left Complex.zero_re⟩
  set f_im : C_c(ℝ, ℝ) :=
    ⟨⟨fun x => (f x).im, (Complex.imCLM.contDiff.comp hf).continuous⟩,
      hfc.comp_left Complex.zero_im⟩
  have h1 := zeta_W_re_eq_fullZeroForm_re_add_im hf hfc
  have h2 := fullZeroForm_eq_compactFullWeilEnergy f_re
  have h3 := fullZeroForm_eq_compactFullWeilEnergy f_im
  exact ⟨by rw [h1, ← h2, ← h3]; rfl, h1⟩

/-- **Quantitative Finite-Scale Complex-to-Grid-Tent Approximation Law.**
For every complex test `f ∈ C_c²(ℝ, ℂ)` vanishing outside `[-R, R]` (`R ≥ 0`) with envelope and
Lipschitz constants `(Mg, Kg, L)` on its real and imaginary parts, and every arithmetic scale
`n : ℕ`, the sum of `compactFullWeilEnergy` on the two single-scale grid tent patterns `P_re` and
`P_im` approximates `(zetaZeroConfig.W f f).re` within
`2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1)` (and within
`gridTentApproximationConstant R Mg Kg L / (6 * (n + 1))`), retaining the prime cutoff
`compactFullWeilPrimeCutoff (R + 2)` beyond `2(R + 1)`. -/
theorem abs_zeta_W_re_sub_gridTentPattern_re_add_im_le {f : ℝ → ℂ} {R Mg Kg L : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 ≤ R)
    (hfR : ∀ x, R < |x| → f x = 0)
    (hMg_re : ∀ x, |(f x).re| ≤ Mg) (hMg_im : ∀ x, |(f x).im| ≤ Mg)
    (hKg_re : ∀ x y, |(f x).re - (f y).re| ≤ Kg * |x - y|)
    (hKg_im : ∀ x y, |(f x).im - (f y).im| ≤ Kg * |x - y|)
    (hGL_re : ∀ x y, |Real.exp (-(3 * x / 2)) * (f x).re -
      Real.exp (-(3 * y / 2)) * (f y).re| ≤ L * |x - y|)
    (hGL_im : ∀ x y, |Real.exp (-(3 * x / 2)) * (f x).im -
      Real.exp (-(3 * y / 2)) * (f y).im| ≤ L * |x - y|)
    (n : ℕ) :
    let G_re : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * (f x).re
    let G_im : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * (f x).im
    let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    let P_re : C_c(ℝ, ℝ) := gridTentPattern G_re n (-(R + 1)) M
    let P_im : C_c(ℝ, ℝ) := gridTentPattern G_im n (-(R + 1)) M
    |(compactFullWeilEnergy P_re + compactFullWeilEnergy P_im) - (zetaZeroConfig.W f f).re| ≤
      2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) ∧
    |(compactFullWeilEnergy P_re + compactFullWeilEnergy P_im) - (zetaZeroConfig.W f f).re| ≤
      gridTentApproximationConstant R Mg Kg L / (6 * ((n : ℝ) + 1)) := by
  dsimp only
  set f_re : C_c(ℝ, ℝ) :=
    ⟨⟨fun x => (f x).re, (Complex.reCLM.contDiff.comp hf).continuous⟩,
      hfc.comp_left Complex.zero_re⟩
  set f_im : C_c(ℝ, ℝ) :=
    ⟨⟨fun x => (f x).im, (Complex.imCLM.contDiff.comp hf).continuous⟩,
      hfc.comp_left Complex.zero_im⟩
  have hreR : ∀ x, R < |x| → f_re x = 0 := fun x hx => by simp [f_re, hfR x hx]
  have himR : ∀ x, R < |x| → f_im x = 0 := fun x hx => by simp [f_im, hfR x hx]
  set P_re : C_c(ℝ, ℝ) := gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * (f x).re)
    n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  set P_im : C_c(ℝ, ℝ) := gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * (f x).im)
    n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  have h1 : |compactFullWeilEnergy P_re - compactFullWeilEnergy f_re| ≤
      gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) :=
    abs_compactFullWeilEnergy_gridTentPattern_sub_le f_re hR hreR hMg_re hKg_re hGL_re n
  have h2 : |compactFullWeilEnergy P_im - compactFullWeilEnergy f_im| ≤
      gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) :=
    abs_compactFullWeilEnergy_gridTentPattern_sub_le f_im hR himR hMg_im hKg_im hGL_im n
  have h3 : |compactFullWeilEnergy P_re - compactFullWeilEnergy f_re| ≤
      gridTentApproximationConstant R Mg Kg L / (12 * ((n : ℝ) + 1)) :=
    abs_compactFullWeilEnergy_gridTentPattern_sub_le_inv_scale f_re hR hreR hMg_re hKg_re hGL_re n
  have h4 : |compactFullWeilEnergy P_im - compactFullWeilEnergy f_im| ≤
      gridTentApproximationConstant R Mg Kg L / (12 * ((n : ℝ) + 1)) :=
    abs_compactFullWeilEnergy_gridTentPattern_sub_le_inv_scale f_im hR himR hMg_im hKg_im hGL_im n
  have hsplit := (zeta_W_re_eq_compactFullWeilEnergy_re_add_im hf hfc).1
  have hdiff : (compactFullWeilEnergy P_re + compactFullWeilEnergy P_im) - (zetaZeroConfig.W f f).re =
      (compactFullWeilEnergy P_re - compactFullWeilEnergy f_re) +
        (compactFullWeilEnergy P_im - compactFullWeilEnergy f_im) := by
    linarith [hsplit]
  have habs := abs_add_le (compactFullWeilEnergy P_re - compactFullWeilEnergy f_re)
    (compactFullWeilEnergy P_im - compactFullWeilEnergy f_im)
  rw [← hdiff] at habs
  refine ⟨by linarith, ?_⟩
  have h6 : gridTentApproximationConstant R Mg Kg L / (12 * ((n : ℝ) + 1)) +
      gridTentApproximationConstant R Mg Kg L / (12 * ((n : ℝ) + 1)) =
      gridTentApproximationConstant R Mg Kg L / (6 * ((n : ℝ) + 1)) := by
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hn1]
    ring
  linarith

/-- **Single-Scale Finite-`n` Lower Floor for Complex Receiver Tests from Grid-Tent Positivity.**
If at a single arithmetic scale `n : ℕ` and radius `R ≥ 0`, the grid tent patterns `P_re` and `P_im`
of `f ∈ C_c²([-R, R], ℂ)` have nonnegative `compactFullWeilEnergy`, then `(zetaZeroConfig.W f f).re`
is bounded below by `-2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1)`
(and the reflection defect excess is bounded above by the same quantity). -/
theorem zeta_W_re_ge_neg_two_gridTentApproximationConstant_of_gridTentPattern_nonneg_at_scale
    {f : ℝ → ℂ} {R Mg Kg L : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 ≤ R)
    (hfR : ∀ x, R < |x| → f x = 0)
    (hMg_re : ∀ x, |(f x).re| ≤ Mg) (hMg_im : ∀ x, |(f x).im| ≤ Mg)
    (hKg_re : ∀ x y, |(f x).re - (f y).re| ≤ Kg * |x - y|)
    (hKg_im : ∀ x y, |(f x).im - (f y).im| ≤ Kg * |x - y|)
    (hGL_re : ∀ x y, |Real.exp (-(3 * x / 2)) * (f x).re -
      Real.exp (-(3 * y / 2)) * (f y).re| ≤ L * |x - y|)
    (hGL_im : ∀ x y, |Real.exp (-(3 * x / 2)) * (f x).im -
      Real.exp (-(3 * y / 2)) * (f y).im| ≤ L * |x - y|)
    (n : ℕ)
    (hPre : 0 ≤ compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * (f x).re)
      n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊))
    (hPim : 0 ≤ compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * (f x).im)
      n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) :
    -2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) ≤
      (zetaZeroConfig.W f f).re ∧
    configurationReflectionDefect zetaZeroConfig f - configurationSquareMass zetaZeroConfig f ≤
      2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) := by
  have happrox := (abs_zeta_W_re_sub_gridTentPattern_re_add_im_le hf hfc hR hfR
    hMg_re hMg_im hKg_re hKg_im hGL_re hGL_im n).1
  have hup := (abs_le.mp happrox).2
  have hrefl := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  exact ⟨by linarith, by linarith⟩

/-- **Single-Scale Finite-`n` Grid-Tent Detection Criterion for Complex Witness Tests.**
If `f ∈ C_c²([-R, R], ℂ)` satisfies
`(zetaZeroConfig.W f f).re ≤ -2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) - 2 * μ`
at a single finite scale `n : ℕ`, then at that exact scale `n` at least one of the two grid tent
patterns `P_re` or `P_im` has `compactFullWeilEnergy ≤ -μ`. -/
theorem exists_real_or_im_gridTentPattern_neg_at_scale_of_zeta_W_re_le
    {f : ℝ → ℂ} {R Mg Kg L μ : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 ≤ R)
    (hfR : ∀ x, R < |x| → f x = 0)
    (hMg_re : ∀ x, |(f x).re| ≤ Mg) (hMg_im : ∀ x, |(f x).im| ≤ Mg)
    (hKg_re : ∀ x y, |(f x).re - (f y).re| ≤ Kg * |x - y|)
    (hKg_im : ∀ x y, |(f x).im - (f y).im| ≤ Kg * |x - y|)
    (hGL_re : ∀ x y, |Real.exp (-(3 * x / 2)) * (f x).re -
      Real.exp (-(3 * y / 2)) * (f y).re| ≤ L * |x - y|)
    (hGL_im : ∀ x y, |Real.exp (-(3 * x / 2)) * (f x).im -
      Real.exp (-(3 * y / 2)) * (f y).im| ≤ L * |x - y|)
    (n : ℕ)
    (hW : (zetaZeroConfig.W f f).re ≤
      -2 * gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) - 2 * μ) :
    let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    let P_re : C_c(ℝ, ℝ) := gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * (f x).re) n (-(R + 1)) M
    let P_im : C_c(ℝ, ℝ) := gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * (f x).im) n (-(R + 1)) M
    compactFullWeilEnergy P_re ≤ -μ ∨ compactFullWeilEnergy P_im ≤ -μ := by
  dsimp only
  have happrox := (abs_zeta_W_re_sub_gridTentPattern_re_add_im_le hf hfc hR hfR
    hMg_re hMg_im hKg_re hKg_im hGL_re hGL_im n).1
  have hup := (abs_le.mp happrox).2
  by_contra hcon
  push Not at hcon
  linarith [hcon.1, hcon.2]

/-- The unmodulated difference test `twoBump (modScaledBump w 0) v (-1)` has identically zero
imaginary part and odd real part. -/
theorem im_twoBump_modScaledBump_zero_eq_zero_and_re_odd (w v x : ℝ) :
    (twoBump (modScaledBump w 0) v (-1) x).im = 0 ∧
    (twoBump (modScaledBump w 0) v (-1) (-x)).re =
      -(twoBump (modScaledBump w 0) v (-1) x).re := by
  have hconj := twoBump_modScaledBump_zero_conj w v x
  have him : (twoBump (modScaledBump w 0) v (-1) x).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  have hodd := congrArg Complex.re (twoBump_modScaledBump_zero_neg w v x)
  simp only [Complex.neg_re] at hodd
  exact ⟨him, hodd⟩

/-- **Exact Odd Real Reduction for Unmodulated Difference Lag Tests (`c = 0`).**
Because `twoBump (modScaledBump w 0) v (-1)` is real-valued and odd, its zero-side Weil form
`(zetaZeroConfig.W f f).re` equals `compactFullWeilEnergy` (and `fullZeroForm`) of its odd real part
`φ(x) = (twoBump (modScaledBump w 0) v (-1) x).re`, which is `C²` and vanishes outside
`[-(v/2 + w), v/2 + w]`. -/
theorem zeta_W_re_twoBump_modScaledBump_zero_eq_compactFullWeilEnergy_re
    {w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v) :
    let f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1)
    let φ : ℝ → ℝ := fun x => (f x).re
    have hφ : ContDiff ℝ 2 φ :=
      Complex.reCLM.contDiff.comp (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    have hφc : HasCompactSupport φ :=
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) v (-1)).comp_left Complex.zero_re
    let φc : C_c(ℝ, ℝ) := ⟨⟨φ, hφ.continuous⟩, hφc⟩
    (∀ x, φ (-x) = -φ x) ∧
    (∀ x, v / 2 + w < |x| → φ x = 0) ∧
    (zetaZeroConfig.W f f).re = fullZeroForm φ ∧
    (zetaZeroConfig.W f f).re = compactFullWeilEnergy φc := by
  dsimp only
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1)
  set φ : ℝ → ℝ := fun x => (f x).re
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)
  have hφ : ContDiff ℝ 2 φ := Complex.reCLM.contDiff.comp hf
  have hφc : HasCompactSupport φ := hfc.comp_left Complex.zero_re
  set φc : C_c(ℝ, ℝ) := ⟨⟨φ, hφ.continuous⟩, hφc⟩
  have hodd : ∀ x, φ (-x) = -φ x := fun x => (im_twoBump_modScaledBump_zero_eq_zero_and_re_odd w v x).2
  have hsupp := tsupport_twoBump_modScaledBump_subset_any 0 hw hv
  have hφR : ∀ x, v / 2 + w < |x| → φ x = 0 := fun x hx => by
    have hfx : f x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := abs_le.mpr (hsupp hmem)
      linarith
    simp [φ, hfx]
  have hf_eq : f = fun x => (φ x : ℂ) := by
    funext x
    apply Complex.ext
    · simp [φ]
    · simp only [Complex.ofReal_im]
      exact (im_twoBump_modScaledBump_zero_eq_zero_and_re_odd w v x).1
  have hW : (zetaZeroConfig.W f f).re = fullZeroForm φ := by
    rw [hf_eq, ← fullZeroForm_eq_zeta_W_re hφ hφc]
  exact ⟨hodd, hφR, hW, hW.trans (fullZeroForm_eq_compactFullWeilEnergy φc)⟩

/-- **Single-Seed Quantitative Finite-Scale Approximation for Unmodulated Difference Lag Tests.**
For `0 < w`, `0 ≤ v ≤ V`, and `V / 2 + w ≤ R`, a single odd real seed
`G(x) = e^{-3x/2} (twoBump (modScaledBump w 0) v (-1) x).re` approximates
`(zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re`
at every scale `n : ℕ` within `gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1)`
(with no imaginary-part pattern needed). -/
theorem abs_zeta_W_re_twoBump_modScaledBump_zero_sub_gridTentPattern_le
    {w v R Mg Kg L : ℝ} (hw : 0 < w) (hv : 0 ≤ v) (hR : v / 2 + w ≤ R)
    (hMg : ∀ x, |(twoBump (modScaledBump w 0) v (-1) x).re| ≤ Mg)
    (hKg : ∀ x y, |(twoBump (modScaledBump w 0) v (-1) x).re -
      (twoBump (modScaledBump w 0) v (-1) y).re| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * (twoBump (modScaledBump w 0) v (-1) x).re -
      Real.exp (-(3 * y / 2)) * (twoBump (modScaledBump w 0) v (-1) y).re| ≤ L * |x - y|)
    (n : ℕ) :
    let φ : ℝ → ℝ := fun x => (twoBump (modScaledBump w 0) v (-1) x).re
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
    let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
    |compactFullWeilEnergy P -
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re| ≤
      gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) := by
  dsimp only
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1)
  set φ : ℝ → ℝ := fun x => (f x).re
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)
  have hφ : ContDiff ℝ 2 φ := Complex.reCLM.contDiff.comp hf
  have hφc : HasCompactSupport φ := hfc.comp_left Complex.zero_re
  set φc : C_c(ℝ, ℝ) := ⟨⟨φ, hφ.continuous⟩, hφc⟩
  obtain ⟨-, hφ_supp, -, hW_eq⟩ :=
    zeta_W_re_twoBump_modScaledBump_zero_eq_compactFullWeilEnergy_re hw hv
  have hR0 : 0 ≤ R := by linarith
  have hφR : ∀ x, R < |x| → φc x = 0 := fun x hx => hφ_supp x (by linarith)
  rw [hW_eq]
  exact abs_compactFullWeilEnergy_gridTentPattern_sub_le φc hR0 hφR hMg hKg hGL n

/-- **Fixed-Radius Equivalence: Eventual Grid-Tent Positivity at Aperture `R` Implies
`ZetaWindowPositive R`, `HodgeIndexAtLevel zetaZeroConfig R`, Nonnegative Ground Energy, and
`R ≤ zetaContactAperture`.**
If at a fixed radius `R ≥ 0`, every seed `G ∈ C_c²(ℝ, ℝ)` vanishing outside `[-R, R]` has
eventually nonnegative `compactFullWeilEnergy` on `gridTentPattern G n (-(R + 1)) M_n`, then:
1. `ZetaWindowPositive R` holds,
2. `HodgeIndexAtLevel zetaZeroConfig R` holds,
3. every complex test `f ∈ C_c²([-R, R], ℂ)` satisfies `0 ≤ (zetaZeroConfig.W f f).re` and
   `configurationReflectionDefect zetaZeroConfig f ≤ configurationSquareMass zetaZeroConfig f`, and
4. if `0 < R`, then `0 ≤ ccmRestrictedWeilGroundEnergy ⟨R, hR⟩` and
   `¬ RiemannHypothesis → R ≤ zetaContactAperture`. -/
theorem zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) :
    ZetaWindowPositive R ∧
    HodgeIndexAtLevel zetaZeroConfig R ∧
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-R) R →
      0 ≤ (zetaZeroConfig.W f f).re ∧
      configurationReflectionDefect zetaZeroConfig f ≤
        configurationSquareMass zetaZeroConfig f) ∧
    (∀ hR0 : 0 < R, 0 ≤ ccmRestrictedWeilGroundEnergy ⟨R, hR0⟩ ∧
      (¬ RiemannHypothesis → R ≤ zetaContactAperture)) := by
  have hWin : ZetaWindowPositive R := by
    intro F hF hFc hFR
    by_contra hneg
    push Not at hneg
    have hspec := gridTentPattern_actual_zeta_detector_spec hF hFc hR hFR hneg
    set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
    have hG : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
    have hGc : HasCompactSupport G := hFc.mul_left
    have hGR : ∀ x, R < |x| → G x = 0 := fun x hx => by simp [G, hFR x hx]
    obtain ⟨n, hn_neg, hn_pos⟩ := (hspec.2.and (hpos G hG hGc hGR)).exists
    linarith [hn_neg.1, hspec.1]
  have hHodge : HodgeIndexAtLevel zetaZeroConfig R :=
    hodgeIndexAtLevel_of_zetaWindowPositive hWin
  have hAll : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-R) R →
      0 ≤ (zetaZeroConfig.W f f).re ∧
      configurationReflectionDefect zetaZeroConfig f ≤
        configurationSquareMass zetaZeroConfig f := by
    intro f hf hfs
    have hW := re_W_nonneg_of_zetaWindowPositive hWin hf hfs
    have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
    have hrefl := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
    exact ⟨hW, by linarith⟩
  refine ⟨hWin, hHodge, hAll, fun hR0 => ?_⟩
  have hμ : 0 ≤ ccmRestrictedWeilGroundEnergy ⟨R, hR0⟩ :=
    ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive ⟨R, hR0⟩ hWin
  refine ⟨hμ, fun hRH => ?_⟩
  have hmem : R ∈ groundEnergyNonnegApertures := ⟨hR0, hμ⟩
  exact le_csSup (bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis hRH) hmem

/-- **Unconditional Finite-Scale Grid-Tent Positivity on the Difference Lag Family Through the
First Prime (`v / 2 + w ≤ 353 / 1000`).**
For `0 < w`, `0 ≤ v`, and `v / 2 + w ≤ 353 / 1000` (reaching lags `v ≤ 706 / 1000 - 2w > log 2`
for `w < (706/1000 - log 2)/2`), the odd real part `φ(x) = (twoBump (modScaledBump w 0) v (-1) x).re`
satisfies `(1 / 1000) ∫ φ² ≤ compactFullWeilEnergy φ`, and for every scale `n : ℕ` where the finite-scale
approximation error is at most `(1 / 2000) ∫ φ²`, the single-scale grid tent pattern `P_n` has
`compactFullWeilEnergy P_n ≥ (1 / 2000) ∫ ‖twoBump (modScaledBump w 0) v (-1)‖²`. -/
theorem zeta_odd_gridTentPattern_pos_through_first_prime
    {w v Mg Kg L : ℝ} (hw : 0 < w) (hv : 0 ≤ v) (hvw : v / 2 + w ≤ 353 / 1000)
    (hMg : ∀ x, |(twoBump (modScaledBump w 0) v (-1) x).re| ≤ Mg)
    (hKg : ∀ x y, |(twoBump (modScaledBump w 0) v (-1) x).re -
      (twoBump (modScaledBump w 0) v (-1) y).re| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * (twoBump (modScaledBump w 0) v (-1) x).re -
      Real.exp (-(3 * y / 2)) * (twoBump (modScaledBump w 0) v (-1) y).re| ≤ L * |x - y|)
    (n : ℕ)
    (hn : gridTentApproximationConstant (353 / 1000) Mg Kg L * sourceFactorialWidth (n + 1) ≤
      (1 / 2000) * ∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2) :
    let φ : ℝ → ℝ := fun x => (twoBump (modScaledBump w 0) v (-1) x).re
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
    let M : ℕ := ⌈2 * (353 / 1000 + 1) / sourceFactorialWidth (n + 1)⌉₊
    let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(353 / 1000 + 1)) M
    (1 / 2000) * (∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2) ≤ compactFullWeilEnergy P ∧
    (1 / 2000) * (∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2) ≤ fullZeroForm P := by
  dsimp only
  have h1 := one_div_1000_mul_le_re_W_twoBump_of_le hw hv hvw
  have happrox := abs_zeta_W_re_twoBump_modScaledBump_zero_sub_gridTentPattern_le hw hv hvw hMg hKg hGL n
  have hlow := (abs_le.mp happrox).1
  set P : C_c(ℝ, ℝ) := gridTentPattern
    (fun x => Real.exp (-(3 * x / 2)) * (twoBump (modScaledBump w 0) v (-1) x).re)
    n (-(353 / 1000 + 1)) ⌈2 * (353 / 1000 + 1) / sourceFactorialWidth (n + 1)⌉₊
  have hP : (1 / 2000) * (∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2) ≤ compactFullWeilEnergy P := by
    linarith
  exact ⟨hP, by rwa [fullZeroForm_eq_compactFullWeilEnergy P]⟩

/-! ## Section 2: Explicit-Lag Quantitative Grid-Tent Detection Across the Visibility Hierarchy -/

/-- **General Bridge from a Negative Modulated Difference-Lag Test on `[0, V]` to Explicit-Aperture
Grid-Tent Detection at Seed Radius `R = V / 2 + w` and Ground-Energy / Contact-Aperture Bounds.** -/
theorem gridTent_detected_of_exists_lag_re_W_neg (c : ℝ) {w V : ℝ} (hw : 0 < w)
    (hex : ∃ v ∈ Icc (0 : ℝ) V,
      (zetaZeroConfig.W (twoBump (modScaledBump w c) v (-1))
        (twoBump (modScaledBump w c) v (-1))).re < 0) :
    have hR : 0 < V / 2 + w := by
      obtain ⟨v, hv, -⟩ := hex
      have : 0 ≤ V := hv.1.trans hv.2
      positivity
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
      (∀ x, V / 2 + w < |x| → G x = 0) ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D := by
  obtain ⟨v, hv, hneg⟩ := hex
  have hV0 : 0 ≤ V := hv.1.trans hv.2
  have hR0 : 0 < V / 2 + w := by positivity
  have hμv := ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_modScaledBump_neg c hw hv.1 hneg
  have hμV : ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR0⟩ < 0 :=
    lt_of_le_of_lt (ccmRestrictedWeilGroundEnergy_antitone
      (a := ⟨v / 2 + w, by have := hv.1; positivity⟩)
      (b := ⟨V / 2 + w, hR0⟩) (show v / 2 + w ≤ V / 2 + w by linarith [hv.2])) hμv
  have hcontact : zetaContactAperture ≤ V / 2 + w := by
    refine csSup_le groundEnergyNonnegApertures_nonempty fun A hA => ?_
    obtain ⟨hA0, hA_nonneg⟩ := hA
    by_contra hlt
    push Not at hlt
    have hle := ccmRestrictedWeilGroundEnergy_antitone (a := ⟨V / 2 + w, hR0⟩) (b := ⟨A, hA0⟩) hlt.le
    linarith
  set f : ℝ → ℂ := twoBump (modScaledBump w c) v (-1)
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w c) v ![1, -1]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw c)) v (-1)
  have hsupp := tsupport_twoBump_modScaledBump_subset_any c hw hv.1
  have hfR : ∀ x, V / 2 + w < |x| → f x = 0 := fun x hx => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := abs_le.mpr (hsupp hmem)
    linarith [hv.2]
  obtain ⟨φ, hφ, hφc, hφR, -, hφneg⟩ :=
    exists_real_contDiff_fullZeroForm_neg_of_zeta_W_neg hf hfc hfR hneg
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc hR0.le hφR hφneg
  refine ⟨hμV, hcontact, fun x => Real.exp (-(3 * x / 2)) * φ x, -fullZeroForm φ / 4,
    by fun_prop, hφc.mul_left, fun x hx => by simp [hφR x hx], hspec.1, hspec.2⟩

/-- **Explicit Odd-Seed Bridge for Unmodulated (`c = 0`) Difference-Lag Detection.**
When `c = 0`, the witness `twoBump (modScaledBump w 0) v (-1)` is real and odd, so the seed
`G(x) = e^{-3x/2} φ(x)` comes from an explicitly **odd** real test `φ(-x) = -φ(x)` supported in
`[-(V / 2 + w), V / 2 + w]`. -/
theorem gridTent_odd_detected_of_exists_oneParam_lag_re_W_neg {w V : ℝ} (hw : 0 < w)
    (hex : ∃ v ∈ Icc (0 : ℝ) V,
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re < 0) :
    have hR : 0 < V / 2 + w := by
      obtain ⟨v, hv, -⟩ := hex
      have : 0 ≤ V := hv.1.trans hv.2
      positivity
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (φ : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      (∀ x, φ (-x) = -φ x) ∧ (∀ x, V / 2 + w < |x| → φ x = 0) ∧ 0 < μ ∧
      let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D := by
  obtain ⟨v, hv, hneg⟩ := hex
  have hV0 : 0 ≤ V := hv.1.trans hv.2
  have hR0 : 0 < V / 2 + w := by positivity
  obtain ⟨hμV, hcontact, -⟩ := gridTent_detected_of_exists_lag_re_W_neg 0 hw ⟨v, hv, hneg⟩
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1)
  set φ : ℝ → ℝ := fun x => (f x).re
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)
  have hφ : ContDiff ℝ 2 φ := Complex.reCLM.contDiff.comp hf
  have hφc : HasCompactSupport φ := hfc.comp_left Complex.zero_re
  obtain ⟨hodd, hφv, hW_eq, -⟩ :=
    zeta_W_re_twoBump_modScaledBump_zero_eq_compactFullWeilEnergy_re hw hv.1
  have hφR : ∀ x, V / 2 + w < |x| → φ x = 0 := fun x hx => hφv x (by linarith [hv.2])
  have hφneg : fullZeroForm φ < 0 := by linarith
  have hspec := gridTentPattern_actual_zeta_detector_spec hφ hφc hR0.le hφR hφneg
  exact ⟨hμV, hcontact, φ, -fullZeroForm φ / 4, hφ, hφc, hodd, hφR, hspec.1, hspec.2⟩

/-- **Quantitative One-Parameter (`c = 0`) Near-Top Detection by Odd-Seed Grid Tent Patterns at
Explicit Lag `V ≥ oneParamLag w η z₀.re`.**
For any `1/V`-near-top zero `1/2 + z₀` of `ζ` right of the critical line with
`0 < η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖` and `V ≥ oneParamLag w η z₀.re`, the ground energy at
aperture `V / 2 + w` is strictly negative, `zetaContactAperture ≤ V / 2 + w`, and there exist an
**odd** test `φ ∈ C_c²([-(V/2 + w), V/2 + w], ℝ)` and a margin `μ > 0` such that the single-scale
grid tent pattern of `G(x) = e^{-3x/2} φ(x)` and its smoothed detector detect `z₀` across all five
form realizations. -/
theorem actual_zeta_oneParam_near_top_detected_by_gridTentPattern
    {w : ℝ} (hw : 0 < w) {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier)
    (hre₀ : 0 < z₀.re) {η : ℝ} (hη : 0 < η)
    (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    have hR : 0 < V / 2 + w := by
      have := le_oneParamLag hw η hre₀
      linarith
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (φ : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      (∀ x, φ (-x) = -φ x) ∧ (∀ x, V / 2 + w < |x| → φ x = 0) ∧ 0 < μ ∧
      let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D :=
  gridTent_odd_detected_of_exists_oneParam_lag_re_W_neg hw
    (one_param_near_top_visible_at_explicit_lag hw hz₀ hre₀ hη hηle hV htop)

/-- **One-Parameter Horizon-Law Detection by Odd-Seed Grid Tent Patterns.**
If `paperFT (scaledBump w) (-(I * z)) ≠ 0` at every zero `1/2 + z` of `ζ`, and a zero `1/2 + z₀`
right of the line with `oneParamHorizon w z₀ ≤ V` has all deeper companions `Re z > Re z₀ + 1/V`
also inside the horizon `oneParamHorizon w z ≤ V`, then an odd seed `φ ∈ C_c²([-(V/2 + w), V/2 + w], ℝ)`
detects `z₀` on `gridTentPattern` and `smoothGridTentDetector` with margin `μ > 0`. -/
theorem actual_zeta_oneParam_horizon_detected_by_gridTentPattern
    {w : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → paperFT (scaledBump w) (-(I * z)) ≠ 0)
    {V : ℝ} {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV : oneParamHorizon w z₀ ≤ V)
    (hin : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → z₀.re + 1 / V < z.re →
      oneParamHorizon w z ≤ V) :
    have hR : 0 < V / 2 + w := by
      have := le_oneParamLag hw ‖paperFT (scaledBump w) (-(I * z₀))‖ hre₀
      unfold oneParamHorizon at hV
      linarith
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (φ : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      (∀ x, φ (-x) = -φ x) ∧ (∀ x, V / 2 + w < |x| → φ x = 0) ∧ 0 < μ ∧
      let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D :=
  gridTent_odd_detected_of_exists_oneParam_lag_re_W_neg hw
    (one_param_visible_of_horizon hw hgen hz₀ hre₀ hV hin)

/-- **Contrapositive Horizon-Law Forcing from Eventual Grid-Tent Positivity at Aperture `R = V / 2 + w`.**
If `paperFT (scaledBump w) (-(I * z)) ≠ 0` at all zeros of `ζ` and single-scale grid tent patterns
at seed radius `R = V / 2 + w` are eventually nonnegative, then every zero `1/2 + z₀` right of the
critical line inside the horizon (`oneParamHorizon w z₀ ≤ V`) forces the existence of a deeper zero
`1/2 + z` strictly beyond the horizon (`z₀.re + 1 / V < z.re` and `V < oneParamHorizon w z`). -/
theorem zeta_gridTentPattern_nonneg_forces_beyond_oneParamHorizon
    {w V : ℝ} (hw : 0 < w)
    (hgen : ∀ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier → paperFT (scaledBump w) (-(I * z)) ≠ 0)
    (hpos : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, V / 2 + w < |x| → G x = 0) →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(V / 2 + w + 1))
            ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊))
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hV : oneParamHorizon w z₀ ≤ V) :
    ∃ z : ℂ, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z₀.re + 1 / V < z.re ∧
      V < oneParamHorizon w z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, φ, μ, hφ, hφc, -, hφR, hμ, hev⟩ :=
    actual_zeta_oneParam_horizon_detected_by_gridTentPattern hw hgen hz₀ hre₀ hV hcon
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * φ x
  have hG : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
  have hGc : HasCompactSupport G := hφc.mul_left
  have hGR : ∀ x, V / 2 + w < |x| → G x = 0 := fun x hx => by simp [G, hφR x hx]
  obtain ⟨n, hn_neg, hn_pos⟩ := (hev.and (hpos G hG hGc hGR)).exists
  linarith [hn_neg.1]

/-- **Quantitative Polylogarithmic Near-Top Detection by Single-Scale Grid Tent Patterns at
`V ≥ nearTopLag w z₀.im z₀.re` (`R = V / 2 + w`).**
For any `1/V`-near-top zero `1/2 + z₀` right of the critical line above `nearTopHeight w` satisfying
the polylogarithmic height envelope bound and `V ≥ nearTopLag w z₀.im z₀.re`, the ground energy at
`V / 2 + w` is strictly negative, `zetaContactAperture ≤ V / 2 + w`, and a seed `G` supported in
`[-(V/2 + w), V/2 + w]` detects `z₀` on `gridTentPattern` and `smoothGridTentDetector`. -/
theorem actual_zeta_polylog_near_top_detected_by_gridTentPattern
    {w : ℝ} (hw : 0 < w) {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier)
    (hre₀ : 0 < z₀.re) (hTw : nearTopHeight w ≤ z₀.im)
    (hγ : 1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4)
    {V : ℝ} (hV : nearTopLag w z₀.im z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    have hR : 0 < V / 2 + w := by
      obtain ⟨v, hv, -⟩ := zeta_near_top_visible_at_polylog_lag hw hz₀ hre₀ hTw hγ hV htop
      have : 0 ≤ V := hv.1.trans hv.2
      positivity
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
      (∀ x, V / 2 + w < |x| → G x = 0) ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) M
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D :=
  gridTent_detected_of_exists_lag_re_W_neg z₀.im hw
    (zeta_near_top_visible_at_polylog_lag hw hz₀ hre₀ hTw hγ hV htop)

/-- **Quantitative Doubly-Logarithmic Near-Top Detection by Single-Scale Grid Tent Patterns under
`OffLineCopiesLocallyBounded M` at `V ≥ nearTopLogLogLagOffLine M w z₀.im z₀.re`.**
Under `OffLineCopiesLocallyBounded M`, any `1/V`-near-top zero `1/2 + z₀` right of the line above
`nearTopHeightOffLine M w` is detected by `gridTentPattern` and `smoothGridTentDetector` at seed
radius `R = V / 2 + w` for any `V ≥ nearTopLogLogLagOffLine M w z₀.im z₀.re = Θ_{M,w}((1 + log log(|z₀.im| + 4)) / z₀.re)`,
removing the `(log z₀.im)²` factor from the unconditional polylogarithmic lag. -/
theorem actual_zeta_loglog_near_top_detected_by_gridTentPattern_of_offLineCopiesLocallyBounded
    {M : ℕ} (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {V : ℝ} (hV : nearTopLogLogLagOffLine M w z₀.im z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    have hR : 0 < V / 2 + w := by
      obtain ⟨v, hv, -⟩ :=
        zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded hM hw hz₀ hre₀ hTw hV htop
      have : 0 ≤ V := hv.1.trans hv.2
      positivity
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
      (∀ x, V / 2 + w < |x| → G x = 0) ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let N : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) N
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) N q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D :=
  gridTent_detected_of_exists_lag_re_W_neg z₀.im hw
    (zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded hM hw hz₀ hre₀ hTw hV htop)

/-- **Quantitative On-Line-Mass Near-Top Detection by Single-Scale Grid Tent Patterns under
`OffLineCopiesLocallyBounded M` at `V ≥ nearTopLagOffLine M w W_on z₀.re`.** -/
theorem actual_zeta_onLineMass_near_top_detected_by_gridTentPattern_of_offLineCopiesLocallyBounded
    {M : ℕ} (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {W_on : ℝ} (hWon : onLineEvenMass w z₀.im ≤ W_on)
    {V : ℝ} (hV : nearTopLagOffLine M w W_on z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    have hR : 0 < V / 2 + w := by
      obtain ⟨v, hv, -⟩ :=
        zeta_near_top_visible_at_explicit_onLineMass_lag hM hw hz₀ hre₀ hTw hWon hV htop
      have : 0 ≤ V := hv.1.trans hv.2
      positivity
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, hR⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
      (∀ x, V / 2 + w < |x| → G x = 0) ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let N : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) N
        compactFullWeilEnergy P ≤ -2 * μ ∧
        fullZeroForm P ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) N q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D :=
  gridTent_detected_of_exists_lag_re_W_neg z₀.im hw
    (zeta_near_top_visible_at_explicit_onLineMass_lag hM hw hz₀ hre₀ hTw hWon hV htop)

/-- **Quantitative Attained-Top Detection by Single-Scale Grid Tent Patterns at the Explicit `O(1/g)`
Lag of `zeta_attained_top_first_negative_lag`.**
For any zero `1/2 + z₀` of largest real part at height `z₀.im ≥ nearTopHeight w`, there is `g > 0`
(the separation of near-top zeros below `recordHeightEnvelope w z₀.im + 1`) such that at lag budget
`V = max (hidingLag w z₀) ((twinRadiusNumerator w z₀.im + uniformTwinDepth w) * max (max 1 (1 / g)) (4 / z₀.re))`
and seed radius `R = V / 2 + w`, `gridTentPattern` and `smoothGridTentDetector` detect `z₀` with
margin `μ > 0`. -/
theorem actual_zeta_attained_top_detected_by_gridTentPattern_at_explicit_lag
    {w : ℝ} (hw : 0 < w) {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier)
    (hre₀ : 0 < z₀.re) (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) :
    ∃ g > 0,
      let V : ℝ := max (hidingLag w z₀)
        ((twinRadiusNumerator w z₀.im + uniformTwinDepth w) * max (max 1 (1 / g)) (4 / z₀.re))
      zetaContactAperture ≤ V / 2 + w ∧
      ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
        (∀ x, V / 2 + w < |x| → G x = 0) ∧ 0 < μ ∧
        ∀ᶠ n : ℕ in atTop,
          let M : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
          let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) M
          compactFullWeilEnergy P ≤ -2 * μ ∧
          fullZeroForm P ≤ -2 * μ ∧
          ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
            let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) M q
            ContDiff ℝ 2 D ∧
            HasCompactSupport D ∧
            |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                (EF.weilTest D D)).re - compactFullWeilEnergy P| ≤ 1 / ((q : ℝ) + 1) ∧
            (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                (EF.weilTest D D)).re ≤ -μ ∧
            (zetaZeroConfig.W D D).re ≤ -μ ∧
            μ ≤ configurationReflectionDefect zetaZeroConfig D -
              configurationSquareMass zetaZeroConfig D := by
  obtain ⟨g, hg, hex⟩ := zeta_attained_top_first_negative_lag hw hz₀ hre₀ hTw htop
  obtain ⟨-, hcontact, hdet⟩ := gridTent_detected_of_exists_lag_re_W_neg z₀.im hw hex
  exact ⟨g, hg, hcontact, hdet⟩

/-- **Quantitative Attained-Top Detection by Single-Scale Grid Tent Patterns at the Logarithmic
`O(log(1/g))` Lag of `zeta_attained_top_visible_log`.** -/
theorem actual_zeta_attained_top_detected_by_gridTentPattern_at_log_lag
    {w : ℝ} (hw : 0 < w) {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier)
    (hre₀ : 0 < z₀.re) (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) {P : ℕ}
    (hP : 80 * Real.log (180 * recordHeightEnvelope w z₀.im) ≤ P)
    {g : ℝ} (hg : 0 < g)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ ≠ ρ' →
      |ρ.im| ≤ recordHeightEnvelope w z₀.im + 1 → |ρ'.im| ≤ recordHeightEnvelope w z₀.im + 1 →
      1 / 2 + z₀.re / 4 ≤ ρ.re → 1 / 2 + z₀.re / 4 ≤ ρ'.re → g ≤ ‖ρ - ρ'‖)
    {V κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀) (hV : 0 < V)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : Real.pi * (k + P : ℕ) ≤ V)
    (hVr : 4 * Real.pi * (k + P : ℕ) ≤ V * (z₀.re / 8))
    (hmain : ∀ p : ℕ, p ≤ P → (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) *
      (4 * κ₀ ^ 2 + 4 * Real.pi ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) * twinTightConstant w *
        Real.log (180 * (recordHeightEnvelope w z₀.im + 6)) <
      (g * κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ccmRestrictedWeilGroundEnergy ⟨V / 2 + w, by positivity⟩ < 0 ∧
    zetaContactAperture ≤ V / 2 + w ∧
    ∃ (G : ℝ → ℝ) (μ : ℝ), ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
      (∀ x, V / 2 + w < |x| → G x = 0) ∧ 0 < μ ∧
      ∀ᶠ n : ℕ in atTop,
        let M : ℕ := ⌈2 * (V / 2 + w + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P_n : C_c(ℝ, ℝ) := gridTentPattern G n (-(V / 2 + w + 1)) M
        compactFullWeilEnergy P_n ≤ -2 * μ ∧
        fullZeroForm P_n ≤ -2 * μ ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(V / 2 + w + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re - compactFullWeilEnergy P_n| ≤ 1 / ((q : ℝ) + 1) ∧
          (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
              (EF.weilTest D D)).re ≤ -μ ∧
          (zetaZeroConfig.W D D).re ≤ -μ ∧
          μ ≤ configurationReflectionDefect zetaZeroConfig D -
            configurationSquareMass zetaZeroConfig D :=
  gridTent_detected_of_exists_lag_re_W_neg z₀.im hw
    (zeta_attained_top_visible_log hw hz₀ hre₀ hTw htop hP hg hsep hk hκ₀ hV hV2 hκV hVk hVr hmain)

/-! ## Section 3: Quantitative Excluded-Depth Laws, Horizon Heights, and Two-Way Visibility/Height-Reduction Duality for `gridTentPattern` at Fixed Aperture `R` -/

/-- **Unconditional Excluded-Depth Law `|ρ.re - 1/2| < 1/R` Below `zetaClusterHorizonHeight A₀ R`
from Eventual Grid-Tent Positivity at Aperture `R ≥ e⁶`.**
There exists an unconditional Riemann–von Mangoldt constant `A₀ ≥ 1` such that for every aperture
`R ≥ e⁶` where `gridTentPattern` is eventually nonnegative on seeds supported in `[-R, R]`, every
nontrivial zero `ρ ∈ zetaZeroConfig.carrier` with
`2 ≤ |ρ.im| ≤ zetaClusterHorizonHeight A₀ R = exp(R / (10⁵ A₀ (log R)²)) - 306` satisfies
`|ρ.re - 1/2| < 1/R = 2/log X` (`X = e^{2R}`). -/
theorem zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ R : ℝ, Real.exp 6 ≤ R →
      (∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
        ∀ᶠ n : ℕ in atTop,
          0 ≤ compactFullWeilEnergy
            (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₀ R →
        |ρ.re - 1 / 2| < 1 / R := by
  obtain ⟨A₀, hA₀, hexcl⟩ := zeta_abs_re_sub_half_lt_of_hodgeIndex
  refine ⟨A₀, hA₀, fun R hR6 hpos => ?_⟩
  have hR0 : 0 ≤ R := (Real.exp_pos 6).le.trans hR6
  have hHodge :=
    (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius hR0 hpos).2.1
  exact hexcl R hR6 hHodge

/-- **Cluster-Multiplicity-Refined Excluded-Depth Law `|ρ₀.re - 1/2| < 1/R` Below
`clusterHorizonHeight A₀ k R` from Eventual Grid-Tent Positivity at Aperture `R ≥ e⁶`.**
There exists `A₀ ≥ 1` such that for every aperture `R ≥ e⁶` where `gridTentPattern` is eventually
nonnegative on seeds supported in `[-R, R]`, every `ρ₀ ∈ zetaZeroConfig.carrier` with local count
`zetaZeroConfig.Nd (ρ₀.im - 101) (ρ₀.im + 101) ≤ k` and height
`2 ≤ |ρ₀.im| ≤ clusterHorizonHeight A₀ k R = exp(R/100 - (k + 1)(log R)²)/A₀ - 4` satisfies
`|ρ₀.re - 1/2| < 1/R`. -/
theorem zeta_excluded_depth_below_localCount_clusterHorizon_of_gridTentPattern_nonneg :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ R : ℝ, Real.exp 6 ≤ R →
      (∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
        ∀ᶠ n : ℕ in atTop,
          0 ≤ compactFullWeilEnergy
            (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) →
      ∀ {k : ℕ} {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 2 ≤ |ρ₀.im| →
        zetaZeroConfig.Nd (ρ₀.im - 101) (ρ₀.im + 101) ≤ k →
        |ρ₀.im| ≤ clusterHorizonHeight A₀ k R →
        |ρ₀.re - 1 / 2| < 1 / R := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun R hR6 hpos k ρ₀ hρ₀ hγ2 hk hγT => ?_⟩
  have hR0 : 0 ≤ R := (Real.exp_pos 6).le.trans hR6
  have hHodge :=
    (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius hR0 hpos).2.1
  exact abs_re_sub_half_lt_of_hodgeIndex_of_local_count zetaZeroConfig hA₀ hloc hR6 hHodge
    hρ₀ hγ2 hk hγT

/-- **Quantitative One-Parameter Near-Top Excluded-Depth Law `z₀.re < oneParamExcludedDepth w η (2(R - w))`
from Eventual Grid-Tent Positivity at Aperture `R > w + oneParamDrift w η / 2`.** -/
theorem zeta_oneParam_excluded_depth_of_gridTentPattern_nonneg
    {w R η : ℝ} (hw : 0 < w) (hη : 0 < η) (hVd : oneParamDrift w η < 2 * (R - w))
    (hpos : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊))
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / (2 * (R - w))) :
    z₀.re < oneParamExcludedDepth w η (2 * (R - w)) := by
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hdrift_ge : w ≤ oneParamDrift w η := by
    unfold oneParamDrift
    have : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / oneParamScale w η :=
      div_nonneg (mul_nonneg (by positivity) hJ0) (Real.sqrt_nonneg _)
    linarith
  have hR0 : 0 ≤ R := by linarith
  have hAll :=
    (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius hR0 hpos).2.2.1
  refine near_top_depth_lt_of_oneParam_nonneg hw hz₀ hre₀ hη hηle hVd htop fun v hv => ?_
  refine (hAll (twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]) ?_).1
  refine (tsupport_twoBump_modScaledBump_subset_any 0 hw hv.1).trans (Icc_subset_Icc ?_ ?_) <;>
    linarith [hv.2]

/-- **Quantitative Polylogarithmic Near-Top Excluded-Depth Law
`z₀.re < nearTopExcludedDepth w z₀.im (2(R - w))` from Eventual Grid-Tent Positivity at Aperture `R`.** -/
theorem zeta_polylog_near_top_excluded_depth_of_gridTentPattern_nonneg
    {w R : ℝ} (hw : 0 < w) {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier)
    (hre₀ : 0 < z₀.re) (hTw : nearTopHeight w ≤ z₀.im)
    (hγ : 1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4)
    (hVd : nearTopDrift w z₀.im < 2 * (R - w))
    (hpos : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊))
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / (2 * (R - w))) :
    z₀.re < nearTopExcludedDepth w z₀.im (2 * (R - w)) := by
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hdrift_ge : w ≤ nearTopDrift w z₀.im := by
    unfold nearTopDrift
    have : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScale w z₀.im :=
      div_nonneg (mul_nonneg (by positivity) hJ0) (Real.sqrt_nonneg _)
    linarith
  have hR0 : 0 ≤ R := by linarith
  have hAll :=
    (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius hR0 hpos).2.2.1
  refine near_top_depth_lt_of_modulated_nonneg hw hz₀ hre₀ hTw hγ hVd htop fun v hv => ?_
  refine (hAll (twoBump (modScaledBump w z₀.im) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w z₀.im) v ![1, -1]) ?_).1
  refine (tsupport_twoBump_modScaledBump_subset_any z₀.im hw hv.1).trans (Icc_subset_Icc ?_ ?_) <;>
    linarith [hv.2]

/-- **Quantitative Doubly-Logarithmic Near-Top Excluded-Depth Laws under
`OffLineCopiesLocallyBounded M` from Eventual Grid-Tent Positivity at Aperture `R`.**
Under `OffLineCopiesLocallyBounded M`, if single-scale grid tent patterns are eventually nonnegative
on seeds supported in `[-R, R]` (`2(R - w) > nearTopCoherenceDriftOffLine M w`), then every
`1/(2(R - w))`-near-top zero `1/2 + z₀` of `ζ` with `nearTopHeightOffLine M w ≤ z₀.im` satisfies both:
1. `z₀.re < nearTopExcludedDepthOffLine M w (onLineEvenMass w z₀.im) (2 * (R - w))`, and
2. `z₀.re < nearTopLogLogExcludedDepthOffLine M w z₀.im (2 * (R - w)) = O_{M,w}((1 + log log(|z₀.im| + 4)) / (2(R - w) - Drift))`. -/
theorem zeta_loglog_near_top_excluded_depth_of_gridTentPattern_nonneg_of_offLineCopiesLocallyBounded
    {M : ℕ} (hM : OffLineCopiesLocallyBounded M) {w R : ℝ} (hw : 0 < w)
    (hVd : nearTopCoherenceDriftOffLine M w < 2 * (R - w))
    (hpos : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊))
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / (2 * (R - w))) :
    z₀.re < nearTopExcludedDepthOffLine M w (onLineEvenMass w z₀.im) (2 * (R - w)) ∧
    z₀.re < nearTopLogLogExcludedDepthOffLine M w z₀.im (2 * (R - w)) := by
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hdrift_ge : w ≤ nearTopCoherenceDriftOffLine M w := by
    unfold nearTopCoherenceDriftOffLine
    have : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScaleOffLine M w :=
      div_nonneg (mul_nonneg (by positivity) hJ0) (Real.sqrt_nonneg _)
    linarith
  have hR0 : 0 ≤ R := by linarith
  have hAll :=
    (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius hR0 hpos).2.2.1
  have hlag_pos : ∀ v ∈ Icc (0 : ℝ) (2 * (R - w)),
      0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
        (twoBump (modScaledBump w z₀.im) v (-1))).re := fun v hv => by
    refine (hAll (twoBump (modScaledBump w z₀.im) v (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w z₀.im) v ![1, -1]) ?_).1
    refine (tsupport_twoBump_modScaledBump_subset_any z₀.im hw hv.1).trans (Icc_subset_Icc ?_ ?_) <;>
      linarith [hv.2]
  exact ⟨re_lt_nearTopExcludedDepthOffLine_of_pos_on_Icc hM hw hz₀ hTw hVd htop hlag_pos,
    re_lt_nearTopLogLogExcludedDepthOffLine_of_pos_on_Icc hM hw hz₀ hTw hVd htop hlag_pos⟩

/-- **Quantitative Equal-Depth `k`-Pair Cluster Excluded-Depth Law
`δ < equalDepthClusterExcludedDepth zetaZeroConfig b δ γ c ℓ w R` from Eventual Grid-Tent Positivity.** -/
theorem zeta_equalDepthCluster_excluded_depth_of_gridTentPattern_nonneg
    {k : ℕ} (hk : 0 < k) (γ : Fin k → ℝ) (hγ : Function.Injective γ) {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ j, heightPoint δ (γ j) ∈ zetaZeroConfig.carrier)
    (hm : ∀ j, heightPoint (-δ) (γ j) ∈ zetaZeroConfig.carrier)
    (hmp : ∀ j, zetaZeroConfig.mult (heightPoint δ (γ j)) = 1)
    (hmm : ∀ j, zetaZeroConfig.mult (heightPoint (-δ) (γ j)) = 1)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 ∨
      ∃ j, ρ = heightPoint δ (γ j) ∨ ρ = heightPoint (-δ) (γ j))
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hw : 0 ≤ w) (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hsep : Function.Injective fun j => cexp (I * γ j * ℓ))
    (hQ : ∀ j, pairWeight b δ (γ j) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, (k + 2) * ℓ / 2 + w < R →
      (∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
        ∀ᶠ n : ℕ in atTop,
          0 ≤ compactFullWeilEnergy
            (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) →
      δ < equalDepthClusterExcludedDepth zetaZeroConfig b δ γ c ℓ w R := by
  obtain ⟨c, hc, hvis⟩ := equalDepthCluster_visible_of_excludedDepth_le zetaZeroConfig
    temperedConfig_zetaZeroConfig hk γ hγ hδ hp hm hmp hmm hon hb hbs hℓ hsep hQ
  refine ⟨c, hc, fun R hR hpos => ?_⟩
  by_contra hle
  push Not at hle
  obtain ⟨f, hf, hfs, hneg⟩ := hvis R hR hle
  have hR0 : 0 ≤ R := by
    have : 0 ≤ (k + 2 : ℝ) * ℓ / 2 := by positivity
    linarith
  have hAll :=
    (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius hR0 hpos).2.2.1
  have hnonneg := (hAll f hf hfs).1
  linarith

/-- **Two-Way Visibility and Height-Reduction Duality for `gridTentPattern` at Arithmetic Length
`X = e^{2R}`.**
There exist unconditional Riemann–von Mangoldt constants `A₀, A₁ ≥ 1` such that for every aperture
`R > 0`:
1. **(Archimedean horizon height scale):** `log(zetaHorizonHeight A₀ R) ≤ 7000 e^R + log A₀ + 160`.
2. **(Zero-to-aperture finite-scale `gridTentPattern` floor reduction):** If every zero of `ζ` up to
   height `T ≥ zetaHorizonHeight A₀ R` has depth `|ρ.re - 1/2| ≤ δ` (`0 ≤ δ ≤ 1/2`) and unit-window
   off-line multiplicity at most `D`, then for every polar-constrained real seed `F ∈ C_c²([-R, R], ℝ)`
   (`evenPoleMoment F = 0` and `oddPoleMoment F = 0`) with envelope `(Mg, Kg, L)` and every finite
   scale `n : ℕ`, the single-scale grid tent pattern `P_n` satisfies
   `compactFullWeilEnergy P_n ≥ -((7000(2R + 3)D e^{2δ(R + 2)} + 2) ∫ F²) - gridTentApproximationConstant R Mg Kg L * d_{n+1}`.
3. **(Aperture-to-zero depth exclusion):** If `R ≥ e⁶` and `gridTentPattern` is eventually nonnegative
   on seeds supported in `[-R, R]`, then every zero `ρ ∈ zetaZeroConfig.carrier` with
   `2 ≤ |ρ.im| ≤ zetaClusterHorizonHeight A₁ R` has depth `|ρ.re - 1/2| < 1/R`. -/
theorem zeta_gridTentPattern_visibility_and_height_reduction_duality :
    ∃ A₀ A₁ : ℝ, 1 ≤ A₀ ∧ 1 ≤ A₁ ∧ ∀ R : ℝ, 0 < R →
      Real.log (zetaHorizonHeight A₀ R) ≤ 7000 * Real.exp R + Real.log A₀ + 160 ∧
      (∀ δ D T : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → zetaHorizonHeight A₀ R ≤ T →
        (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T → |ρ.re - 1 / 2| ≤ δ) →
        OffLineDensityBoundBelow zetaZeroConfig T D →
        ∀ (F : ℝ → ℝ) (Mg Kg L : ℝ), ContDiff ℝ 2 F → HasCompactSupport F →
          tsupport F ⊆ Icc (-R) R → evenPoleMoment F = 0 → oddPoleMoment F = 0 →
          (∀ x, |F x| ≤ Mg) → (∀ x y, |F x - F y| ≤ Kg * |x - y|) →
          (∀ x y, |Real.exp (-(3 * x / 2)) * F x - Real.exp (-(3 * y / 2)) * F y| ≤ L * |x - y|) →
          ∀ n : ℕ,
            let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
            let P : C_c(ℝ, ℝ) :=
              gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊;
            -((7000 * (2 * R + 3) * D * Real.exp (2 * δ * (R + 2)) + 2) * ∫ u, F u ^ 2) -
                gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) ≤
              compactFullWeilEnergy P) ∧
      (Real.exp 6 ≤ R →
        (∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
          ∀ᶠ n : ℕ in atTop,
            0 ≤ compactFullWeilEnergy
              (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊)) →
        ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₁ R →
          |ρ.re - 1 / 2| < 1 / R) := by
  obtain ⟨A₀, A₁, hA₀, hA₁, htrade⟩ := zeta_visibility_and_height_reduction_tradeoff
  refine ⟨A₀, A₁, hA₀, hA₁, fun R hR => ?_⟩
  obtain ⟨hlog, hred, hexcl⟩ := htrade R hR
  refine ⟨hlog, ?_, ?_⟩
  · intro δ D T hδ0 hδ2 hHT hδ hD F Mg Kg L hF hFc hFs hev hodd hMg hKg hGL n
    dsimp only
    set f : ℝ → ℂ := fun x => (F x : ℂ)
    have hf : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp hF
    have hsupp_eq : Function.support f = Function.support F := by ext x; simp [f]
    have hfs : tsupport f ⊆ Icc (-R) R := by simpa only [tsupport, hsupp_eq] using hFs
    have hp1 : paperFT f (I / 2) = 0 := by
      rw [paperFT_ofReal_I_half_eq_moments hF.continuous hFc, hev, hodd]
      simp
    have hp2 : paperFT f (-(I / 2)) = 0 := by
      have hneg : -(I / 2) = -I / 2 := by ring
      rw [hneg, paperFT_ofReal_neg_I_half_eq_moments hF.continuous hFc, hev, hodd]
      simp
    have hW := hred δ D T hδ0 hδ2 hHT hδ hD f hf hfs hp1 hp2
    have hint : (∫ u, ‖f u‖ ^ 2) = ∫ u, F u ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp [f, Complex.norm_real, sq_abs]
    set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
    have hW_eq : (zetaZeroConfig.W f f).re = compactFullWeilEnergy Fc :=
      (fullZeroForm_eq_zeta_W_re hF hFc).symm.trans (fullZeroForm_eq_compactFullWeilEnergy Fc)
    have hFR : ∀ x, R < |x| → Fc x = 0 := fun x hx => by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := abs_le.mpr (hFs hmem)
      linarith
    set P : C_c(ℝ, ℝ) :=
      gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x) n (-(R + 1))
        ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    have happrox : |compactFullWeilEnergy P - compactFullWeilEnergy Fc| ≤
        gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) :=
      abs_compactFullWeilEnergy_gridTentPattern_sub_le Fc hR.le hFR hMg hKg hGL n
    have hlow := (abs_le.mp happrox).1
    rw [hint, hW_eq] at hW
    linarith
  · intro hR6 hpos
    have hHodge :=
      (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius hR.le hpos).2.1
    exact hexcl hR6 hHodge

end GaloisForLFunctions.ArithmeticPositivityTheory
end
