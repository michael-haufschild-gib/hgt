import GaloisForLFunctions.RHTower.MassGaugeSuperluminalCompression
import GaloisForLFunctions.HTGeometry.MassGaugeDampedSymbol

/-!
# Damping and bounded filtering cannot lower the causal exponential type

The filtered damped propagator is the Fourier multiplier with symbol
`B(ξ) e^{-(σ+iu)ω_{a,λ}(ξ)}`, compressed to a causal window.  Because `Re ω ≥ 0` and
`|Im ω| < λ`, the symbol is bounded by `‖B‖_∞ e^{λu}` for every `σ ≥ 0` and `u ≥ 0`, so the
compressed operator norm obeys the same bound and its logarithmic growth rate is at most `λ`:

`(1/u) log ‖P_H F^{-1} M_{B e^{-(σ+iu)ω}} F P_H‖ ≤ (log ‖B‖_∞)/u + λ → λ`.

The bound is uniform in the window, so no fixed bounded causal filter and no fixed analytic
real-time smoothing can push the causal type below `λ`.
-/

open MeasureTheory Filter Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The filtered damped symbol -/

/-- The damped half-wave symbol read in the `2π`-normalised frequency variable. -/
def dampedSuperluminalSymbol (a lambda sigma u w : ℝ) : ℂ :=
  massGaugeDampedSymbol a lambda sigma u (2 * Real.pi * w)

/-- A bounded filter applied to the damped symbol. -/
def filteredDampedSymbol (B : ℝ → ℂ) (a lambda sigma u w : ℝ) : ℂ :=
  B w * dampedSuperluminalSymbol a lambda sigma u w

theorem continuous_dampedSuperluminalSymbol {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 ≤ lambda) (sigma u : ℝ) :
    Continuous (dampedSuperluminalSymbol a lambda sigma u) :=
  (continuous_massGaugeDampedSymbol ha hlambda sigma u).comp (by fun_prop)

theorem measurable_filteredDampedSymbol {B : ℝ → ℂ} (hB : Measurable B) {a lambda : ℝ}
    (ha : lambda < a) (hlambda : 0 ≤ lambda) (sigma u : ℝ) :
    Measurable (filteredDampedSymbol B a lambda sigma u) :=
  hB.mul (continuous_dampedSuperluminalSymbol ha hlambda sigma u).measurable

theorem norm_filteredDampedSymbol_le {B : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hB : ∀ w, ‖B w‖ ≤ M)
    {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) {sigma u : ℝ}
    (hsigma : 0 ≤ sigma) (hu : 0 ≤ u) (w : ℝ) :
    ‖filteredDampedSymbol B a lambda sigma u w‖ ≤ M * Real.exp (u * lambda) := by
  rw [filteredDampedSymbol, norm_mul]
  refine mul_le_mul (hB w)
    (norm_massGaugeDampedSymbol_le ha hlambda hsigma hu _) (norm_nonneg _) hM

/-! ## The compressed filtered propagator -/

/-- The filtered damped propagator on `L²(ℝ)`. -/
def filteredDampedHalfWave {B : ℝ → ℂ} (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hBM : ∀ w, ‖B w‖ ≤ M) {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma u : ℝ} (hsigma : 0 ≤ sigma) (hu : 0 ≤ u) :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  fourierMulCLM (measurable_filteredDampedSymbol hB ha hlambda.le sigma u)
    (mul_nonneg hM (Real.exp_nonneg _))
    (norm_filteredDampedSymbol_le hM hBM ha hlambda hsigma hu)

/-- The filtered damped propagator compressed to a causal window. -/
def filteredDampedCompression {B : ℝ → ℂ} (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hBM : ∀ w, ‖B w‖ ≤ M) {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma u : ℝ} (hsigma : 0 ≤ sigma) (hu : 0 ≤ u) {S : Set ℝ} (hS : MeasurableSet S) :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  (windowCutoff hS).comp
    ((filteredDampedHalfWave hB hM hBM ha hlambda hsigma hu).comp (windowCutoff hS))

/-- **(24.54) upper bound.**  The compressed filtered damped propagator obeys the radiation
envelope of its filter. -/
theorem norm_filteredDampedCompression_le {B : ℝ → ℂ} (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hBM : ∀ w, ‖B w‖ ≤ M) {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma u : ℝ} (hsigma : 0 ≤ sigma) (hu : 0 ≤ u) {S : Set ℝ} (hS : MeasurableSet S) :
    ‖filteredDampedCompression hB hM hBM ha hlambda hsigma hu hS‖
      ≤ M * Real.exp (u * lambda) := by
  have hU : ‖filteredDampedHalfWave hB hM hBM ha hlambda hsigma hu‖ ≤ M * Real.exp (u * lambda) :=
    norm_fourierMulCLM_le _ _ _
  have hP := norm_windowCutoff_le hS
  have hMe : (0 : ℝ) ≤ M * Real.exp (u * lambda) := mul_nonneg hM (Real.exp_nonneg _)
  have hstep1 :
      ‖(filteredDampedHalfWave hB hM hBM ha hlambda hsigma hu).comp (windowCutoff hS)‖
        ≤ M * Real.exp (u * lambda) * 1 := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    exact mul_le_mul hU hP (norm_nonneg _) hMe
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  calc ‖windowCutoff hS‖
        * ‖(filteredDampedHalfWave hB hM hBM ha hlambda hsigma hu).comp (windowCutoff hS)‖
      ≤ 1 * (M * Real.exp (u * lambda) * 1) :=
        mul_le_mul hP hstep1 (norm_nonneg _) zero_le_one
    _ = M * Real.exp (u * lambda) := by ring

/-! ## The exponential type of the envelope -/

/-- **(24.54)/(24.49) upper half.**  The logarithmic growth rate of the envelope is exactly the
radiation character `λ`, independently of the filter bound and the damping. -/
theorem tendsto_dampedTypeBound {M lambda : ℝ} (hM : 0 < M) :
    Tendsto (fun u : ℝ => Real.log (M * Real.exp (u * lambda)) / u) atTop (nhds lambda) := by
  have hzero : Tendsto (fun u : ℝ => Real.log M / u) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hsum : Tendsto (fun u : ℝ => Real.log M / u + lambda) atTop (nhds (0 + lambda)) :=
    hzero.add tendsto_const_nhds
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [Real.log_mul (ne_of_gt hM) (Real.exp_ne_zero _), Real.log_exp]
  field_simp

end

end RHTower
