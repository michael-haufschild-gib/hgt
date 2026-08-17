import GaloisForLFunctions.HTGeometry.MassGaugeDampedBandRatio
import GaloisForLFunctions.RHTower.GaussianCausalPacket
import GaloisForLFunctions.RHTower.DampedFilteredCausalType

/-!
# The damped propagator compressed to a causal window

The analytically damped massive half-wave `S_{σ,u} = 𝓕⁻¹ M_{e^{-(σ+iu)ω}} 𝓕` differs from the
undamped propagator by a contraction, so its compression to any window still obeys the radiation
envelope `e^{λu}`.  This is the upper half of the exact type law: the damping cannot raise the
exponential type, and — the content of the lower half — it cannot lower it either.
-/

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

open scoped FourierTransform

namespace RHTower

open RHTower.MellinL2

noncomputable section

theorem measurable_dampedSuperluminalSymbol {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 ≤ lambda) (sigma u : ℝ) :
    Measurable (dampedSuperluminalSymbol a lambda sigma u) :=
  (continuous_dampedSuperluminalSymbol ha hlambda sigma u).measurable

theorem norm_dampedSuperluminalSymbol_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma u : ℝ} (hsigma : 0 ≤ sigma) (hu : 0 ≤ u) (w : ℝ) :
    ‖dampedSuperluminalSymbol a lambda sigma u w‖ ≤ Real.exp (u * lambda) :=
  norm_massGaugeDampedSymbol_le ha hlambda hsigma hu _

/-- The radiation envelope, valid at every real time. -/
theorem norm_dampedSuperluminalSymbol_abs_le {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) {sigma : ℝ} (hsigma : 0 ≤ sigma) (u w : ℝ) :
    ‖dampedSuperluminalSymbol a lambda sigma u w‖ ≤ Real.exp (|u| * lambda) := by
  rw [dampedSuperluminalSymbol, norm_massGaugeDampedSymbol]
  refine Real.exp_le_exp.2 ?_
  have hre : 0 ≤ (massGaugeDispersion a lambda (2 * Real.pi * w)).re := sqrt_re_nonneg _
  have him : |(massGaugeDispersion a lambda (2 * Real.pi * w)).im| < lambda :=
    abs_massGaugeDispersion_im_lt ha hlambda _
  have h1 : u * (massGaugeDispersion a lambda (2 * Real.pi * w)).im ≤ |u| * lambda := by
    calc u * (massGaugeDispersion a lambda (2 * Real.pi * w)).im
        ≤ |u * (massGaugeDispersion a lambda (2 * Real.pi * w)).im| := le_abs_self _
      _ = |u| * |(massGaugeDispersion a lambda (2 * Real.pi * w)).im| := abs_mul _ _
      _ ≤ |u| * lambda := mul_le_mul_of_nonneg_left him.le (abs_nonneg u)
  nlinarith [hre, hsigma, h1]

/-- The analytically damped massive half-wave propagator on `L²`. -/
def dampedHalfWave {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (u : ℝ) :
    Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 →L[ℂ]
      Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 :=
  fourierMulCLM (measurable_dampedSuperluminalSymbol ha hlambda.le sigma u) (Real.exp_nonneg _)
    (norm_dampedSuperluminalSymbol_abs_le ha hlambda hsigma u)

theorem norm_dampedHalfWave_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) :
    ‖dampedHalfWave ha hlambda hsigma u‖ ≤ Real.exp (|u| * lambda) :=
  norm_fourierMulCLM_le _ _ _

/-- The damped propagator compressed to the causal window `(0, H)`. -/
def dampedCompression {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (u H : ℝ) :
    Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 →L[ℂ]
      Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 :=
  (windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H))).comp
    ((dampedHalfWave ha hlambda hsigma u).comp
      (windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H))))

/-- **(24.49) upper bound.**  Damping cannot raise the causal type. -/
theorem norm_dampedCompression_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u H : ℝ) :
    ‖dampedCompression ha hlambda hsigma u H‖ ≤ Real.exp (|u| * lambda) := by
  have hP : ‖windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H))‖ ≤ 1 :=
    norm_windowCutoff_le _
  have hS : ‖dampedHalfWave ha hlambda hsigma u‖ ≤ Real.exp (|u| * lambda) :=
    norm_dampedHalfWave_le ha hlambda hsigma u
  have hstep1 : ‖(dampedHalfWave ha hlambda hsigma u).comp
      (windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H)))‖
      ≤ Real.exp (|u| * lambda) * 1 := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    exact mul_le_mul hS hP (norm_nonneg _) (Real.exp_nonneg _)
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  calc ‖windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H))‖
        * ‖(dampedHalfWave ha hlambda hsigma u).comp
          (windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H)))‖
      ≤ 1 * (Real.exp (|u| * lambda) * 1) :=
        mul_le_mul hP hstep1 (norm_nonneg _) zero_le_one
    _ = Real.exp (|u| * lambda) := by ring

/-- **(24.49) upper half of the type law.**  The normalised logarithm of the compressed damped
propagator never exceeds `λ`. -/
theorem log_norm_dampedCompression_div_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {u : ℝ} (hu : 0 < u) (H : ℝ) :
    Real.log ‖dampedCompression ha hlambda hsigma u H‖ / u ≤ lambda := by
  have hle := norm_dampedCompression_le ha hlambda hsigma u H
  rw [abs_of_pos hu] at hle
  have hlog : Real.log ‖dampedCompression ha hlambda hsigma u H‖ ≤ u * lambda := by
    rcases eq_or_lt_of_le (norm_nonneg (dampedCompression ha hlambda hsigma u H)) with h | h
    · rw [← h, Real.log_zero]
      positivity
    · have := Real.log_le_log h hle
      rwa [Real.log_exp] at this
  rw [div_le_iff₀ hu]
  linarith [hlog]

end

end RHTower
