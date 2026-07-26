import GaloisForLFunctions.RHTower.DeningerArithmeticJetFrobenius
import GaloisForLFunctions.RHTower.XiConvergenceExponent
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Deninger's arithmetic trace distributions on positive time

Deninger's Lefschetz formula lives on the open time axis `ℝ₊ = (0, ∞)`.  This file constructs
that distribution space and the source-defined cohomological trace distributions.

The middle trace cannot be defined by the pointwise series `Σρ exp (t ρ)`: it is not absolutely
convergent.  Instead, reciprocal-square convergence of the actual Xi divisor makes

`Σρ exp (t ρ) / ρ²`

locally normally convergent.  Its second distributional derivative is the canonical
multiplicity-exact `H¹` trace.  This is Deninger's distributional trace construction, not a
divisor Hilbert model and not a CCM comparison.

The endpoint traces and archimedean local term are regular distributions on the same open set.
The prime-power Dirac comb and the equality of the two sides are developed after these intrinsic
cohomological objects.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace RHTower

noncomputable section

/-- Deninger's open positive-time domain. -/
def deningerTimeDomain : Opens ℝ :=
  ⟨Ioi 0, isOpen_Ioi⟩

/-- Smooth compactly supported test functions on positive time. -/
abbrev DeningerTimeTestFunction :=
  𝓓(deningerTimeDomain, ℝ)

/-- Complex-valued distributions on positive time. -/
abbrev DeningerTimeDistribution :=
  𝓓'(deningerTimeDomain, ℂ)

/-- Real scalar multiplication on a complex value, bundled as a continuous real-bilinear map. -/
noncomputable def deningerRealComplexMul :
    ℝ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ (E := ℂ) ℂ).comp Complex.ofRealCLM

@[simp]
theorem deningerRealComplexMul_apply (r : ℝ) (z : ℂ) :
    deningerRealComplexMul r z = (r : ℂ) * z := by
  rfl

/-- Regular distribution associated with a complex locally integrable time function. -/
noncomputable def deningerRegularTimeDistribution (f : ℝ → ℂ) :
    DeningerTimeDistribution :=
  TestFunction.integralAgainstBilinCLM
    deningerRealComplexMul volume f

theorem deningerRegularTimeDistribution_apply
    {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi 0) volume)
    (φ : DeningerTimeTestFunction) :
    deningerRegularTimeDistribution f φ =
      ∫ t : ℝ, (φ t : ℂ) * f t := by
  have hf' :
      LocallyIntegrableOn f
        (↑deningerTimeDomain : Set ℝ) volume := by
    simpa [deningerTimeDomain] using hf
  have h :=
    TestFunction.integralAgainstBilinCLM_eq_integral
      (B := deningerRealComplexMul) (μ := volume)
      (φ := f) hf' (f := φ)
  change
    (TestFunction.integralAgainstBilinCLM
      deningerRealComplexMul volume f) φ =
        ∫ t : ℝ, (φ t : ℂ) * f t
  simpa [deningerRealComplexMul] using h

/-- Raw eigenvalue of source Frobenius on one multiplicity copy. -/
def deningerRawThetaEigen (q : XiZeroCopy) : ℂ :=
  (q.1 : ℂ)

/-- Every source Frobenius eigenvalue lies in the open critical strip, unconditionally. -/
theorem deningerRawThetaEigen_re_mem_open_unit (q : XiZeroCopy) :
    0 < (deningerRawThetaEigen q).re ∧
      (deningerRawThetaEigen q).re < 1 := by
  exact xi_zero_re_mem_open_unit
    (xi_eq_zero_of_mem_divisor_support q.1)

/-- Raw source Frobenius eigenvalues are nonzero. -/
theorem deningerRawThetaEigen_ne_zero (q : XiZeroCopy) :
    deningerRawThetaEigen q ≠ 0 := by
  intro h
  have hre : (deningerRawThetaEigen q).re = 0 := by
    rw [h]
    rfl
  exact (deningerRawThetaEigen_re_mem_open_unit q).1.ne' hre

/--
Multiplicity-exact reciprocal-square convergence for raw source Frobenius eigenvalues.

The existing convergence theorem is indexed by Xi-divisor support and weighted by analytic
multiplicity.  Expanding every positive integer multiplicity into its finite fiber gives this
copy-indexed statement.
-/
theorem deningerRawThetaEigen_inv_sq_summable :
    Summable
      (fun q : XiZeroCopy =>
        1 / ‖deningerRawThetaEigen q‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  constructor
  · intro rho
    exact (hasSum_fintype _).summable
  · refine xi_zero_multiplicity_inv_sq_summable.congr (fun rho => ?_)
    rw [tsum_fintype]
    simp only [deningerRawThetaEigen, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnonneg :
        0 ≤ (MeromorphicOn.divisor xi Set.univ) (rho : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support rho)
    have hcast :
        (((MeromorphicOn.divisor xi Set.univ)
            (rho : ℂ)).toNat : ℝ) =
          ((MeromorphicOn.divisor xi Set.univ)
            (rho : ℂ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast, div_eq_mul_inv]
    ring

/-- One reciprocal-square regularized source-flow trace term. -/
def deningerRegularizedSpectralFlowTerm
    (q : XiZeroCopy) (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * deningerRawThetaEigen q) /
    deningerRawThetaEigen q ^ 2

/-- Reciprocal-square regularized trace of the source `H¹` flow. -/
def deningerRegularizedSpectralFlow (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, deningerRegularizedSpectralFlowTerm q t

theorem norm_deningerRegularizedSpectralFlowTerm
    (q : XiZeroCopy) (t : ℝ) :
    ‖deningerRegularizedSpectralFlowTerm q t‖ =
      Real.exp (t * (deningerRawThetaEigen q).re) *
        (1 / ‖deningerRawThetaEigen q‖ ^ 2) := by
  rw [deningerRegularizedSpectralFlowTerm, norm_div,
    norm_pow, Complex.norm_exp, div_eq_mul_inv]
  congr 1
  · simp [Complex.mul_re]
  · simp [one_div]

theorem norm_deningerRegularizedSpectralFlowTerm_le
    (q : XiZeroCopy) (t₀ t : ℝ)
    (ht : t ∈ Metric.ball t₀ 1 ∩ Ioi 0) :
    ‖deningerRegularizedSpectralFlowTerm q t‖ ≤
      Real.exp (t₀ + 1) *
        (1 / ‖deningerRawThetaEigen q‖ ^ 2) := by
  have htpos : 0 ≤ t := le_of_lt ht.2
  have htre : t < t₀ + 1 := by
    have habs : |t - t₀| < 1 := by
      simpa [Real.dist_eq] using ht.1
    have := (abs_lt.mp habs).2
    linarith
  have hrho := deningerRawThetaEigen_re_mem_open_unit q
  have hmul :
      t * (deningerRawThetaEigen q).re ≤ t := by
    have h :=
      mul_le_mul_of_nonneg_left hrho.2.le htpos
    simpa using h
  have hexp :
      Real.exp (t * (deningerRawThetaEigen q).re) ≤
        Real.exp (t₀ + 1) :=
    Real.exp_le_exp.mpr (hmul.trans htre.le)
  rw [norm_deningerRegularizedSpectralFlowTerm]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- The reciprocal-square regularized source flow converges locally uniformly on positive time. -/
theorem deningerRegularizedSpectralFlow_hasSumLocallyUniformlyOn :
    HasSumLocallyUniformlyOn
      deningerRegularizedSpectralFlowTerm
      deningerRegularizedSpectralFlow
      (Ioi 0) := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro t₀ ht₀
  refine ⟨Metric.ball t₀ 1 ∩ Ioi 0, ?_, ?_⟩
  · exact inter_mem
      (mem_nhdsWithin_of_mem_nhds
        (Metric.isOpen_ball.mem_nhds
          (Metric.mem_ball_self zero_lt_one)))
      self_mem_nhdsWithin
  · apply HasSumUniformlyOn.of_norm_le_summable
      (deningerRawThetaEigen_inv_sq_summable.mul_left
        (Real.exp (t₀ + 1)))
    intro q t ht
    exact norm_deningerRegularizedSpectralFlowTerm_le q t₀ t ht

/-- The regularized source-flow trace is continuous on positive time. -/
theorem continuousOn_deningerRegularizedSpectralFlow :
    ContinuousOn deningerRegularizedSpectralFlow (Ioi 0) := by
  apply deningerRegularizedSpectralFlow_hasSumLocallyUniformlyOn.continuousOn
  exact Frequently.of_forall (fun s => by
    apply continuousOn_finsetSum
    intro q hq
    unfold deningerRegularizedSpectralFlowTerm
    fun_prop)

/-- The regularized source-flow trace defines a regular distribution on positive time. -/
theorem deningerRegularizedSpectralFlow_locallyIntegrableOn :
    LocallyIntegrableOn
      deningerRegularizedSpectralFlow (Ioi 0) volume :=
  continuousOn_deningerRegularizedSpectralFlow.locallyIntegrableOn
    isOpen_Ioi.measurableSet

/-- Regular distribution before removing the reciprocal-square regularization. -/
noncomputable def deningerRegularizedH1FlowDistribution :
    DeningerTimeDistribution :=
  deningerRegularTimeDistribution deningerRegularizedSpectralFlow

/-- One positive-time distributional derivative. -/
noncomputable def deningerTimeDistributionDeriv :
    DeningerTimeDistribution →L[ℝ] DeningerTimeDistribution :=
  Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)

/-- One positive-time test-function derivative. -/
noncomputable def deningerTimeTestDerivative :
    DeningerTimeTestFunction →L[ℝ] DeningerTimeTestFunction :=
  TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ)

/--
Canonical distributional trace of the source `H¹` flow.

Two distributional derivatives remove the reciprocal-square regularization.  This definition is
valid without pointwise convergence of `Σρ exp (t ρ)`.
-/
noncomputable def deningerArithmeticH1TraceDistribution :
    DeningerTimeDistribution :=
  deningerTimeDistributionDeriv
    (deningerTimeDistributionDeriv
      deningerRegularizedH1FlowDistribution)

theorem deningerArithmeticH1TraceDistribution_apply
    (φ : DeningerTimeTestFunction) :
    deningerArithmeticH1TraceDistribution φ =
      deningerRegularizedH1FlowDistribution
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ)) := by
  rw [deningerArithmeticH1TraceDistribution,
    deningerTimeDistributionDeriv,
    Distribution.lineDerivCLM_apply,
    Distribution.lineDerivCLM_apply]
  simp [deningerTimeTestDerivative]

/-- Weight-zero endpoint trace function. -/
def deningerArithmeticH0TraceFunction (_t : ℝ) : ℂ :=
  1

/-- Weight-two endpoint trace function. -/
def deningerArithmeticH2TraceFunction (t : ℝ) : ℂ :=
  Complex.exp (t : ℂ)

theorem deningerArithmeticH0TraceFunction_locallyIntegrableOn :
    LocallyIntegrableOn
      deningerArithmeticH0TraceFunction (Ioi 0) volume := by
  apply ContinuousOn.locallyIntegrableOn
  · simpa [deningerArithmeticH0TraceFunction] using
      (continuous_const : Continuous
        (fun _ : ℝ => (1 : ℂ))).continuousOn
  · exact isOpen_Ioi.measurableSet

theorem deningerArithmeticH2TraceFunction_locallyIntegrableOn :
    LocallyIntegrableOn
      deningerArithmeticH2TraceFunction (Ioi 0) volume := by
  apply ContinuousOn.locallyIntegrableOn
  · unfold deningerArithmeticH2TraceFunction
    fun_prop
  · exact isOpen_Ioi.measurableSet

/-- Distributional trace of the source endpoint flow on `H⁰`. -/
noncomputable def deningerArithmeticH0TraceDistribution :
    DeningerTimeDistribution :=
  deningerRegularTimeDistribution deningerArithmeticH0TraceFunction

/-- Distributional trace of the source endpoint flow on `H²`. -/
noncomputable def deningerArithmeticH2TraceDistribution :
    DeningerTimeDistribution :=
  deningerRegularTimeDistribution deningerArithmeticH2TraceFunction

theorem deningerArithmeticH0TraceDistribution_apply
    (φ : DeningerTimeTestFunction) :
    deningerArithmeticH0TraceDistribution φ =
      ∫ t : ℝ, (φ t : ℂ) := by
  rw [deningerArithmeticH0TraceDistribution,
    deningerRegularTimeDistribution_apply
      deningerArithmeticH0TraceFunction_locallyIntegrableOn]
  simp [deningerArithmeticH0TraceFunction]

theorem deningerArithmeticH2TraceDistribution_apply
    (φ : DeningerTimeTestFunction) :
    deningerArithmeticH2TraceDistribution φ =
      ∫ t : ℝ, (φ t : ℂ) * Complex.exp (t : ℂ) := by
  rw [deningerArithmeticH2TraceDistribution,
    deningerRegularTimeDistribution_apply
      deningerArithmeticH2TraceFunction_locallyIntegrableOn]
  rfl

/-- Alternating distributional trace on source `H⁰ - H¹ + H²`. -/
noncomputable def deningerArithmeticAlternatingTraceDistribution :
    DeningerTimeDistribution :=
  deningerArithmeticH0TraceDistribution -
    deningerArithmeticH1TraceDistribution +
      deningerArithmeticH2TraceDistribution

/-- Archimedean local Lefschetz density on positive time. -/
def deningerArchimedeanLefschetzDensity (t : ℝ) : ℂ :=
  (((1 - Real.exp (-2 * t))⁻¹ : ℝ) : ℂ)

theorem deningerArchimedeanLefschetzDenominator_ne_zero
    {t : ℝ} (ht : t ∈ Ioi 0) :
    1 - Real.exp (-2 * t) ≠ 0 := by
  intro h
  have hexp : Real.exp (-2 * t) = 1 :=
    (sub_eq_zero.mp h).symm
  have : -2 * t = 0 :=
    (Real.exp_eq_one_iff _).mp hexp
  change 0 < t at ht
  linarith

theorem continuousOn_deningerArchimedeanLefschetzDensity :
    ContinuousOn deningerArchimedeanLefschetzDensity (Ioi 0) := by
  have hreal :
      ContinuousOn
        (fun t : ℝ => (1 - Real.exp (-2 * t))⁻¹)
        (Ioi 0) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht
      exact deningerArchimedeanLefschetzDenominator_ne_zero ht
  exact Complex.ofRealCLM.continuous.comp_continuousOn hreal

theorem deningerArchimedeanLefschetzDensity_locallyIntegrableOn :
    LocallyIntegrableOn
      deningerArchimedeanLefschetzDensity (Ioi 0) volume :=
  continuousOn_deningerArchimedeanLefschetzDensity.locallyIntegrableOn
    isOpen_Ioi.measurableSet

/-- Regular archimedean local term in Deninger's time-domain Lefschetz formula. -/
noncomputable def deningerArchimedeanLefschetzDistribution :
    DeningerTimeDistribution :=
  deningerRegularTimeDistribution
    deningerArchimedeanLefschetzDensity

theorem deningerArchimedeanLefschetzDistribution_apply
    (φ : DeningerTimeTestFunction) :
    deningerArchimedeanLefschetzDistribution φ =
      ∫ t : ℝ, (φ t : ℂ) *
        deningerArchimedeanLefschetzDensity t := by
  exact deningerRegularTimeDistribution_apply
    deningerArchimedeanLefschetzDensity_locallyIntegrableOn φ

end

end RHTower
