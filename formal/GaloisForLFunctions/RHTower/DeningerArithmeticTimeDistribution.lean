import GaloisForLFunctions.RHTower.DeningerArithmeticJetFrobenius
import GaloisForLFunctions.RHTower.XiConvergenceExponent
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

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
open scoped Distributions FourierTransform

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

private theorem deningerXiDivisorSupport_univ_countable :
    (Set.univ : Set XiDivisorSupport).Countable := by
  have hlocal : LocallyFiniteSupport
      (fun z : ℂ => MeromorphicOn.divisor xi Set.univ z) := by
    intro z
    exact (MeromorphicOn.divisor xi Set.univ).supportLocallyFiniteWithinDomain'
      z (Set.mem_univ z)
  apply hlocal.locallyFinite_support.countable_univ
  intro rho
  exact ⟨(rho : ℂ), rfl⟩

noncomputable local instance : Countable XiDivisorSupport :=
  Set.countable_univ_iff.mp
    deningerXiDivisorSupport_univ_countable

noncomputable local instance : Countable XiZeroCopy :=
  inferInstance

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

/-! ## Arbitrary compact-test Laplace amplitudes -/

/-- The positive-time Laplace amplitude used in Deninger's distributional explicit formula. -/
def deningerTimeTestLaplace
    (φ : DeningerTimeTestFunction) (s : ℂ) : ℂ :=
  ∫ t : ℝ, (φ t : ℂ) * Complex.exp ((t : ℂ) * s)

/-- On the one-dimensional time axis, the bundled test derivative is the ordinary derivative. -/
theorem deningerTimeTestDerivative_apply_eq_deriv
    (φ : DeningerTimeTestFunction) (t : ℝ) :
    deningerTimeTestDerivative φ t =
      deriv (fun x : ℝ => φ x) t := by
  rw [deningerTimeTestDerivative, TestFunction.lineDerivCLM_apply]
  rw [if_pos (by simp)]
  rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    fderiv_apply_one_eq_deriv]

set_option maxHeartbeats 800000 in
/--
Whole-line integration by parts for a positive-time test Laplace amplitude.

Compact support removes both endpoint terms; this is why the formula is intrinsic to
`𝓓((0,∞))`, with no value imposed at time zero.
-/
theorem deningerTimeTestLaplace_mul
    (φ : DeningerTimeTestFunction) (s : ℂ) :
    s * deningerTimeTestLaplace φ s =
      -deningerTimeTestLaplace
        (deningerTimeTestDerivative φ) s := by
  let u : ℝ → ℂ := fun t => (φ t : ℂ)
  let u' : ℝ → ℂ :=
    fun t => (deningerTimeTestDerivative φ t : ℂ)
  let v : ℝ → ℂ :=
    fun t => Complex.exp ((t : ℂ) * s)
  let v' : ℝ → ℂ :=
    fun t => s * Complex.exp ((t : ℂ) * s)
  have hu : ∀ t, HasDerivAt u (u' t) t := by
    intro t
    have hφ :
        HasDerivAt (fun x : ℝ => φ x)
          (deriv (fun x : ℝ => φ x) t) t :=
      (φ.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    simpa only [u, u', deningerTimeTestDerivative_apply_eq_deriv] using
      hφ.ofReal_comp
  have hv : ∀ t, HasDerivAt v (v' t) t := by
    intro t
    have hlin :
        HasDerivAt (fun x : ℝ => (x : ℂ) * s) s t := by
      convert ((hasDerivAt_id t).ofReal_comp.mul_const s) using 1
      all_goals simp
    simpa only [v, v', mul_comm] using hlin.cexp
  have huCont : Continuous u := by
    exact Complex.continuous_ofReal.comp φ.continuous
  have hu'Cont : Continuous u' := by
    exact Complex.continuous_ofReal.comp
      (deningerTimeTestDerivative φ).continuous
  have hvCont : Continuous v := by
    dsimp only [v]
    fun_prop
  have hv'Cont : Continuous v' := by
    dsimp only [v']
    fun_prop
  have huCompact : HasCompactSupport u := by
    simpa only [u, Function.comp_apply] using
      (φ.hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  have hu'Compact : HasCompactSupport u' := by
    simpa only [u', Function.comp_apply] using
      ((deningerTimeTestDerivative φ).hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  have huv : Integrable (u * v) :=
    (huCont.mul hvCont).integrable_of_hasCompactSupport
      huCompact.mul_right
  have huv' : Integrable (u * v') :=
    (huCont.mul hv'Cont).integrable_of_hasCompactSupport
      huCompact.mul_right
  have hu'v : Integrable (u' * v) :=
    (hu'Cont.mul hvCont).integrable_of_hasCompactSupport
      hu'Compact.mul_right
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (v := v) (u' := u') (v' := v')
    (fun t _ => hu t) (fun t _ => hv t) huv' hu'v huv
  have hleft :
      ∫ t : ℝ, u t * v' t =
        s * ∫ t : ℝ, u t * v t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [v']
    ring
  rw [hleft] at hparts
  simpa only [deningerTimeTestLaplace, u, u', v] using hparts

/-- Two integrations by parts expose the reciprocal-square spectral regularization. -/
theorem deningerTimeTestLaplace_mul_sq
    (φ : DeningerTimeTestFunction) (s : ℂ) :
    s ^ 2 * deningerTimeTestLaplace φ s =
      deningerTimeTestLaplace
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ)) s := by
  calc
    s ^ 2 * deningerTimeTestLaplace φ s =
        s * (s * deningerTimeTestLaplace φ s) := by ring
    _ = s * (-deningerTimeTestLaplace
        (deningerTimeTestDerivative φ) s) := by
      rw [deningerTimeTestLaplace_mul]
    _ = -(s * deningerTimeTestLaplace
        (deningerTimeTestDerivative φ) s) := by ring
    _ = -(-deningerTimeTestLaplace
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ)) s) := by
      rw [deningerTimeTestLaplace_mul]
    _ = deningerTimeTestLaplace
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ)) s := by ring

set_option maxHeartbeats 600000 in
/-- The Laplace amplitude of every positive-time test is an entire function. -/
theorem analyticOnNhd_deningerTimeTestLaplace
    (φ : DeningerTimeTestFunction) :
    AnalyticOnNhd ℂ
      (deningerTimeTestLaplace φ) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro s₀
  let F : ℂ → ℝ → ℂ :=
    fun s t =>
      (φ t : ℂ) * Complex.exp ((t : ℂ) * s)
  let F' : ℂ → ℝ → ℂ :=
    fun s t =>
      (φ t : ℂ) *
        (Complex.exp ((t : ℂ) * s) * (t : ℂ))
  let bound : ℝ → ℝ :=
    fun t =>
      ‖(φ t : ℂ)‖ *
        (|t| * Real.exp (|t| * (‖s₀‖ + 1)))
  have hφCompact :
      HasCompactSupport (fun t : ℝ => (φ t : ℂ)) := by
    simpa only [Function.comp_apply] using
      (φ.hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  have hFCont : ∀ s : ℂ, Continuous (F s) := by
    intro s
    dsimp only [F]
    fun_prop
  have hF'Cont : ∀ s : ℂ, Continuous (F' s) := by
    intro s
    dsimp only [F']
    fun_prop
  have hFInt : ∀ s : ℂ, Integrable (F s) := by
    intro s
    exact (hFCont s).integrable_of_hasCompactSupport
      hφCompact.mul_right
  have hboundCont : Continuous bound := by
    dsimp only [bound]
    fun_prop
  have hboundCompact : HasCompactSupport bound := by
    dsimp only [bound]
    exact hφCompact.norm.mul_right
  have hboundInt : Integrable bound :=
    hboundCont.integrable_of_hasCompactSupport hboundCompact
  have hdiff :
      ∀ t : ℝ, ∀ s : ℂ,
        HasDerivAt (fun z : ℂ => F z t) (F' s t) s := by
    intro t s
    have hlin :
        HasDerivAt
          (fun z : ℂ => (t : ℂ) * z)
          (t : ℂ) s := by
      simpa using
        ((hasDerivAt_id s).const_mul (t : ℂ))
    simpa only [F, F', mul_assoc] using
      hlin.cexp.const_mul (φ t : ℂ)
  have hnormBound :
      ∀ t : ℝ, ∀ s ∈ Metric.closedBall s₀ 1,
        ‖F' s t‖ ≤ bound t := by
    intro t s hs
    have hdist : ‖s - s₀‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_eq] using hs
    have hsnorm : ‖s‖ ≤ ‖s₀‖ + 1 := by
      calc
        ‖s‖ ≤ ‖s₀‖ + ‖s - s₀‖ :=
          norm_le_norm_add_norm_sub' s s₀
        _ ≤ ‖s₀‖ + 1 := by gcongr
    have htre :
        t * s.re ≤ |t| * (‖s₀‖ + 1) := by
      calc
        t * s.re ≤ |t * s.re| :=
          le_abs_self _
        _ = |t| * |s.re| := abs_mul t s.re
        _ ≤ |t| * ‖s‖ :=
          mul_le_mul_of_nonneg_left
            (Complex.abs_re_le_norm s) (abs_nonneg t)
        _ ≤ |t| * (‖s₀‖ + 1) :=
          mul_le_mul_of_nonneg_left hsnorm (abs_nonneg t)
    have hexp :
        Real.exp (((t : ℂ) * s).re) ≤
          Real.exp (|t| * (‖s₀‖ + 1)) := by
      rw [show ((t : ℂ) * s).re = t * s.re by
        simp [Complex.mul_re]]
      exact Real.exp_le_exp.mpr htre
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs]
    rw [show ‖(t : ℂ)‖ = |t| by simp]
    calc
      |φ t| * (Real.exp (((t : ℂ) * s).re) * |t|) =
          |φ t| * (|t| * Real.exp (((t : ℂ) * s).re)) := by
        ring
      _ ≤ |φ t| *
          (|t| * Real.exp (|t| * (‖s₀‖ + 1))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (abs_nonneg t))
          (abs_nonneg (φ t))
  have hderiv :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (x₀ := s₀) (s := Metric.closedBall s₀ 1)
      (F := F) (F' := F') (bound := bound)
      (Metric.closedBall_mem_nhds s₀ zero_lt_one)
      (Filter.Eventually.of_forall
        (fun s => (hFCont s).aestronglyMeasurable))
      (hFInt s₀)
      (hF'Cont s₀).aestronglyMeasurable
      (Filter.Eventually.of_forall hnormBound)
      hboundInt
      (Filter.Eventually.of_forall
        (fun t s _hs => hdiff t s))
  have hderivAt :
      HasDerivAt
        (fun s => ∫ t : ℝ, F s t)
        (∫ t : ℝ, F' s₀ t) s₀ :=
    hderiv.2
  simpa only [deningerTimeTestLaplace, F] using
    hderivAt.differentiableAt

/-- Deninger's test amplitude in the centered Xi contour coordinate. -/
def deningerCenteredTimeTestTransform
    (φ : DeningerTimeTestFunction) (z : ℂ) : ℂ :=
  deningerTimeTestLaplace φ
    (1 / 2 + z * Complex.I)

/-- The centered transform is entire, as required by the Xi source contour theorem. -/
theorem analyticOnNhd_deningerCenteredTimeTestTransform
    (φ : DeningerTimeTestFunction) :
    AnalyticOnNhd ℂ
      (deningerCenteredTimeTestTransform φ)
      Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  have hlap :
      Differentiable ℂ (deningerTimeTestLaplace φ) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp
      (analyticOnNhd_deningerTimeTestLaplace φ)
  exact hlap.comp
    (by
      fun_prop)

/-- Centering sends each Xi spectral copy back to its raw Frobenius eigenvalue. -/
theorem deningerCenteredTimeTestTransform_xiSpectralPoint
    (φ : DeningerTimeTestFunction) (q : XiZeroCopy) :
    deningerCenteredTimeTestTransform φ
        (xiSpectralPoint q) =
      deningerTimeTestLaplace φ
        (deningerRawThetaEigen q) := by
  rw [deningerCenteredTimeTestTransform,
    deningerRawThetaEigen]
  apply congrArg (deningerTimeTestLaplace φ)
  simp only [xiSpectralPoint]
  have hI :
      (-Complex.I) * Complex.I = (1 : ℂ) := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  rw [mul_assoc, hI, mul_one]
  ring

/-! ## Fourier inversion of Deninger's arbitrary test amplitude -/

/-- Exponential tilt of a positive-time test on a vertical Laplace line. -/
def deningerExponentiallyTiltedTimeTest
    (φ : DeningerTimeTestFunction) (c t : ℝ) : ℂ :=
  (φ t : ℂ) * Complex.exp ((c * t : ℝ) : ℂ)

theorem continuous_deningerExponentiallyTiltedTimeTest
    (φ : DeningerTimeTestFunction) (c : ℝ) :
    Continuous
      (deningerExponentiallyTiltedTimeTest φ c) := by
  unfold deningerExponentiallyTiltedTimeTest
  fun_prop

theorem contDiff_deningerExponentiallyTiltedTimeTest
    (φ : DeningerTimeTestFunction) (c : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (deningerExponentiallyTiltedTimeTest φ c) := by
  have hφC :
      ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun t : ℝ => (φ t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hexpR :
      ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun t : ℝ => Real.exp (c * t)) := by
    fun_prop
  have hexpC :
      ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun t : ℝ => (Real.exp (c * t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexpR
  simpa only [deningerExponentiallyTiltedTimeTest,
    Complex.ofReal_exp] using hφC.mul hexpC

theorem hasCompactSupport_deningerExponentiallyTiltedTimeTest
    (φ : DeningerTimeTestFunction) (c : ℝ) :
    HasCompactSupport
      (deningerExponentiallyTiltedTimeTest φ c) := by
  have hφCompact :
      HasCompactSupport (fun t : ℝ => (φ t : ℂ)) := by
    simpa only [Function.comp_apply] using
      (φ.hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  exact hφCompact.mul_right

/-- The exponentially tilted test bundled as a Schwartz function. -/
noncomputable def deningerExponentiallyTiltedTimeSchwartz
    (φ : DeningerTimeTestFunction) (c : ℝ) :
    SchwartzMap ℝ ℂ :=
  (hasCompactSupport_deningerExponentiallyTiltedTimeTest φ c).toSchwartzMap
    (contDiff_deningerExponentiallyTiltedTimeTest φ c)

@[simp]
theorem deningerExponentiallyTiltedTimeSchwartz_apply
    (φ : DeningerTimeTestFunction) (c t : ℝ) :
    deningerExponentiallyTiltedTimeSchwartz φ c t =
      deningerExponentiallyTiltedTimeTest φ c t := by
  rfl

/--
The vertical Laplace amplitude is exactly the Fourier transform of the exponentially tilted
time test, with mathlib's `2π` Fourier normalization.
-/
theorem fourier_deningerExponentiallyTiltedTimeTest
    (φ : DeningerTimeTestFunction) (c ξ : ℝ) :
    𝓕 (deningerExponentiallyTiltedTimeTest φ c) ξ =
      deningerTimeTestLaplace φ
        ((c : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
  rw [Real.fourier_eq', deningerTimeTestLaplace]
  apply integral_congr_ae
  filter_upwards with t
  simp only [RCLike.inner_apply, conj_trivial,
    ofReal_mul, smul_eq_mul,
    deningerExponentiallyTiltedTimeTest]
  calc
    Complex.exp
          ((-2 : ℂ) * Real.pi * (ξ * t) *
            Complex.I) *
        ((φ t : ℂ) *
          Complex.exp ((c : ℂ) * t)) =
      (φ t : ℂ) *
        (Complex.exp
            ((-2 : ℂ) * Real.pi * (ξ * t) *
              Complex.I) *
          Complex.exp ((c : ℂ) * t)) := by ring
    _ = (φ t : ℂ) *
        Complex.exp
          (((-2 : ℂ) * Real.pi * (ξ * t) *
              Complex.I) +
            (c : ℂ) * t) := by
      rw [Complex.exp_add]
    _ = (φ t : ℂ) *
        Complex.exp
          ((t : ℂ) *
            ((c : ℂ) -
              (2 * Real.pi * ξ : ℝ) *
                Complex.I)) := by
      congr 1
      push_cast
      ring

theorem integrable_deningerExponentiallyTiltedTimeTest
    (φ : DeningerTimeTestFunction) (c : ℝ) :
    Integrable
      (deningerExponentiallyTiltedTimeTest φ c) :=
  (deningerExponentiallyTiltedTimeSchwartz φ c).integrable

theorem integrable_fourier_deningerExponentiallyTiltedTimeTest
    (φ : DeningerTimeTestFunction) (c : ℝ) :
    Integrable
      (𝓕 (deningerExponentiallyTiltedTimeTest φ c)) := by
  have hSchwartz :
      Integrable
        (fun ξ : ℝ =>
          (𝓕 (deningerExponentiallyTiltedTimeSchwartz φ c) :
            SchwartzMap ℝ ℂ) ξ) :=
    (𝓕 (deningerExponentiallyTiltedTimeSchwartz φ c) :
      SchwartzMap ℝ ℂ).integrable
  simpa only [SchwartzMap.fourier_coe] using hSchwartz

/--
Vertical Fourier inversion for Deninger's Laplace amplitude:

`∫ exp(2π i ξ x) Φ(c - 2π i ξ) dξ = φ(x) exp(c x)`.
-/
theorem integral_fourierKernel_mul_deningerTimeTestLaplace
    (φ : DeningerTimeTestFunction) (c x : ℝ) :
    (∫ ξ : ℝ,
        Complex.exp
            (((2 * Real.pi * ξ * x : ℝ) : ℂ) *
              Complex.I) *
          deningerTimeTestLaplace φ
            ((c : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) =
      deningerExponentiallyTiltedTimeTest φ c x := by
  have hinv :
      𝓕⁻ (𝓕
          (deningerExponentiallyTiltedTimeTest φ c)) x =
        deningerExponentiallyTiltedTimeTest φ c x :=
    (integrable_deningerExponentiallyTiltedTimeTest φ c).fourierInv_fourier_eq
      (integrable_fourier_deningerExponentiallyTiltedTimeTest φ c)
      (continuous_deningerExponentiallyTiltedTimeTest φ c).continuousAt
  rw [Real.fourierInv_eq'] at hinv
  simpa only [RCLike.inner_apply, conj_trivial,
    ofReal_mul, Complex.real_smul, smul_eq_mul,
    fourier_deningerExponentiallyTiltedTimeTest,
    mul_comm] using hinv

/-- `L¹` mass controlling every critical-strip Laplace amplitude after two derivatives. -/
def deningerTimeTestSecondDerivativeExponentialMass
    (φ : DeningerTimeTestFunction) : ℝ :=
  ∫ t : ℝ,
    ‖(deningerTimeTestDerivative
      (deningerTimeTestDerivative φ) t : ℂ)‖ *
        Real.exp |t|

theorem deningerTimeTestSecondDerivativeExponentialMass_nonneg
    (φ : DeningerTimeTestFunction) :
    0 ≤ deningerTimeTestSecondDerivativeExponentialMass φ := by
  exact integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

set_option maxHeartbeats 400000 in
private theorem deningerTimeTestSecondDerivativeExponentialIntegrable
    (φ : DeningerTimeTestFunction) :
    Integrable
      (fun t : ℝ =>
        ‖(deningerTimeTestDerivative
          (deningerTimeTestDerivative φ) t : ℂ)‖ *
            Real.exp |t|) := by
  let d2 : ℝ → ℂ :=
    fun t =>
      (deningerTimeTestDerivative
        (deningerTimeTestDerivative φ) t : ℂ)
  have hcont :
      Continuous
        (fun t : ℝ =>
          ‖d2 t‖ *
              Real.exp |t|) := by
    fun_prop
  have hd2Compact : HasCompactSupport d2 := by
    simpa only [d2, Function.comp_apply] using
      ((deningerTimeTestDerivative
        (deningerTimeTestDerivative φ)).hasCompactSupport.comp_left
          (g := fun r : ℝ => (r : ℂ)) rfl)
  have hprodCompact :
      HasCompactSupport
        (fun t : ℝ => ‖d2 t‖ * Real.exp |t|) := by
    exact hd2Compact.norm.mul_right
  simpa only [d2] using
    hcont.integrable_of_hasCompactSupport hprodCompact

/-- The twice-differentiated Laplace amplitude is bounded uniformly on the closed critical strip. -/
theorem norm_deningerTimeTestLaplace_secondDerivative_le
    (φ : DeningerTimeTestFunction) {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖deningerTimeTestLaplace
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ)) s‖ ≤
      deningerTimeTestSecondDerivativeExponentialMass φ := by
  let d2 : ℝ → ℂ :=
    fun t =>
      (deningerTimeTestDerivative
        (deningerTimeTestDerivative φ) t : ℂ)
  let e : ℝ → ℂ :=
    fun t => Complex.exp ((t : ℂ) * s)
  have hd2Cont : Continuous d2 := by
    exact Complex.continuous_ofReal.comp
      (deningerTimeTestDerivative
        (deningerTimeTestDerivative φ)).continuous
  have heCont : Continuous e := by
    dsimp only [e]
    fun_prop
  have hd2Compact : HasCompactSupport d2 := by
    simpa only [d2, Function.comp_apply] using
      ((deningerTimeTestDerivative
        (deningerTimeTestDerivative φ)).hasCompactSupport.comp_left
          (g := fun r : ℝ => (r : ℂ)) rfl)
  have hprodInt : Integrable (d2 * e) :=
    (hd2Cont.mul heCont).integrable_of_hasCompactSupport
      hd2Compact.mul_right
  have hpoint : ∀ t : ℝ,
      ‖d2 t * e t‖ ≤ ‖d2 t‖ * Real.exp |t| := by
    intro t
    have htre : t * s.re ≤ |t| := by
      by_cases ht : 0 ≤ t
      · calc
          t * s.re ≤ t * 1 :=
            mul_le_mul_of_nonneg_left hs1 ht
          _ = t := mul_one t
          _ ≤ |t| := le_abs_self t
      · have ht' : t ≤ 0 := le_of_not_ge ht
        exact
          (mul_nonpos_of_nonpos_of_nonneg ht' hs0).trans
            (abs_nonneg t)
    rw [norm_mul]
    dsimp only [e]
    rw [Complex.norm_exp]
    have hre : ((t : ℂ) * s).re = t * s.re := by
      simp [Complex.mul_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr htre) (norm_nonneg _)
  calc
    ‖deningerTimeTestLaplace
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ)) s‖ =
        ‖∫ t : ℝ, d2 t * e t‖ := by
      rfl
    _ ≤ ∫ t : ℝ, ‖d2 t * e t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖d2 t‖ * Real.exp |t| :=
      integral_mono hprodInt.norm
        (by
          simpa only [d2] using
            deningerTimeTestSecondDerivativeExponentialIntegrable φ)
        hpoint
    _ = deningerTimeTestSecondDerivativeExponentialMass φ := by
      rfl

/-- Reciprocal-square bound for arbitrary positive-time test amplitudes at source eigenvalues. -/
theorem norm_deningerTimeTestLaplace_rawThetaEigen_le
    (φ : DeningerTimeTestFunction) (q : XiZeroCopy) :
    ‖deningerTimeTestLaplace φ (deningerRawThetaEigen q)‖ ≤
      deningerTimeTestSecondDerivativeExponentialMass φ /
        ‖deningerRawThetaEigen q‖ ^ 2 := by
  have hrho := deningerRawThetaEigen_re_mem_open_unit q
  have hsecond :=
    norm_deningerTimeTestLaplace_secondDerivative_le φ
      hrho.1.le hrho.2.le
  have hmul :
      ‖deningerRawThetaEigen q‖ ^ 2 *
          ‖deningerTimeTestLaplace φ
            (deningerRawThetaEigen q)‖ ≤
        deningerTimeTestSecondDerivativeExponentialMass φ := by
    calc
      ‖deningerRawThetaEigen q‖ ^ 2 *
          ‖deningerTimeTestLaplace φ
            (deningerRawThetaEigen q)‖ =
          ‖deningerRawThetaEigen q ^ 2 *
            deningerTimeTestLaplace φ
              (deningerRawThetaEigen q)‖ := by
            rw [norm_mul, norm_pow]
      _ = ‖deningerTimeTestLaplace
          (deningerTimeTestDerivative
            (deningerTimeTestDerivative φ))
              (deningerRawThetaEigen q)‖ := by
        rw [deningerTimeTestLaplace_mul_sq]
      _ ≤ deningerTimeTestSecondDerivativeExponentialMass φ :=
        hsecond
  exact (le_div_iff₀
    (pow_pos (norm_pos_iff.mpr
      (deningerRawThetaEigen_ne_zero q)) 2)).2
        (by simpa only [mul_comm] using hmul)

/--
For every compactly supported smooth positive-time test, the complete multiplicity-exact
spectral side `Σρ Φ(ρ)` is absolutely convergent.
-/
theorem deningerTimeTestLaplace_rawThetaEigen_summable
    (φ : DeningerTimeTestFunction) :
    Summable
      (fun q : XiZeroCopy =>
        deningerTimeTestLaplace φ
          (deningerRawThetaEigen q)) := by
  apply Summable.of_norm
  exact
    ((deningerRawThetaEigen_inv_sq_summable.mul_left
      (deningerTimeTestSecondDerivativeExponentialMass φ)).of_nonneg_of_le
        (fun _ => norm_nonneg _)
        (fun q => by
          have h :=
            norm_deningerTimeTestLaplace_rawThetaEigen_le φ q
          simpa only [div_eq_mul_inv, one_mul] using h))

/--
Every prescribed finite packet of source eigenvalues lies in an admissible Xi rectangle whose
continued prime--archimedean contour is exactly Deninger's finite test-amplitude sum.
-/
theorem exists_admissible_deningerTimeTestContour_eq_spectralSum_containing
    (φ : DeningerTimeTestFunction)
    (t : Finset XiZeroCopy) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (∀ q ∈ t,
        q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
      rectIntegral
          (fun z =>
            deningerCenteredTimeTestTransform φ z *
              continuedPrimeArchSourceRelativeTrace z)
          z₁ z₂ =
        2 * Real.pi * Complex.I *
          ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
            deningerTimeTestLaplace φ
              (deningerRawThetaEigen q) := by
  obtain ⟨z₁, z₂, hre, him, hcontains, hcontour⟩ :=
    exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing
      t (analyticOnNhd_deningerCenteredTimeTestTransform φ)
  refine ⟨z₁, z₂, hre, him, hcontains, ?_⟩
  rw [hcontour]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  exact deningerCenteredTimeTestTransform_xiSpectralPoint φ q

/--
The full `H¹` spectral trace is a cofinal normalized contour limit of the independently defined
continued prime--archimedean source, for every positive-time test.
-/
theorem exists_admissible_deningerTimeTest_normalizedContour_approximates_spectralSum
    (φ : DeningerTimeTestFunction)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      dist
        ((2 * Real.pi * Complex.I)⁻¹ *
          rectIntegral
            (fun z =>
              deningerCenteredTimeTestTransform φ z *
                continuedPrimeArchSourceRelativeTrace z)
            z₁ z₂)
        (∑' q : XiZeroCopy,
          deningerTimeTestLaplace φ
            (deningerRawThetaEigen q)) <
        epsilon := by
  let f : XiZeroCopy → ℂ :=
    fun q =>
      deningerTimeTestLaplace φ
        (deningerRawThetaEigen q)
  have hsum : Summable f :=
    deningerTimeTestLaplace_rawThetaEigen_summable φ
  have hball :
      Metric.ball (∑' q, f q) epsilon ∈
        nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent :
      ∀ᶠ s : Finset XiZeroCopy in atTop,
        ∑ q ∈ s, f q ∈
          Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hcontains, hcontour⟩ :=
    exists_admissible_deningerTimeTestContour_eq_spectralSum_containing
      φ t
  refine ⟨z₁, z₂, hre, him, ?_⟩
  have hpacket :
      t ≤ xiZeroCopyClosedRectangle z₁ z₂ := by
    intro q hq
    exact hcontains q hq
  have hnear :=
    ht (xiZeroCopyClosedRectangle z₁ z₂) hpacket
  rw [Metric.mem_ball] at hnear
  have hc :
      (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  rw [hcontour, ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]
  simpa only [f] using hnear

private theorem deningerCriticalStrip_time_mul_re_le_abs
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1)
    (t : ℝ) :
    t * s.re ≤ |t| := by
  by_cases ht : 0 ≤ t
  · calc
      t * s.re ≤ t * 1 :=
        mul_le_mul_of_nonneg_left hs1 ht
      _ = t := mul_one t
      _ ≤ |t| := le_abs_self t
  · have ht' : t ≤ 0 := le_of_not_ge ht
    exact
      (mul_nonpos_of_nonpos_of_nonneg ht' hs0).trans
        (abs_nonneg t)

private theorem deningerH1RegularizedTraceTerm_integrable
    (φ : DeningerTimeTestFunction) (q : XiZeroCopy) :
    Integrable
      (fun t : ℝ =>
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ) t : ℂ) *
            deningerRegularizedSpectralFlowTerm q t) := by
  have hd2Cont :
      Continuous
        (fun t : ℝ =>
          (deningerTimeTestDerivative
            (deningerTimeTestDerivative φ) t : ℂ)) :=
    Complex.continuous_ofReal.comp
      (deningerTimeTestDerivative
        (deningerTimeTestDerivative φ)).continuous
  have htermCont :
      Continuous
        (deningerRegularizedSpectralFlowTerm q) := by
    unfold deningerRegularizedSpectralFlowTerm
    fun_prop
  have hd2Compact :
      HasCompactSupport
        (fun t : ℝ =>
          (deningerTimeTestDerivative
            (deningerTimeTestDerivative φ) t : ℂ)) := by
    simpa only [Function.comp_apply] using
      ((deningerTimeTestDerivative
        (deningerTimeTestDerivative φ)).hasCompactSupport.comp_left
          (g := fun r : ℝ => (r : ℂ)) rfl)
  exact
    (hd2Cont.mul htermCont).integrable_of_hasCompactSupport
      hd2Compact.mul_right

private theorem integral_norm_deningerH1RegularizedTraceTerm_le
    (φ : DeningerTimeTestFunction) (q : XiZeroCopy) :
    (∫ t : ℝ,
        ‖(deningerTimeTestDerivative
          (deningerTimeTestDerivative φ) t : ℂ) *
            deningerRegularizedSpectralFlowTerm q t‖) ≤
      deningerTimeTestSecondDerivativeExponentialMass φ *
        (1 / ‖deningerRawThetaEigen q‖ ^ 2) := by
  let d2 : ℝ → ℂ :=
    fun t =>
      (deningerTimeTestDerivative
        (deningerTimeTestDerivative φ) t : ℂ)
  have hrho := deningerRawThetaEigen_re_mem_open_unit q
  have hpoint : ∀ t : ℝ,
      ‖d2 t * deningerRegularizedSpectralFlowTerm q t‖ ≤
        (‖d2 t‖ * Real.exp |t|) *
          (1 / ‖deningerRawThetaEigen q‖ ^ 2) := by
    intro t
    have htre :=
      deningerCriticalStrip_time_mul_re_le_abs
        hrho.1.le hrho.2.le t
    rw [norm_mul,
      norm_deningerRegularizedSpectralFlowTerm]
    have hexp :
        Real.exp (t * (deningerRawThetaEigen q).re) ≤
          Real.exp |t| :=
      Real.exp_le_exp.mpr htre
    have hinv :
        0 ≤ 1 / ‖deningerRawThetaEigen q‖ ^ 2 := by
      positivity
    calc
      ‖d2 t‖ *
          (Real.exp (t * (deningerRawThetaEigen q).re) *
            (1 / ‖deningerRawThetaEigen q‖ ^ 2)) =
          (‖d2 t‖ *
            Real.exp (t * (deningerRawThetaEigen q).re)) *
              (1 / ‖deningerRawThetaEigen q‖ ^ 2) := by ring
      _ ≤ (‖d2 t‖ * Real.exp |t|) *
          (1 / ‖deningerRawThetaEigen q‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (norm_nonneg _))
          hinv
  have hmajorInt :
      Integrable
        (fun t : ℝ =>
          (‖d2 t‖ * Real.exp |t|) *
            (1 / ‖deningerRawThetaEigen q‖ ^ 2)) := by
    have hbase :
        Integrable
          (fun t : ℝ => ‖d2 t‖ * Real.exp |t|) := by
      simpa only [d2] using
        deningerTimeTestSecondDerivativeExponentialIntegrable φ
    exact hbase.mul_const _
  calc
    (∫ t : ℝ,
        ‖(deningerTimeTestDerivative
          (deningerTimeTestDerivative φ) t : ℂ) *
            deningerRegularizedSpectralFlowTerm q t‖) =
        ∫ t : ℝ,
          ‖d2 t * deningerRegularizedSpectralFlowTerm q t‖ := by
      rfl
    _ ≤ ∫ t : ℝ,
        (‖d2 t‖ * Real.exp |t|) *
          (1 / ‖deningerRawThetaEigen q‖ ^ 2) :=
      integral_mono
        (deningerH1RegularizedTraceTerm_integrable φ q).norm
        hmajorInt hpoint
    _ = deningerTimeTestSecondDerivativeExponentialMass φ *
        (1 / ‖deningerRawThetaEigen q‖ ^ 2) := by
      rw [integral_mul_const]
      rfl

private theorem deningerH1RegularizedTraceTerm_integral_norm_summable
    (φ : DeningerTimeTestFunction) :
    Summable
      (fun q : XiZeroCopy =>
        ∫ t : ℝ,
          ‖(deningerTimeTestDerivative
            (deningerTimeTestDerivative φ) t : ℂ) *
              deningerRegularizedSpectralFlowTerm q t‖) := by
  exact
    ((deningerRawThetaEigen_inv_sq_summable.mul_left
      (deningerTimeTestSecondDerivativeExponentialMass φ)).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun q => by
          simpa only [one_mul] using
            integral_norm_deningerH1RegularizedTraceTerm_le φ q))

private theorem integral_deningerH1RegularizedTraceTerm_eq_laplace
    (φ : DeningerTimeTestFunction) (q : XiZeroCopy) :
    (∫ t : ℝ,
        (deningerTimeTestDerivative
          (deningerTimeTestDerivative φ) t : ℂ) *
            deningerRegularizedSpectralFlowTerm q t) =
      deningerTimeTestLaplace φ
        (deningerRawThetaEigen q) := by
  let d2φ :=
    deningerTimeTestDerivative
      (deningerTimeTestDerivative φ)
  let rho := deningerRawThetaEigen q
  have hrho : rho ≠ 0 :=
    deningerRawThetaEigen_ne_zero q
  calc
    (∫ t : ℝ,
        (d2φ t : ℂ) *
          deningerRegularizedSpectralFlowTerm q t) =
        (rho ^ 2)⁻¹ *
          deningerTimeTestLaplace d2φ rho := by
      rw [deningerTimeTestLaplace]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [deningerRegularizedSpectralFlowTerm,
        rho, d2φ, div_eq_mul_inv]
      ring
    _ = (rho ^ 2)⁻¹ *
        (rho ^ 2 * deningerTimeTestLaplace φ rho) := by
      rw [deningerTimeTestLaplace_mul_sq]
    _ = deningerTimeTestLaplace φ rho := by
      field_simp

/--
The distributional `H¹` trace acts on an arbitrary test by the complete multiplicity-exact
spectral sum `Σρ Φ(ρ)`.  No pointwise convergence of `Σρ exp(tρ)` is assumed.
-/
theorem deningerArithmeticH1TraceDistribution_apply_eq_spectralSum
    (φ : DeningerTimeTestFunction) :
    deningerArithmeticH1TraceDistribution φ =
      ∑' q : XiZeroCopy,
        deningerTimeTestLaplace φ
          (deningerRawThetaEigen q) := by
  let d2φ :=
    deningerTimeTestDerivative
      (deningerTimeTestDerivative φ)
  let F : XiZeroCopy → ℝ → ℂ :=
    fun q t =>
      (d2φ t : ℂ) *
        deningerRegularizedSpectralFlowTerm q t
  have hswap :
      (∑' q : XiZeroCopy, ∫ t : ℝ, F q t) =
        ∫ t : ℝ, ∑' q : XiZeroCopy, F q t := by
    exact integral_tsum_of_summable_integral_norm
      (fun q => by
        simpa only [F, d2φ] using
          deningerH1RegularizedTraceTerm_integrable φ q)
      (by
        simpa only [F, d2φ] using
          deningerH1RegularizedTraceTerm_integral_norm_summable φ)
  rw [deningerArithmeticH1TraceDistribution_apply]
  rw [deningerRegularizedH1FlowDistribution,
    deningerRegularTimeDistribution_apply
      deningerRegularizedSpectralFlow_locallyIntegrableOn]
  calc
    (∫ t : ℝ, (d2φ t : ℂ) *
        deningerRegularizedSpectralFlow t) =
        ∫ t : ℝ, ∑' q : XiZeroCopy, F q t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [deningerRegularizedSpectralFlow]
      change
        (d2φ t : ℂ) *
            (∑' q : XiZeroCopy,
              deningerRegularizedSpectralFlowTerm q t) =
          ∑' q : XiZeroCopy,
            (d2φ t : ℂ) *
              deningerRegularizedSpectralFlowTerm q t
      rw [← tsum_mul_left]
    _ = ∑' q : XiZeroCopy, ∫ t : ℝ, F q t :=
      hswap.symm
    _ = ∑' q : XiZeroCopy,
        deningerTimeTestLaplace φ
          (deningerRawThetaEigen q) := by
      apply tsum_congr
      intro q
      simpa only [F, d2φ] using
        integral_deningerH1RegularizedTraceTerm_eq_laplace φ q

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

/-- Natural-number indices `n ≥ 2` for the von-Mangoldt prime-power comb. -/
abbrev DeningerPrimePowerIndex :=
  {n : ℕ // 2 ≤ n}

/-- Positive time attached to `n`; von Mangoldt makes the non-prime-power coefficients vanish. -/
def deningerPrimePowerTime (n : DeningerPrimePowerIndex) : ℝ :=
  Real.log (n : ℕ)

/-- Von-Mangoldt coefficient of one positive-time atom. -/
def deningerPrimePowerWeight (n : DeningerPrimePowerIndex) : ℝ :=
  ArithmeticFunction.vonMangoldt (n : ℕ)

theorem deningerPrimePowerTime_pos (n : DeningerPrimePowerIndex) :
    0 < deningerPrimePowerTime n := by
  rw [deningerPrimePowerTime]
  apply Real.log_pos
  exact_mod_cast lt_of_lt_of_le Nat.one_lt_two n.property

/-- Prime `p` and positive exponent `k+1`, regarded as a positive-integer time atom. -/
def deningerEulerPrimePowerIndex
    (pk : Nat.Primes × ℕ) : DeningerPrimePowerIndex :=
  ⟨pk.1 ^ (pk.2 + 1),
    by
      have h :=
        Nat.one_lt_pow (Nat.succ_ne_zero pk.2)
          pk.1.2.one_lt
      have h' : 1 < (pk.1 : ℕ) ^ (pk.2 + 1) := by
        simpa [Nat.succ_eq_add_one] using h
      omega⟩

theorem deningerEulerPrimePowerIndex_injective :
    Function.Injective deningerEulerPrimePowerIndex := by
  intro x y h
  apply Nat.Primes.prodNatEquiv.injective
  apply Subtype.ext
  have hv :
      (deningerEulerPrimePowerIndex x : ℕ) =
        (deningerEulerPrimePowerIndex y : ℕ) :=
    congrArg (fun z : DeningerPrimePowerIndex => (z : ℕ)) h
  simpa [deningerEulerPrimePowerIndex,
    Nat.Primes.prodNatEquiv_apply] using hv

/-- A prime-power atom has Deninger's orbit time `(k+1) log p`. -/
theorem deningerPrimePowerTime_euler
    (pk : Nat.Primes × ℕ) :
    deningerPrimePowerTime
        (deningerEulerPrimePowerIndex pk) =
      (pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ) := by
  change
    Real.log ((((pk.1 : ℕ) ^ (pk.2 + 1) : ℕ) : ℝ)) =
      (pk.2 + 1 : ℝ) * Real.log (pk.1 : ℕ)
  rw [Nat.cast_pow, Real.log_pow]
  simp

/-- A prime-power atom has coefficient `log p`, independently of its iterate depth. -/
theorem deningerPrimePowerWeight_euler
    (pk : Nat.Primes × ℕ) :
    deningerPrimePowerWeight
        (deningerEulerPrimePowerIndex pk) =
      Real.log (pk.1 : ℕ) := by
  change
    ArithmeticFunction.vonMangoldt
        ((pk.1 : ℕ) ^ (pk.2 + 1)) =
      Real.log (pk.1 : ℕ)
  rw [ArithmeticFunction.vonMangoldt_apply_pow
      (Nat.succ_ne_zero pk.2),
    ArithmeticFunction.vonMangoldt_apply_prime pk.1.2]

/--
Every nonzero von-Mangoldt atom is represented by a unique prime and positive exponent.

Thus the natural-number comb below is exactly Deninger's
`Σ_p log p Σ_{k≥1} δ_{k log p}`, with no extra nonzero atoms.
-/
theorem existsUnique_eulerPrimePowerIndex_of_weight_ne_zero
    (n : DeningerPrimePowerIndex)
    (hn : deningerPrimePowerWeight n ≠ 0) :
    ∃! pk : Nat.Primes × ℕ,
      deningerEulerPrimePowerIndex pk = n := by
  have hpow : IsPrimePow (n : ℕ) :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn
  let pk : Nat.Primes × ℕ :=
    Nat.Primes.prodNatEquiv.symm ⟨(n : ℕ), hpow⟩
  have hval :
      ((Nat.Primes.prodNatEquiv pk).val : ℕ) = (n : ℕ) :=
    congrArg Subtype.val
      (Nat.Primes.prodNatEquiv.apply_symm_apply
        ⟨(n : ℕ), hpow⟩)
  have hpk : deningerEulerPrimePowerIndex pk = n := by
    apply Subtype.ext
    simpa [pk, deningerEulerPrimePowerIndex,
      Nat.Primes.prodNatEquiv_apply] using hval
  refine ⟨pk, hpk, ?_⟩
  intro other hother
  exact deningerEulerPrimePowerIndex_injective
    (hother.trans hpk.symm)

/-- Prime-power indices whose time lies in a fixed compact set. -/
def deningerPrimeActiveSet (K : Compacts ℝ) :
    Set DeningerPrimePowerIndex :=
  {n | deningerPrimePowerTime n ∈ (K : Set ℝ)}

/--
Only finitely many positive-integer logarithms meet a compact time set.

This is the local-finiteness mechanism behind the prime-power Dirac comb; it uses no estimate on
primes and no spectral information.
-/
theorem deningerPrimeActiveSet_finite (K : Compacts ℝ) :
    (deningerPrimeActiveSet K).Finite := by
  rcases K.isCompact.bddAbove with ⟨B, hB⟩
  let N : ℕ := ⌈Real.exp B⌉₊
  refine ((Set.finite_Iic N).preimage
    (Set.injOn_of_injective Subtype.val_injective)).subset ?_
  intro n hn
  change (n : ℕ) ≤ N
  have hlog :
      Real.log ((n : ℕ) : ℝ) ≤ B :=
    hB hn
  have hnposNat : 0 < (n : ℕ) :=
    lt_of_lt_of_le Nat.zero_lt_two n.property
  have hnposReal : 0 < ((n : ℕ) : ℝ) := by
    exact_mod_cast hnposNat
  have hnexp : ((n : ℕ) : ℝ) ≤ Real.exp B := by
    rw [← Real.exp_log hnposReal]
    exact Real.exp_le_exp.mpr hlog
  have hnceil :
      ((n : ℕ) : ℝ) ≤ (N : ℝ) :=
    hnexp.trans (Nat.le_ceil (Real.exp B))
  exact_mod_cast hnceil

/-- Finite active prime-power index set on a compact time set. -/
noncomputable def deningerPrimeActiveFinset (K : Compacts ℝ) :
    Finset DeningerPrimePowerIndex :=
  (deningerPrimeActiveSet_finite K).toFinset

@[simp]
theorem mem_deningerPrimeActiveFinset
    (K : Compacts ℝ) (n : DeningerPrimePowerIndex) :
    n ∈ deningerPrimeActiveFinset K ↔
      deningerPrimePowerTime n ∈ (K : Set ℝ) := by
  simp [deningerPrimeActiveFinset, deningerPrimeActiveSet]

/-- Evaluation on a fixed-support smooth function, bundled continuously. -/
noncomputable def deningerSupportedTimeEval
    (K : Compacts ℝ) (t : ℝ) :
    𝓓_{K}(ℝ, ℝ) →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ t).comp
    (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ)

@[simp]
theorem deningerSupportedTimeEval_apply
    (K : Compacts ℝ) (t : ℝ) (φ : 𝓓_{K}(ℝ, ℝ)) :
    deningerSupportedTimeEval K t φ = φ t :=
  rfl

/-- Finite prime-power functional on functions supported in `K`. -/
noncomputable def deningerPrimeLocalCLM
    (K : Compacts ℝ) :
    𝓓_{K}(ℝ, ℝ) →L[ℝ] ℂ :=
  ∑ n ∈ deningerPrimeActiveFinset K,
    deningerPrimePowerWeight n •
      Complex.ofRealCLM.comp
        (deningerSupportedTimeEval K
          (deningerPrimePowerTime n))

theorem deningerPrimeLocalCLM_apply
    (K : Compacts ℝ) (φ : 𝓓_{K}(ℝ, ℝ)) :
    deningerPrimeLocalCLM K φ =
      ∑ n ∈ deningerPrimeActiveFinset K,
        (deningerPrimePowerWeight n : ℂ) *
          (φ (deningerPrimePowerTime n) : ℂ) := by
  simp [deningerPrimeLocalCLM, deningerPrimePowerWeight,
    deningerSupportedTimeEval]

/-- Algebraic action of the locally finite von-Mangoldt Dirac comb. -/
def deningerPrimeLefschetzFunctional
    (φ : DeningerTimeTestFunction) : ℂ :=
  ∑' n : DeningerPrimePowerIndex,
    (deningerPrimePowerWeight n : ℂ) *
      (φ (deningerPrimePowerTime n) : ℂ)

theorem deningerPrimeLefschetzFunctional_ofSupportedIn
    (K : Compacts ℝ)
    (K_sub : (K : Set ℝ) ⊆ (deningerTimeDomain : Set ℝ))
    (φ : 𝓓_{K}(ℝ, ℝ)) :
    deningerPrimeLefschetzFunctional
        (TestFunction.ofSupportedIn K_sub φ) =
      deningerPrimeLocalCLM K φ := by
  rw [deningerPrimeLefschetzFunctional,
    tsum_eq_sum (s := deningerPrimeActiveFinset K)]
  · simpa using (deningerPrimeLocalCLM_apply K φ).symm
  · intro n hn
    have htime :
        deningerPrimePowerTime n ∉ (K : Set ℝ) := by
      simpa using hn
    have hzero :
        φ (deningerPrimePowerTime n) = 0 :=
      φ.zero_on_compl htime
    simp [hzero]

/--
Independent finite-place Lefschetz distribution

`Σ_{n≥2} Λ(n) δ_{log n}`.

Compact support makes the action a finite sum on every fixed-support Fréchet stage, so
`TestFunction.limitCLM` supplies continuity on the LF test-function space.
-/
noncomputable def deningerPrimeLefschetzDistribution :
    DeningerTimeDistribution :=
  TestFunction.limitCLM ℝ
    deningerPrimeLefschetzFunctional
    (fun K _K_sub => deningerPrimeLocalCLM K)
    deningerPrimeLefschetzFunctional_ofSupportedIn

@[simp]
theorem deningerPrimeLefschetzDistribution_apply
    (φ : DeningerTimeTestFunction) :
    deningerPrimeLefschetzDistribution φ =
      ∑' n : DeningerPrimePowerIndex,
        (deningerPrimePowerWeight n : ℂ) *
          (φ (deningerPrimePowerTime n) : ℂ) :=
  by
    rw [deningerPrimeLefschetzDistribution]
    change
      (TestFunction.limitCLM ℝ
        deningerPrimeLefschetzFunctional
        (fun K _K_sub => deningerPrimeLocalCLM K)
        deningerPrimeLefschetzFunctional_ofSupportedIn) φ =
          deningerPrimeLefschetzFunctional φ
    exact TestFunction.limitCLM_apply ℝ
      deningerPrimeLefschetzFunctional
      (fun K _K_sub => deningerPrimeLocalCLM K)
      deningerPrimeLefschetzFunctional_ofSupportedIn φ

/-- Complete independently constructed prime-plus-archimedean local trace distribution. -/
noncomputable def deningerPrimeArchimedeanLefschetzDistribution :
    DeningerTimeDistribution :=
  deningerPrimeLefschetzDistribution +
    deningerArchimedeanLefschetzDistribution

@[simp]
theorem deningerTimeTestLaplace_zero
    (φ : DeningerTimeTestFunction) :
    deningerTimeTestLaplace φ 0 =
      ∫ t : ℝ, (φ t : ℂ) := by
  simp [deningerTimeTestLaplace]

@[simp]
theorem deningerTimeTestLaplace_one
    (φ : DeningerTimeTestFunction) :
    deningerTimeTestLaplace φ 1 =
      ∫ t : ℝ, (φ t : ℂ) *
        Complex.exp (t : ℂ) := by
  apply integral_congr_ae
  filter_upwards with t
  simp

/--
Exact scalar form of the cohomological side: endpoint amplitudes minus the complete `H¹`
spectrum.  This is the left side of Deninger's Proposition 3.2 for every positive-time test.
-/
theorem deningerArithmeticAlternatingTraceDistribution_apply
    (φ : DeningerTimeTestFunction) :
    deningerArithmeticAlternatingTraceDistribution φ =
      deningerTimeTestLaplace φ 0 -
        (∑' q : XiZeroCopy,
          deningerTimeTestLaplace φ
            (deningerRawThetaEigen q)) +
          deningerTimeTestLaplace φ 1 := by
  change
    deningerArithmeticH0TraceDistribution φ -
        deningerArithmeticH1TraceDistribution φ +
      deningerArithmeticH2TraceDistribution φ = _
  rw [deningerArithmeticH0TraceDistribution_apply,
    deningerArithmeticH1TraceDistribution_apply_eq_spectralSum,
    deningerArithmeticH2TraceDistribution_apply,
    deningerTimeTestLaplace_zero,
    deningerTimeTestLaplace_one]

/--
Exact scalar form of the independently constructed prime-plus-archimedean source distribution.
-/
theorem deningerPrimeArchimedeanLefschetzDistribution_apply
    (φ : DeningerTimeTestFunction) :
    deningerPrimeArchimedeanLefschetzDistribution φ =
      (∑' n : DeningerPrimePowerIndex,
        (deningerPrimePowerWeight n : ℂ) *
          (φ (deningerPrimePowerTime n) : ℂ)) +
        ∫ t : ℝ, (φ t : ℂ) *
          deningerArchimedeanLefschetzDensity t := by
  change
    deningerPrimeLefschetzDistribution φ +
      deningerArchimedeanLefschetzDistribution φ = _
  rw [deningerPrimeLefschetzDistribution_apply,
    deningerArchimedeanLefschetzDistribution_apply]

/--
Scalar Deninger explicit formula for arbitrary smooth compactly supported positive-time tests.

This proposition is the precise remaining analytic content of the distributional Lefschetz law;
it contains no cohomology placeholders and no special test-family restriction.
-/
def DeningerArithmeticScalarExplicitFormula : Prop :=
  ∀ φ : DeningerTimeTestFunction,
    deningerTimeTestLaplace φ 0 -
        (∑' q : XiZeroCopy,
          deningerTimeTestLaplace φ
            (deningerRawThetaEigen q)) +
      deningerTimeTestLaplace φ 1 =
        (∑' n : DeningerPrimePowerIndex,
          (deningerPrimePowerWeight n : ℂ) *
            (φ (deningerPrimePowerTime n) : ℂ)) +
          ∫ t : ℝ, (φ t : ℂ) *
            deningerArchimedeanLefschetzDensity t

/--
The full distributional Lefschetz equality is equivalent to the single scalar explicit-formula
proposition above.  Thus no topological or convergence gap remains between a proof of the scalar
identity and equality in `𝓓'((0,∞),ℂ)`.
-/
theorem deningerArithmeticDistributionalLefschetz_iff_scalarExplicitFormula :
    deningerArithmeticAlternatingTraceDistribution =
        deningerPrimeArchimedeanLefschetzDistribution ↔
      DeningerArithmeticScalarExplicitFormula := by
  constructor
  · intro h φ
    have happ :=
      congrArg
        (fun T : DeningerTimeDistribution => T φ) h
    change
      deningerArithmeticAlternatingTraceDistribution φ =
        deningerPrimeArchimedeanLefschetzDistribution φ at happ
    rw [deningerArithmeticAlternatingTraceDistribution_apply,
      deningerPrimeArchimedeanLefschetzDistribution_apply] at happ
    exact happ
  · intro h
    ext φ
    rw [deningerArithmeticAlternatingTraceDistribution_apply,
      deningerPrimeArchimedeanLefschetzDistribution_apply]
    exact h φ

end

end RHTower
