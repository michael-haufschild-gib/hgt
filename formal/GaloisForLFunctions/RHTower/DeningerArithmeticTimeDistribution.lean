import GaloisForLFunctions.RHTower.DeningerArithmeticJetFrobenius
import GaloisForLFunctions.RHTower.XiConvergenceExponent
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Calculus.Deriv.Support
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

end

end RHTower
