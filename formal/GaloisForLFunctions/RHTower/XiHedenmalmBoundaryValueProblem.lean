import GaloisForLFunctions.RHTower.ThetaCuspInversionBoundaryValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Hedenmalm's explicit theta boundary-value problem

This module formalizes the boundary-value theorem from Hedenmalm's 2026 spectral interpretation
of the Riemann zeta zeros (`arXiv:2606.17494`) in logarithmic coordinates.  The source amplitude is
normalized to one.  The explicit theta integral solves the first-order equation, the weighted left
endpoint condition makes that solution unique, and the weighted right endpoint condition is
equivalent to `XiC alpha = 0`.

The result is an exact spectral reformulation.  It does not make the spectral parameter real.  The
research wall remains the construction of a positive Hilbert-space form and a genuinely
self-adjoint realization of the operator pencil.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Hedenmalm's explicit boundary eigenfunction in logarithmic coordinates. -/
def xiHedenmalmBoundaryEigenfunction (alpha : ℂ) (x : ℝ) : ℂ :=
  thetaCuspBoundaryPrimitive (-alpha) x

/-- The boundary eigenfunction after removal of its exact exponential norm gauge. -/
def xiHedenmalmBoundaryGauge (alpha : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-alpha.im * x) : ℂ) * xiHedenmalmBoundaryEigenfunction alpha x

/-- The same weighted endpoint gauge for an arbitrary candidate boundary solution. -/
def xiHedenmalmWeightedBoundaryGauge (alpha : ℂ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-alpha.im * x) : ℂ) * u x

/-- The logarithmic first-order boundary equation isolated from Hedenmalm's operator pencil. -/
def XiHedenmalmBoundaryEquation (alpha : ℂ) (u : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, HasDerivAt u
    (-I * alpha * u x + (thetaCuspFullSource x : ℂ)) x

/-- The gauged eigenfunction has exactly the norm of the left cumulative theta transform. -/
theorem norm_xiHedenmalmBoundaryGauge (alpha : ℂ) (x : ℝ) :
    ‖xiHedenmalmBoundaryGauge alpha x‖ =
      ‖∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand (-alpha) y‖ := by
  have hexpNorm :
      ‖Complex.exp (I * (-alpha) * (x : ℂ))‖ = Real.exp (alpha.im * x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [mul_re]
  rw [xiHedenmalmBoundaryGauge, xiHedenmalmBoundaryEigenfunction,
    thetaCuspBoundaryPrimitive, norm_mul, norm_mul, hexpNorm]
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [mul_assoc, ← Real.exp_add]
  have : -alpha.im * x + alpha.im * x = 0 := by ring
  rw [this, Real.exp_zero, one_mul]

/-- Differentiating the left cumulative theta transform recovers its integrand. -/
theorem hasDerivAt_thetaCuspCumulativeIntegral
    {alpha : ℂ} (hstrip : |alpha.im| < 1) (x : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        ∫ y : ℝ in Iic u, thetaCuspFourierLaplaceIntegrand (-alpha) y)
      (thetaCuspFourierLaplaceIntegrand (-alpha) x) x := by
  have hstripNeg : |(-alpha).im| < 1 := by simpa using hstrip
  have hint : Integrable (thetaCuspFourierLaplaceIntegrand (-alpha)) :=
    integrable_thetaCuspFourierLaplaceIntegrand hstripNeg
  have hcont : Continuous (thetaCuspFourierLaplaceIntegrand (-alpha)) := by
    unfold thetaCuspFourierLaplaceIntegrand
    fun_prop
  have hfun :
      (fun u : ℝ =>
        ∫ y : ℝ in Iic u, thetaCuspFourierLaplaceIntegrand (-alpha) y) =
      fun u : ℝ =>
        (∫ y : ℝ in Iic 0, thetaCuspFourierLaplaceIntegrand (-alpha) y) +
          ∫ y : ℝ in (0 : ℝ)..u, thetaCuspFourierLaplaceIntegrand (-alpha) y := by
    funext u
    have hdiff := intervalIntegral.integral_Iic_sub_Iic
      (f := thetaCuspFourierLaplaceIntegrand (-alpha))
      (a := (0 : ℝ)) (b := u) hint.integrableOn hint.integrableOn
    exact (eq_add_of_sub_eq hdiff).trans (add_comm _ _)
  rw [hfun]
  exact (intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 x)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt).const_add _

/-- The explicit function solves Hedenmalm's inhomogeneous first-order theta equation. -/
theorem hasDerivAt_xiHedenmalmBoundaryEigenfunction
    {alpha : ℂ} (hstrip : |alpha.im| < 1) (x : ℝ) :
    HasDerivAt (xiHedenmalmBoundaryEigenfunction alpha)
      (-I * alpha * xiHedenmalmBoundaryEigenfunction alpha x +
        (thetaCuspFullSource x : ℂ)) x := by
  let cumulative : ℝ → ℂ := fun u =>
    ∫ y : ℝ in Iic u, thetaCuspFourierLaplaceIntegrand (-alpha) y
  have hcumulative : HasDerivAt cumulative
      (thetaCuspFourierLaplaceIntegrand (-alpha) x) x := by
    simpa only [cumulative] using hasDerivAt_thetaCuspCumulativeIntegral hstrip x
  have hexp : HasDerivAt
      (fun u : ℝ => Complex.exp (I * (-alpha) * (u : ℂ)))
      (Complex.exp (I * (-alpha) * (x : ℂ)) * (I * (-alpha))) x := by
    fun_prop
  have hprod := hexp.mul hcumulative
  rw [xiHedenmalmBoundaryEigenfunction, thetaCuspBoundaryPrimitive]
  change HasDerivAt (fun u : ℝ =>
      Complex.exp (I * -alpha * (u : ℂ)) * cumulative u) _ x
  convert hprod using 1
  rw [thetaCuspFourierLaplaceIntegrand]
  have hexpCancel :
      Complex.exp (I * -alpha * (x : ℂ)) *
          Complex.exp (-I * -alpha * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero
    ring
  rw [hexpCancel, one_mul]
  ring

/-- The explicit theta integral is a solution of the logarithmic Hedenmalm equation. -/
theorem xiHedenmalmBoundaryEigenfunction_satisfies_equation
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    XiHedenmalmBoundaryEquation alpha
      (xiHedenmalmBoundaryEigenfunction alpha) := by
  intro x
  exact hasDerivAt_xiHedenmalmBoundaryEigenfunction hstrip x

/-- The cumulative Fourier--Laplace integral tends to the completed Xi value at the right end. -/
theorem tendsto_thetaCuspCumulativeIntegral_atTop
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    Tendsto
      (fun x : ℝ =>
        ∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand (-alpha) y)
      atTop (𝓝 (XiC alpha)) := by
  have hstripNeg : |(-alpha).im| < 1 := by simpa using hstrip
  have hint : Integrable (thetaCuspFourierLaplaceIntegrand (-alpha)) :=
    integrable_thetaCuspFourierLaplaceIntegrand hstripNeg
  have htail :
      Tendsto
        (fun x : ℝ =>
          ∫ y : ℝ in Ioi x, thetaCuspFourierLaplaceIntegrand (-alpha) y)
        atTop (𝓝 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
  have htotal :
      (∫ y : ℝ, thetaCuspFourierLaplaceIntegrand (-alpha) y) = XiC alpha := by
    have hmem : -alpha ∈ thetaCuspFourierLaplaceStrip := by
      rw [thetaCuspFourierLaplaceStrip]
      exact abs_lt.mp hstripNeg
    rw [← thetaCuspFourierLaplace,
      thetaCuspFourierLaplace_eq_XiC_on_strip hmem, XiC_even]
  have hsub :
      Tendsto
        (fun x : ℝ =>
          (∫ y : ℝ, thetaCuspFourierLaplaceIntegrand (-alpha) y) -
            ∫ y : ℝ in Ioi x, thetaCuspFourierLaplaceIntegrand (-alpha) y)
        atTop
        (𝓝 ((∫ y : ℝ, thetaCuspFourierLaplaceIntegrand (-alpha) y) - 0)) :=
    Tendsto.const_sub _ htail
  have hcum :
      Tendsto
        (fun x : ℝ =>
          ∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand (-alpha) y)
        atTop
        (𝓝 (∫ y : ℝ, thetaCuspFourierLaplaceIntegrand (-alpha) y)) := by
    convert hsub using 1
    · funext x
      have hsplit := integral_add_compl
        (f := thetaCuspFourierLaplaceIntegrand (-alpha))
        (s := Iic x) measurableSet_Iic hint
      simpa only [compl_Iic] using (eq_sub_of_add_eq hsplit)
    · simp
  simpa [htotal] using hcum

/-- Hedenmalm's weighted boundary condition at zero is automatic in the natural strip. -/
theorem tendsto_xiHedenmalmBoundaryGauge_atBot
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    Tendsto (xiHedenmalmBoundaryGauge alpha) atBot (𝓝 0) := by
  have hcum :
      Tendsto
        (fun x : ℝ =>
          ∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand (-alpha) y)
        atBot (𝓝 0) :=
    MeasureTheory.tendsto_integral_Iic_zero tendsto_id
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_xiHedenmalmBoundaryGauge, norm_zero] using hcum.norm

/-- A solution of Hedenmalm's first-order equation with the weighted left boundary condition is
the explicit theta integral.  This is the uniqueness half of the boundary-value theorem. -/
theorem xiHedenmalmBoundaryEquation_unique_of_atBot
    {alpha : ℂ} (hstrip : |alpha.im| < 1) {u : ℝ → ℂ}
    (hu : XiHedenmalmBoundaryEquation alpha u)
    (huBot : Tendsto (xiHedenmalmWeightedBoundaryGauge alpha u) atBot (𝓝 0)) :
    u = xiHedenmalmBoundaryEigenfunction alpha := by
  let q : ℝ → ℂ := fun x =>
    Complex.exp (I * alpha * (x : ℂ)) *
      (u x - xiHedenmalmBoundaryEigenfunction alpha x)
  have hqDeriv (x : ℝ) : HasDerivAt q 0 x := by
    have hexp : HasDerivAt
        (fun y : ℝ => Complex.exp (I * alpha * (y : ℂ)))
        (Complex.exp (I * alpha * (x : ℂ)) * (I * alpha)) x := by
      fun_prop
    have hdiff := (hu x).sub
      (hasDerivAt_xiHedenmalmBoundaryEigenfunction hstrip x)
    have hprod := hexp.mul hdiff
    change HasDerivAt
      (fun y : ℝ => Complex.exp (I * alpha * (y : ℂ)) *
        (u y - xiHedenmalmBoundaryEigenfunction alpha y)) 0 x
    convert hprod using 1 <;> ring
  have hqDiff : Differentiable ℝ q := fun x => (hqDeriv x).differentiableAt
  have hqConst (x : ℝ) : q x = q 0 :=
    is_const_of_deriv_eq_zero hqDiff (fun y => (hqDeriv y).deriv) x 0
  have hExplicitBot :
      Tendsto
        (xiHedenmalmWeightedBoundaryGauge alpha
          (xiHedenmalmBoundaryEigenfunction alpha)) atBot (𝓝 0) := by
    simpa only [xiHedenmalmWeightedBoundaryGauge, xiHedenmalmBoundaryGauge] using
      tendsto_xiHedenmalmBoundaryGauge_atBot hstrip
  have hdiffBot :
      Tendsto
        (fun x : ℝ =>
          xiHedenmalmWeightedBoundaryGauge alpha u x -
            xiHedenmalmWeightedBoundaryGauge alpha
              (xiHedenmalmBoundaryEigenfunction alpha) x)
        atBot (𝓝 0) := by
    simpa only [sub_zero] using huBot.sub hExplicitBot
  have hnormQ : Tendsto (fun x : ℝ => ‖q x‖) atBot (𝓝 0) := by
    have hnormDiff := hdiffBot.norm
    simpa only [norm_zero] using hnormDiff.congr' (Filter.Eventually.of_forall fun x => by
      rw [q, xiHedenmalmWeightedBoundaryGauge, ← mul_sub, norm_mul,
        Complex.norm_exp, norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      congr 2
      simp [mul_re])
  have hnormConst : Tendsto (fun _ : ℝ => ‖q 0‖) atBot (𝓝 ‖q 0‖) :=
    tendsto_const_nhds
  have hnormQ0 : ‖q 0‖ = 0 := by
    apply tendsto_nhds_unique hnormConst
    exact hnormQ.congr' (Filter.Eventually.of_forall fun x => by rw [hqConst])
  have hq0 : q 0 = 0 := norm_eq_zero.mp hnormQ0
  funext x
  have hqx : q x = 0 := (hqConst x).trans hq0
  rw [q, mul_eq_zero] at hqx
  exact sub_eq_zero.mp (hqx.resolve_left (Complex.exp_ne_zero _))

/-- Hedenmalm's weighted boundary condition at infinity holds exactly at completed Xi zeros. -/
theorem tendsto_xiHedenmalmBoundaryGauge_atTop_iff
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    Tendsto (xiHedenmalmBoundaryGauge alpha) atTop (𝓝 0) ↔
      XiC alpha = 0 := by
  have hcum := tendsto_thetaCuspCumulativeIntegral_atTop hstrip
  constructor
  · intro hgauge
    have hnormZero :
        Tendsto
          (fun x : ℝ =>
            ‖∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand (-alpha) y‖)
          atTop (𝓝 0) := by
      have hnormGauge := hgauge.norm
      simpa only [norm_xiHedenmalmBoundaryGauge, norm_zero] using hnormGauge
    have hnormXi := hcum.norm
    have : ‖XiC alpha‖ = 0 := tendsto_nhds_unique hnormXi hnormZero
    exact norm_eq_zero.mp this
  · intro hzero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hcumZero :
        Tendsto
          (fun x : ℝ =>
            ∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand (-alpha) y)
          atTop (𝓝 0) := by
      simpa only [hzero] using hcum
    simpa only [norm_xiHedenmalmBoundaryGauge, norm_zero] using hcumZero.norm

/-- The normalized Hedenmalm boundary-value problem: the source amplitude is fixed to one, and
the weighted solution vanishes at both logarithmic ends. -/
def XiHedenmalmNormalizedBoundaryValueProblem (alpha : ℂ) (u : ℝ → ℂ) : Prop :=
  XiHedenmalmBoundaryEquation alpha u ∧
    Tendsto (xiHedenmalmWeightedBoundaryGauge alpha u) atBot (𝓝 0) ∧
    Tendsto (xiHedenmalmWeightedBoundaryGauge alpha u) atTop (𝓝 0)

/-- **Hedenmalm's normalized boundary-value theorem.**  In the Fourier--Laplace strip relevant to
nontrivial zeta zeros, the normalized problem has a unique solution exactly when the completed Xi
function vanishes.  The unique solution is the explicit theta boundary integral. -/
theorem existsUnique_xiHedenmalmNormalizedBoundaryValueProblem_iff
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    (∃! u : ℝ → ℂ, XiHedenmalmNormalizedBoundaryValueProblem alpha u) ↔
      XiC alpha = 0 := by
  constructor
  · rintro ⟨u, hu, -⟩
    have huEq := xiHedenmalmBoundaryEquation_unique_of_atBot
      hstrip hu.1 hu.2.1
    have htop :
        Tendsto (xiHedenmalmBoundaryGauge alpha) atTop (𝓝 0) := by
      simpa only [huEq, xiHedenmalmWeightedBoundaryGauge,
        xiHedenmalmBoundaryGauge] using hu.2.2
    exact (tendsto_xiHedenmalmBoundaryGauge_atTop_iff hstrip).mp htop
  · intro hzero
    refine ⟨xiHedenmalmBoundaryEigenfunction alpha, ?_, ?_⟩
    · refine ⟨xiHedenmalmBoundaryEigenfunction_satisfies_equation hstrip, ?_, ?_⟩
      · simpa only [xiHedenmalmWeightedBoundaryGauge,
          xiHedenmalmBoundaryGauge] using
          tendsto_xiHedenmalmBoundaryGauge_atBot hstrip
      · simpa only [xiHedenmalmWeightedBoundaryGauge,
          xiHedenmalmBoundaryGauge] using
          (tendsto_xiHedenmalmBoundaryGauge_atTop_iff hstrip).mpr hzero
    · intro u hu
      exact xiHedenmalmBoundaryEquation_unique_of_atBot
        hstrip hu.1 hu.2.1

/-- The explicit logarithmic eigenfunction satisfies both weighted endpoint conditions exactly
when its spectral parameter is a completed Xi zero. -/
theorem xiHedenmalmBoundaryGauge_twoEnded_iff_XiC_eq_zero
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    (Tendsto (xiHedenmalmBoundaryGauge alpha) atBot (𝓝 0) ∧
        Tendsto (xiHedenmalmBoundaryGauge alpha) atTop (𝓝 0)) ↔
      XiC alpha = 0 := by
  rw [and_iff_right (tendsto_xiHedenmalmBoundaryGauge_atBot hstrip),
    tendsto_xiHedenmalmBoundaryGauge_atTop_iff hstrip]

end RHTower
