import Mathlib.Analysis.Complex.CauchyIntegral
import GaloisForLFunctions.RHTower.ChargeTomography
import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicGaugeCharge
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityReflection

/-!
# The literal two-sided theta completion is an analytic unit at every Xi divisor

The one-sided positive theta completion is zero-free in the upper half-plane.  Allowing the
reflected growing channel removes positivity, but the exact two-sided source identity is even
more rigid at an Xi divisor: its numerator becomes `1/2`, so the two-sided completion cannot
vanish there.  It is therefore an analytic unit and contributes zero anisotropic divisor charge.

This closes the literal signed two-sided theta completion as a moving-gauge survivor.  It does
not address arbitrary signed source laws which are not the canonical reflected theta density.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Canonical two-sided theta-density completion. -/
def thetaCuspTailTwoSidedPhaseValue (z : ℂ) : ℂ :=
  thetaCuspTailSecondDensityPhaseValue z +
    thetaCuspTailSecondDensityPhaseValue (-z)

/-- Spectral derivative of the canonical two-sided theta-density completion. -/
def thetaCuspTailTwoSidedPhaseDerivative (z : ℂ) : ℂ :=
  thetaCuspTailSecondDensityPhaseDerivative z -
    thetaCuspTailSecondDensityPhaseDerivative (-z)

theorem hasDerivAt_thetaCuspTailTwoSidedPhaseValue
    {z : ℂ} (hz : |z.im| < 1) :
    HasDerivAt thetaCuspTailTwoSidedPhaseValue
      (thetaCuspTailTwoSidedPhaseDerivative z) z := by
  have hzBounds := abs_lt.mp hz
  have hplus :=
    hasDerivAt_thetaCuspTailSecondDensityPhaseValue
      (z₀ := z) hzBounds.1
  have hminusBase :=
    hasDerivAt_thetaCuspTailSecondDensityPhaseValue
      (z₀ := -z) (by
        simp only [neg_im]
        linarith)
  have hminus := hminusBase.comp z (hasDerivAt_id z).neg
  have hfun :
      thetaCuspTailTwoSidedPhaseValue =
        thetaCuspTailSecondDensityPhaseValue +
          thetaCuspTailSecondDensityPhaseValue ∘ Neg.neg := by
    funext w
    rfl
  have hder :
      thetaCuspTailTwoSidedPhaseDerivative z =
        thetaCuspTailSecondDensityPhaseDerivative z +
          thetaCuspTailSecondDensityPhaseDerivative (-z) * -1 := by
    simp only [thetaCuspTailTwoSidedPhaseDerivative]
    ring
  rw [hfun, hder]
  exact hplus.add hminus

/-- The two-sided completion is analytic throughout the open theta Fourier--Laplace strip. -/
theorem analyticAt_thetaCuspTailTwoSidedPhaseValue
    {z : ℂ} (hz : |z.im| < 1) :
    AnalyticAt ℂ thetaCuspTailTwoSidedPhaseValue z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hzmem : z ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    exact abs_lt.mp hz
  filter_upwards
    [isOpen_thetaCuspFourierLaplaceStrip.mem_nhds hzmem] with w hw
  apply (hasDerivAt_thetaCuspTailTwoSidedPhaseValue
    (z := w) ?_).differentiableAt
  rw [thetaCuspFourierLaplaceStrip] at hw
  exact abs_lt.mpr hw

/-- At an Xi divisor, the exact two-sided source relation has numerator `1/2`; hence the
canonical two-sided completion is nonzero without a positivity argument. -/
theorem thetaCuspTailTwoSidedPhaseValue_ne_zero_of_XiC_eq_zero
    {z : ℂ} (hz : |z.im| < 1) (hXi : XiC z = 0) :
    thetaCuspTailTwoSidedPhaseValue z ≠ 0 := by
  have hcross :=
    thetaCuspTailSecondDensityPhaseValue_twoSided_crossed hz
  change (z ^ 2 + 1 / 4) * thetaCuspTailTwoSidedPhaseValue z =
    1 / 2 + 4 * z ^ 2 * XiC z at hcross
  rw [hXi, mul_zero, add_zero] at hcross
  intro hzero
  rw [hzero, mul_zero] at hcross
  norm_num at hcross

theorem xiCTaylorCenteredPoint_mem_thetaCuspFourierLaplaceStrip
    {sigma : ℂ} (hsigma0 : 0 < sigma.re) (hsigma1 : sigma.re < 1) :
    |(xiCTaylorCenteredPoint sigma).im| < 1 := by
  have him :
      (xiCTaylorCenteredPoint sigma).im = 1 / 2 - sigma.re := by
    rw [xiCTaylorCenteredPoint, mul_im]
    norm_num
  rw [him, abs_lt]
  constructor <;> linarith

/-- The literal two-sided theta completion preserves the full finite Taylor divisor charge. -/
theorem xiCTaylor_twoSidedThetaGaugeTransferCharge_tendsto
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {sigma : ℂ} (hsigma0 : 0 < sigma.re) (hsigma1 : sigma.re < 1)
    (hXi : xi sigma = 0) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          ((logDeriv
              (xiCTaylorApprox
                (N (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
            (logDeriv thetaCuspTailTwoSidedPhaseValue
              (xiCTaylorAnisotropicCenteredPoint sigma n)).im))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  have hzstrip :=
    xiCTaylorCenteredPoint_mem_thetaCuspFourierLaplaceStrip
      hsigma0 hsigma1
  have hXiCentered :
      XiC (xiCTaylorCenteredPoint sigma) = 0 := by
    simpa only [XiC_xiCTaylorCenteredPoint] using hXi
  exact xiCTaylor_analyticUnitGaugeTransferCharge_tendsto hN
    thetaCuspTailTwoSidedPhaseValue sigma
    (analyticAt_thetaCuspTailTwoSidedPhaseValue hzstrip)
    (thetaCuspTailTwoSidedPhaseValue_ne_zero_of_XiC_eq_zero
      hzstrip hXiCentered)

/-- A nonzero Xi divisor cannot be screened by the literal two-sided theta completion. -/
theorem not_xiCTaylor_twoSidedThetaGaugeChargeScreenedAt
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {sigma : ℂ} (hsigma0 : 0 < sigma.re) (hsigma1 : sigma.re < 1)
    (hXi : xi sigma = 0) :
    ¬ XiCTaylorMeromorphicGaugeChargeScreenedAt
      N thetaCuspTailTwoSidedPhaseValue sigma := by
  have hzstrip :=
    xiCTaylorCenteredPoint_mem_thetaCuspFourierLaplaceStrip
      hsigma0 hsigma1
  have hXiCentered :
      XiC (xiCTaylorCenteredPoint sigma) = 0 := by
    simpa only [XiC_xiCTaylorCenteredPoint] using hXi
  have hA :=
    analyticAt_thetaCuspTailTwoSidedPhaseValue hzstrip
  have hA0 :=
    thetaCuspTailTwoSidedPhaseValue_ne_zero_of_XiC_eq_zero
      hzstrip hXiCentered
  have horder :
      meromorphicOrderAt thetaCuspTailTwoSidedPhaseValue
        (xiCTaylorCenteredPoint sigma) = (0 : ℤ) := by
    rw [hA.meromorphicOrderAt_eq,
      hA.analyticOrderAt_eq_zero.mpr hA0]
    rfl
  have hclass :=
    xiCTaylor_meromorphicGaugeChargeScreenedAt_iff_order_eq
      hN thetaCuspTailTwoSidedPhaseValue sigma 0
      hA.meromorphicAt horder
  intro hscreen
  have hzeroInt := hclass.mp hscreen
  have hzeroNat : (analyticOrderAt xi sigma).toNat = 0 := by
    exact_mod_cast hzeroInt.symm
  have hxiNe := (xi_orderToNat_eq_zero_iff sigma).mp hzeroNat
  exact hxiNe hXi

end

end RHTower
