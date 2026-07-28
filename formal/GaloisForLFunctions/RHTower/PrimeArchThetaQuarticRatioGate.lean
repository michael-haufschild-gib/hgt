import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.HTGeometry.CubicMomentLogConvexRatio

/-!
# A single quartic gate for the first nonconstant theta-source Hankel condition

The first nonconstant prime--Gamma source Hankel condition is equivalent to nonnegativity of the
source cubic in the raw even moments `m_j = thetaCuspRawEvenMoment j`.  Written in the variable
`y = x^2`, where the moments become `m_j = ∫₀^∞ y^(j-1/2) H(y) dy`, the natural normalization is
`L_j = m_j / Γ(j+1/2)` and the cubic becomes a second difference of the ratios
`r_j = L_j / L_(j-1) = μ_j / (j - 1/2)`.  Log-convexity of that ratio sequence therefore suffices,
and log-convexity is the single monomial inequality

`5 * m_0 * m_2^3 ≤ 9 * m_1^3 * m_3`.

This replaces the two separate sufficient ratio bounds by one.  It is an exact equality for the
Gaussian weight `Φ = e^(-x^2)` — the model at which the cubic itself is tight — and it fails for the
two-sided exponential, so it is strictly stronger than the cubic and strictly sharper at the relevant
model.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Log-convexity of the Γ-normalized moment-ratio sequence of the completed theta source. -/
def ThetaCuspQuarticRatioGate : Prop :=
  5 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 3 ≤
    9 * thetaCuspRawEvenMoment 1 ^ 3 * thetaCuspRawEvenMoment 3

/-- The quartic gate is exactly log-convexity of the normalized ratio sequence
`r_j = μ_j / (j - 1/2)`. -/
theorem thetaCuspQuarticRatioGate_iff_logConvex :
    ThetaCuspQuarticRatioGate ↔
      5 * (thetaCuspRawEvenMoment 2 / thetaCuspRawEvenMoment 1) ^ 2 ≤
        9 * (thetaCuspRawEvenMoment 1 / thetaCuspRawEvenMoment 0) *
          (thetaCuspRawEvenMoment 3 / thetaCuspRawEvenMoment 2) :=
  GaloisForLFunctions.CubicMomentLogConvexRatio.quartic_iff_logConvex
    (thetaCuspRawEvenMoment_pos 0) (thetaCuspRawEvenMoment_pos 1) (thetaCuspRawEvenMoment_pos 2)

/-- The quartic gate implies nonnegativity of the source cubic. -/
theorem thetaCusp_raw_cubic_nonneg_of_quarticRatioGate (h : ThetaCuspQuarticRatioGate) :
    0 ≤ 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 +
      15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
      10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 :=
  GaloisForLFunctions.CubicMomentLogConvexRatio.cubic_nonneg_of_quartic
    (thetaCuspRawEvenMoment_pos 0) (thetaCuspRawEvenMoment_pos 1)
    (thetaCuspRawEvenMoment_pos 2) (thetaCuspRawEvenMoment_pos 3) h

/-- **One monomial inequality discharges the first nonconstant source Hankel condition.** -/
theorem thetaCuspSixthMomentHankelInequality_of_quarticRatioGate
    (h : ThetaCuspQuarticRatioGate) : ThetaCuspSixthMomentHankelInequality :=
  thetaCusp_raw_cubic_nonneg_iff_sixthMomentHankelInequality.mp
    (thetaCusp_raw_cubic_nonneg_of_quarticRatioGate h)

/-- The same gate discharges the equivalent three-state size-biased mean balance. -/
theorem thetaCuspThreeTemperatureMeanBalance_of_quarticRatioGate
    (h : ThetaCuspQuarticRatioGate) : ThetaCuspThreeTemperatureMeanBalance :=
  thetaCuspThreeTemperatureMeanBalance_iff_sixthMomentHankelInequality.mpr
    (thetaCuspSixthMomentHankelInequality_of_quarticRatioGate h)

/-- The gate also discharges every real linear-polynomial prime--Gamma source trace Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_quarticRatioGate
    (h : ThetaCuspQuarticRatioGate) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_iff_threeTemperatureMeanBalance.mpr
    (thetaCuspThreeTemperatureMeanBalance_of_quarticRatioGate h)

end

end RHTower
