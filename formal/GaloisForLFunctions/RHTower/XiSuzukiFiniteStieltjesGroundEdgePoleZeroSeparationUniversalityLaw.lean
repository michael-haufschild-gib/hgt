import GaloisForLFunctions.RHTower.SuzukiFiniteStieltjesGroundEdgeExclusionUniversalityLaw
import GaloisForLFunctions.RHTower.XiSuzukiPoleZeroNormalFormUniversalityLaw

/-!
# Xi--Suzuki finite-Stieltjes ground-edge pole/zero separation

The same affine-sewn Suzuki exterior can have a universal source-independent pole/zero normal
form at every Xi zero while failing the Herglotz half-plane condition at the central finite
negative-Stieltjes chart.  The separation is forced when the central chord mass is identified
with a positive ground edge above the half-curvature floor.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Xi--Suzuki finite-Stieltjes ground-edge pole/zero separation law.**  At an arbitrary Xi
zero, the centered affine-sewn exterior belongs to the universal order/coefficient normal form.
For the same exterior functions, identifying its finite negative-Stieltjes central flux with a
positive ground edge above the half-curvature floor makes a global Herglotz presentation
impossible. -/
theorem xiSuzuki_finiteStieltjesGroundEdgePoleZeroSeparationUniversality
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta edge slope moment mass : ℝ}
    {eta gamma z a b : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta rightAlpha rightBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hz : XiC z = 0)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hWAlphaCenter : WAlpha 0 = 0)
    (hWBetaCenter : WBeta 0 = 0)
    (hWAlphaZero : WAlpha z ≠ 0)
    (hWBetaZero : WBeta z ≠ 0)
    (hWAlphaDeriv : HasDerivAt WAlpha a 0)
    (hWBetaDeriv : HasDerivAt WBeta b 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hIAlpha : ∀ w, AnalyticAt ℂ intervalAlpha w)
    (hIBeta : ∀ w, AnalyticAt ℂ intervalBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w)
    (hRightAlphaCenter : rightAlpha 0 =
      ((suzukiFiniteNegativeStieltjesJet s node weight edge slope alpha : ℝ) : ℂ) * a)
    (hRightBetaCenter : rightBeta 0 =
      ((suzukiFiniteNegativeStieltjesJet s node weight edge slope beta : ℝ) : ℂ) * b)
    (hnodeAlpha : ∀ i ∈ s, alpha ≠ node i)
    (hnodeBeta : ∀ i ∈ s, beta ≠ node i)
    (hmass : 0 < mass)
    (hmoment : (deriv (deriv XiC) 0 / XiC 0).re / 2 * mass ≤ moment)
    (hidentify : suzukiGroundEdgeAverage moment mass =
      edge - ∑ i ∈ s,
        weight i * suzukiStieltjesChordKernel (node i) alpha beta) :
    XiSuzukiPoleZeroNormalFormUniversalCertificate eta
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta) gamma z
        WAlpha WBeta intervalAlpha intervalBeta rightAlpha rightBeta ∧
      ¬ ∀ w : ℂ, 0 < w.im →
        0 ≤ (suzukiAffineSewnExteriorWeylQuotient
          (suzukiOneSidedCenteredShiftParameter alpha)
          (suzukiOneSidedCenteredShiftParameter beta)
          WAlpha WBeta rightAlpha rightBeta w).im := by
  have habCentered :
      suzukiOneSidedCenteredShiftParameter alpha ≠
        suzukiOneSidedCenteredShiftParameter beta :=
    suzukiOneSidedCenteredShiftParameter_injective.ne hab
  constructor
  · exact xiZero_suzukiPoleZeroNormalFormUniversalCertificate
      habCentered hz hWAlpha hWBeta hWAlphaZero hWBetaZero
        hIAlpha hIBeta hRAlpha hRBeta
  · exact not_suzukiFiniteNegativeStieltjes_herglotz_of_groundEdgeIdentification
      hab hWAlphaDeriv hWBetaDeriv hWAlphaCenter hWBetaCenter ha hb
        (hRAlpha 0).differentiableAt (hRBeta 0).differentiableAt
        hRightAlphaCenter hRightBetaCenter hnodeAlpha hnodeBeta
        hmass hmoment hidentify

end

end RHTower
