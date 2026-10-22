import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteStieltjesHerglotzMassLaw
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEdgeHerglotzObstructionLaw

/-!
# Finite-Stieltjes versus positive ground-edge Suzuki exclusion

A Herglotz affine-sewn exterior with finite negative-Stieltjes source jets forces its exact
central flux below Xi curvature.  A positive ground edge whose moment is above half Xi curvature
forces the same normalized flux strictly above Xi curvature.  Identifying the two source
descriptions is therefore impossible.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Finite-Stieltjes/ground-edge exclusion law.**  A finite negative-Stieltjes source whose
exact chord-mass flux equals a positive ground-edge average above the half-curvature floor cannot
produce a Herglotz affine-sewn exterior. -/
theorem not_suzukiFiniteNegativeStieltjes_herglotz_of_groundEdgeIdentification
    {ι : Type*} {s : Finset ι} {node weight : ι → ℝ}
    {alpha beta edge slope : ℝ} {a b : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    (hRightAlpha0 : rightAlpha 0 =
      ((suzukiFiniteNegativeStieltjesJet s node weight edge slope alpha : ℝ) : ℂ) * a)
    (hRightBeta0 : rightBeta 0 =
      ((suzukiFiniteNegativeStieltjesJet s node weight edge slope beta : ℝ) : ℂ) * b)
    (hnodeAlpha : ∀ i ∈ s, alpha ≠ node i)
    (hnodeBeta : ∀ i ∈ s, beta ≠ node i)
    {moment mass : ℝ} (hmass : 0 < mass)
    (hmoment : (deriv (deriv XiC) 0 / XiC 0).re / 2 * mass ≤ moment)
    (hidentify : suzukiGroundEdgeAverage moment mass =
      edge - ∑ i ∈ s,
        weight i * suzukiStieltjesChordKernel (node i) alpha beta) :
    ¬ ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta)
        WAlpha WBeta rightAlpha rightBeta z).im := by
  intro hHerglotz
  have hmassLaw := suzukiFiniteNegativeStieltjesHerglotz_massLaw
    hab hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hRightAlpha hRightBeta
    hRightAlpha0 hRightBeta0 hnodeAlpha hnodeBeta hHerglotz
  dsimp only at hmassLaw
  have hbelow :
      edge - ∑ i ∈ s,
          weight i * suzukiStieltjesChordKernel (node i) alpha beta ≤
        (deriv (deriv XiC) 0 / XiC 0).re :=
    hmassLaw.2.2.1
  have habove :=
    suzukiGroundEdgeAverage_gt_XiC_curvature_of_half_lowerMoment hmass hmoment
  rw [hidentify] at habove
  exact (not_lt_of_ge hbelow) habove

end

end RHTower
