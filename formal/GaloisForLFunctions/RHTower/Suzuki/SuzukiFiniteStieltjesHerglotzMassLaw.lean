import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanStieltjesFlux

/-!
# Suzuki finite-Stieltjes Herglotz mass law

For a finite negative-Stieltjes realization of the two source jets, Herglotz positivity of the
affine-sewn exterior Weyl quotient forces an exact chord-mass budget.  The same theorem records
the corresponding residue split and strict central source-flux sign.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **Finite-Stieltjes Herglotz mass law.**  A Herglotz affine-sewn exterior with finite
negative-Stieltjes normalized source jets must fill the exact gap between its edge constant and
the Xi central logarithmic curvature. -/
theorem suzukiFiniteNegativeStieltjesHerglotz_massLaw
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
    (hHerglotz : ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta)
        WAlpha WBeta rightAlpha rightBeta z).im) :
    let spectralMass :=
      ∑ i ∈ s, weight i * suzukiStieltjesChordKernel (node i) alpha beta
    Tendsto
        (fun z : ℂ => z *
          suzukiAffineSewnExteriorWeylQuotient
            (suzukiOneSidedCenteredShiftParameter alpha)
            (suzukiOneSidedCenteredShiftParameter beta)
            WAlpha WBeta rightAlpha rightBeta z)
        (𝓝[≠] 0)
        (𝓝 (-(deriv (deriv XiC) 0 / XiC 0) + ((edge - spectralMass : ℝ) : ℂ))) ∧
      suzukiAffineSewnCentralSourceFlux
          (suzukiOneSidedCenteredShiftParameter alpha)
          (suzukiOneSidedCenteredShiftParameter beta)
          a b (rightAlpha 0) (rightBeta 0) = ((edge - spectralMass : ℝ) : ℂ) ∧
      edge - spectralMass ≤ (deriv (deriv XiC) 0 / XiC 0).re ∧
      edge - (deriv (deriv XiC) 0 / XiC 0).re ≤ spectralMass ∧
      edge - spectralMass < 0 := by
  dsimp only
  have habCentered :
      suzukiOneSidedCenteredShiftParameter alpha ≠
        suzukiOneSidedCenteredShiftParameter beta :=
    suzukiOneSidedCenteredShiftParameter_injective.ne hab
  have hflux :
      suzukiAffineSewnCentralSourceFlux
          (suzukiOneSidedCenteredShiftParameter alpha)
          (suzukiOneSidedCenteredShiftParameter beta)
          a b (rightAlpha 0) (rightBeta 0) =
        ((edge - ∑ i ∈ s,
          weight i * suzukiStieltjesChordKernel (node i) alpha beta : ℝ) : ℂ) := by
    rw [hRightAlpha0, hRightBeta0]
    exact suzukiWeylNormalizedCentralSourceFlux_finiteNegativeStieltjes_eq
      hab ha hb hnodeAlpha hnodeBeta
  have hresidue := tendsto_z_mul_suzukiAffineSewnExteriorWeylQuotient
    hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hRightAlpha hRightBeta habCentered
  rw [hflux] at hresidue
  have hfluxLe :=
    suzukiAffineSewnCentralSourceFlux_re_le_XiC_curvature_of_herglotz
      hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hRightAlpha hRightBeta
      habCentered hHerglotz
  rw [hflux] at hfluxLe
  simp only [ofReal_re] at hfluxLe
  refine ⟨hresidue, hflux, hfluxLe, ?_, ?_⟩
  · linarith
  · exact lt_of_le_of_lt hfluxLe XiC_secondDeriv_div_center_re_neg

end

end RHTower
