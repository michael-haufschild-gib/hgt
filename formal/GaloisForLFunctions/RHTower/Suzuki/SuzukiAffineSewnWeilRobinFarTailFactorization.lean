import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalWeilRobinGreenIdentity

/-!
# Suzuki affine-sewn Weil--Robin far-tail factorization

Every source channel common after characteristic normalization factors through the complete
two-shift sewn characteristic.  Far delayed hinges are exactly such channels.  Hence affine
sewing cannot cancel a far von-Mangoldt atom: after normalization the atom is independent of both
shifts and both deficiency characteristics.  Its phase-aligned negative Pick diagonal survives
as a characteristic congruence.

This module also sews the exact causal Weil--Robin Green identities before division.  It uses no
RH premise, positivity hypothesis, estimate, computation, Xi-zero data, or nonvanishing premise
except in the final strict-sign specialization.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Universal common-channel factorization -/

/-- **Affine common-channel law.**  A scalar channel common after normalization factors through
the full sewn characteristic, for every affine target shift. -/
theorem suzukiAffineSewnIntervalPart_commonChannel_factorization
    (alpha beta gamma : ℂ) (WAlpha WBeta m : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (fun u => m u * WAlpha u) (fun u => m u * WBeta u) z =
      m z * suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z := by
  simp only [suzukiAffineSewnIntervalPart, suzukiAffineSewnCharacteristic]
  ring

/-- A finite collection of common source channels still factors before any cofinal limit. -/
theorem suzukiAffineSewnIntervalPart_finiteCommonChannels_factorization
    {ι : Type*} (s : Finset ι)
    (alpha beta gamma : ℂ) (WAlpha WBeta : ℂ → ℂ)
    (m : ι → ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (fun u => (∑ j ∈ s, m j u) * WAlpha u)
        (fun u => (∑ j ∈ s, m j u) * WBeta u) z =
      (∑ j ∈ s, m j z) *
        suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z := by
  exact suzukiAffineSewnIntervalPart_commonChannel_factorization
    alpha beta gamma WAlpha WBeta (fun u => ∑ j ∈ s, m j u) z

/-! ## Sewn causal Weil--Robin identity -/

/-- Robin boundary current left after `z^(2 : ℕ)` cancels the screw primitive. -/
def suzukiCausalWeilRobinBoundaryCurrent
    (a : ℝ) (U Uprime z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (a : ℂ)) *
    (Complex.I * z * U - Uprime)

/-- The completed Green channel is boundary current plus completed Weil exterior. -/
theorem suzukiCausalWeilRobinCompletedChannel_eq_boundary_add
    (a : ℝ) (U Uprime weilExterior z : ℂ) :
    suzukiCausalWeilRobinCompletedChannel a U Uprime weilExterior z =
      suzukiCausalWeilRobinBoundaryCurrent a U Uprime z + weilExterior := by
  rfl

/-- **Affine-sewn causal Weil--Robin Green law.**  Sew only after each source exterior has been
converted into its exact denominator-matched Robin plus Weil channel. -/
theorem z_sq_mul_suzukiAffineSewnIntervalPart_weilRobinReconstruction
    (alpha beta gamma : ℂ) (a : ℝ)
    (WAlpha WBeta UAlpha UprimeAlpha EAlpha
      UBeta UprimeBeta EBeta : ℂ → ℂ)
    (z : ℂ) (hz : z ≠ 0) :
    z ^ (2 : ℕ) *
        suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
          (fun u => suzukiCausalWeilRobinReconstruction a
            (UAlpha u) (UprimeAlpha u) (EAlpha u) u)
          (fun u => suzukiCausalWeilRobinReconstruction a
            (UBeta u) (UprimeBeta u) (EBeta u) u) z =
      suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (fun u => suzukiCausalWeilRobinCompletedChannel a
          (UAlpha u) (UprimeAlpha u) (EAlpha u) u)
        (fun u => suzukiCausalWeilRobinCompletedChannel a
          (UBeta u) (UprimeBeta u) (EBeta u) u) z := by
  have hAlpha := z_sq_mul_suzukiCausalWeilRobinReconstruction
    a (UAlpha z) (UprimeAlpha z) (EAlpha z) z hz
  have hBeta := z_sq_mul_suzukiCausalWeilRobinReconstruction
    a (UBeta z) (UprimeBeta z) (EBeta z) z hz
  simp only [suzukiAffineSewnIntervalPart,
    suzukiCausalWeilRobinCompletedChannel]
  linear_combination
    (beta - gamma) * WBeta z * hAlpha -
      (alpha - gamma) * WAlpha z * hBeta

/-! ## Far delayed hinges -/

/-- A far delayed-hinge Weil exterior factors through the sewn characteristic exactly. -/
theorem suzukiAffineSewnIntervalPart_delayedHingeWeilExterior_factorization
    (alpha beta gamma : ℂ) (ell : ℝ)
    (WAlpha WBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (fun u => suzukiDelayedHingeWeilExterior ell (WAlpha u) u)
        (fun u => suzukiDelayedHingeWeilExterior ell (WBeta u) u) z =
      (-Complex.exp (Complex.I * z * (ell : ℂ))) *
        suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z := by
  simpa only [suzukiDelayedHingeWeilExterior] using
    (suzukiAffineSewnIntervalPart_commonChannel_factorization
      alpha beta gamma WAlpha WBeta
        (fun u => -Complex.exp (Complex.I * u * (ell : ℂ))) z)

/-- In Xi-real normalization, the sewn far-prime channel is the same universal jump atom times
the complete sewn characteristic. -/
theorem suzukiAffineSewnIntervalPart_criticalDelayedHinge_factorization
    (alpha beta gamma : ℂ) (weight ell : ℝ)
    (WAlpha WBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (fun u => suzukiCriticalDelayedHingeJumpAtom weight ell u * WAlpha u)
        (fun u => suzukiCriticalDelayedHingeJumpAtom weight ell u * WBeta u) z =
      suzukiCriticalDelayedHingeJumpAtom weight ell z *
        suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z := by
  exact suzukiAffineSewnIntervalPart_commonChannel_factorization
    alpha beta gamma WAlpha WBeta
      (suzukiCriticalDelayedHingeJumpAtom weight ell) z

/-! ## Common-factor Bezoutian and strict sign inheritance -/

/-- A common projective factor acts on the Hermitian Bezoutian only by congruence. -/
theorem suzukiHermitianBezoutCross_commonFactor
    (P m : ℂ → ℂ) (z w : ℂ) :
    suzukiHermitianBezoutCross (fun u => P u * m u) P z w =
      P z * (starRingEnd ℂ) (P w) *
        (m z - (starRingEnd ℂ) (m w)) := by
  simp only [suzukiHermitianBezoutCross, map_mul]
  ring

/-- **Affine-sewing far-prime sign obstruction.**  If the sewn characteristic is nonzero at the
phase-aligned node, its congruence cannot repair the strictly negative far-prime Pick diagonal. -/
theorem suzukiAffineSewnCharacteristicScaledPick_delayedHinge_neg_phaseAligned
    (alpha beta : ℂ) (WAlpha WBeta : ℂ → ℂ)
    (weight ell : ℝ) (hweight : 0 < weight) (hell : 0 < ell)
    (hP : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
      ((2 * Real.pi / ell : ℝ) + Complex.I * (Real.pi / ell : ℝ)) ≠ 0) :
    (suzukiCompoundDenominatorScaledPick
      (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
      (suzukiCriticalDelayedHingeJumpAtom weight ell)
      ((2 * Real.pi / ell : ℝ) + Complex.I * (Real.pi / ell : ℝ))
      ((2 * Real.pi / ell : ℝ) + Complex.I * (Real.pi / ell : ℝ))).re < 0 := by
  exact suzukiCompoundDenominatorScaledPick_delayedHinge_neg_phaseAligned
    (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
      weight ell hweight hell hP

end

end RHTower
