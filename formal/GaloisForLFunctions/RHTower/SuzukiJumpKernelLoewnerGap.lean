import GaloisForLFunctions.RHTower.SuzukiCarlemanCoordinatePhase

/-!
# Suzuki jump kernel as an exact Loewner growth gap

The curvature-centered screw recurrence supplies admissible shift pairs with the required central
residue sign. Remaining RH-bearing theorem is positivity of full sewn jump Pick kernel.

For real form shifts `alpha < beta < 0`, let `qAlpha` and `qBeta` be reflection-odd normalized
right-triangle responses. Actual admissible sewn exterior Weyl quotient is

`-multiplier + (beta*qAlpha-alpha*qBeta)/(beta-alpha)`.

Pick kernel is real-affine in its function, so full jump kernel is same affine extrapolation of
two source Pick kernels minus fixed Xi-multiplier kernel. On every finite test vector its
nonnegativity is equivalent to

`(-alpha) * sourceGrowth >= (beta-alpha) * multiplierDeficit`.

This is matrix/Loewner analogue of scalar central chord-mass gap. No positivity, RH premise,
estimate, or numerical computation is assumed.
-/

open Complex GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Scalar Pick kernel of a spectral function. -/
def suzukiScalarPickKernel (m : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (m z - (starRingEnd ℂ) (m w)) / (z - (starRingEnd ℂ) w)

/-- Affine extrapolation to form shift zero from two real source shifts. -/
def suzukiRealAffineSourceFunction
    (alpha beta : ℝ) (qAlpha qBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((beta : ℂ) * qAlpha z - (alpha : ℂ) * qBeta z) / ((beta - alpha : ℝ) : ℂ)

/-- Abstract normalized sewn sheet jump. -/
def suzukiJumpWeylCandidate
    (multiplier : ℂ → ℂ) (alpha beta : ℝ)
    (qAlpha qBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  -multiplier z + suzukiRealAffineSourceFunction alpha beta qAlpha qBeta z

/-- Pick kernel commutes exactly with real affine source extrapolation. -/
theorem suzukiScalarPickKernel_realAffineSourceFunction
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    (qAlpha qBeta : ℂ → ℂ) (z w : ℂ) :
    suzukiScalarPickKernel
        (suzukiRealAffineSourceFunction alpha beta qAlpha qBeta) z w =
      ((beta : ℂ) * suzukiScalarPickKernel qAlpha z w -
        (alpha : ℂ) * suzukiScalarPickKernel qBeta z w) /
          ((beta - alpha : ℝ) : ℂ) := by
  simp only [suzukiScalarPickKernel, suzukiRealAffineSourceFunction,
    map_div₀, map_sub, map_mul, conj_ofReal]
  have habc : ((beta - alpha : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hab.symm
  field_simp [habc]
  ring

/-- Full jump kernel is affine source kernel minus fixed multiplier kernel. -/
theorem suzukiScalarPickKernel_jumpWeylCandidate
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    (multiplier qAlpha qBeta : ℂ → ℂ) (z w : ℂ) :
    suzukiScalarPickKernel
        (suzukiJumpWeylCandidate multiplier alpha beta qAlpha qBeta) z w =
      -suzukiScalarPickKernel multiplier z w +
        ((beta : ℂ) * suzukiScalarPickKernel qAlpha z w -
          (alpha : ℂ) * suzukiScalarPickKernel qBeta z w) /
            ((beta - alpha : ℝ) : ℂ) := by
  change suzukiScalarPickKernel
      (fun u => -multiplier u +
        suzukiRealAffineSourceFunction alpha beta qAlpha qBeta u) z w = _
  rw [show suzukiScalarPickKernel
      (fun u => -multiplier u +
        suzukiRealAffineSourceFunction alpha beta qAlpha qBeta u) z w =
      -suzukiScalarPickKernel multiplier z w +
        suzukiScalarPickKernel
          (suzukiRealAffineSourceFunction alpha beta qAlpha qBeta) z w by
    simp only [suzukiScalarPickKernel, map_add, map_neg]
    ring]
  rw [suzukiScalarPickKernel_realAffineSourceFunction hab]

/-- **Exact Loewner gap law.** On any finite test vector, positivity of affine source kernel minus
target is equivalent to source growth paying whole multiplier deficit. -/
theorem suzukiAffineKernelGap_nonneg_iff_loewnerGrowth
    {alpha beta sourceAlpha sourceBeta target : ℝ}
    (hab : alpha < beta) :
    0 ≤ (beta * sourceAlpha - alpha * sourceBeta) / (beta - alpha) - target ↔
      (beta - alpha) * (target - sourceAlpha) ≤
        (-alpha) * (sourceBeta - sourceAlpha) := by
  have hden : 0 < beta - alpha := sub_pos.mpr hab
  rw [sub_nonneg, le_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- Forward consumer of exact Loewner growth law. -/
theorem suzukiAffineKernelGap_nonneg_of_loewnerGrowth
    {alpha beta sourceAlpha sourceBeta target : ℝ}
    (hab : alpha < beta)
    (hgrowth : (beta - alpha) * (target - sourceAlpha) ≤
      (-alpha) * (sourceBeta - sourceAlpha)) :
    0 ≤ (beta * sourceAlpha - alpha * sourceBeta) / (beta - alpha) - target :=
  (suzukiAffineKernelGap_nonneg_iff_loewnerGrowth hab).2 hgrowth

/-- Negative-shift sewing is genuine extrapolation beyond nearer source. -/
theorem suzukiAffineKernel_extrapolation_factor_gt_one
    {alpha beta : ℝ} (hab : alpha < beta) (hbeta : beta < 0) :
    1 < -alpha / (beta - alpha) := by
  rw [lt_div_iff₀ (sub_pos.mpr hab)]
  linarith

/-- **Concrete source identification.** Away from finite characteristic divisor, actual
one-sided-coordinate sewn quotient is exactly abstract jump candidate formed from reflection-odd
normalized right triangles. -/
theorem suzukiAffineSewnExteriorWeylQuotient_eq_jumpWeylCandidate
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    {z : ℂ}
    (hWAlphaZ : WAlpha z ≠ 0) (hWBetaZ : WBeta z ≠ 0) :
    suzukiAffineSewnExteriorWeylQuotient
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta)
        WAlpha WBeta rightAlpha rightBeta z =
      suzukiJumpWeylCandidate (suzukiShiftedXiMultiplier 0) alpha beta
        (suzukiReflectionOddPart (fun u => rightAlpha u / WAlpha u))
        (suzukiReflectionOddPart (fun u => rightBeta u / WBeta u)) z := by
  simp only [suzukiAffineSewnExteriorWeylQuotient, suzukiExteriorWeylQuotient,
    suzukiAffineSewnOddCarlemanPoleCarrier, suzukiOddCarlemanPoleCarrier,
    suzukiAffineSewnCharacteristic, suzukiAffineSewnIntervalPart,
    suzukiReflectionOddPart, suzukiOneSidedCenteredShiftParameter,
    suzukiJumpWeylCandidate, suzukiRealAffineSourceFunction,
    hWAlpha z, hWBeta z]
  have habc : ((beta - alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab.symm
  field_simp [habc, hWAlphaZ, hWBetaZ, I_ne_zero]
  rw [show -(beta : ℂ) - -(alpha : ℂ) = -((beta - alpha : ℝ) : ℂ) by push_cast; ring]
  field_simp [habc]
  ring

/-- Full Pick kernel of actual admissible sewn quotient is Xi multiplier deficit plus affine
Loewner extrapolation of two reflection-odd source kernels. -/
theorem suzukiScalarPickKernel_affineSewnExteriorWeylQuotient
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    {z w : ℂ}
    (hWAlphaZ : WAlpha z ≠ 0) (hWBetaZ : WBeta z ≠ 0)
    (hWAlphaW : WAlpha w ≠ 0) (hWBetaW : WBeta w ≠ 0) :
    suzukiScalarPickKernel
        (suzukiAffineSewnExteriorWeylQuotient
          (suzukiOneSidedCenteredShiftParameter alpha)
          (suzukiOneSidedCenteredShiftParameter beta)
          WAlpha WBeta rightAlpha rightBeta) z w =
      -suzukiScalarPickKernel (suzukiShiftedXiMultiplier 0) z w +
        ((beta : ℂ) * suzukiScalarPickKernel
            (suzukiReflectionOddPart (fun u => rightAlpha u / WAlpha u)) z w -
          (alpha : ℂ) * suzukiScalarPickKernel
            (suzukiReflectionOddPart (fun u => rightBeta u / WBeta u)) z w) /
          ((beta - alpha : ℝ) : ℂ) := by
  let qAlpha : ℂ → ℂ :=
    suzukiReflectionOddPart (fun u => rightAlpha u / WAlpha u)
  let qBeta : ℂ → ℂ :=
    suzukiReflectionOddPart (fun u => rightBeta u / WBeta u)
  let m : ℂ → ℂ :=
    suzukiAffineSewnExteriorWeylQuotient
      (suzukiOneSidedCenteredShiftParameter alpha)
      (suzukiOneSidedCenteredShiftParameter beta)
      WAlpha WBeta rightAlpha rightBeta
  let candidate : ℂ → ℂ :=
    suzukiJumpWeylCandidate (suzukiShiftedXiMultiplier 0) alpha beta qAlpha qBeta
  have hz : m z = candidate z := by
    exact suzukiAffineSewnExteriorWeylQuotient_eq_jumpWeylCandidate
      hab hWAlpha hWBeta hWAlphaZ hWBetaZ
  have hw : m w = candidate w := by
    exact suzukiAffineSewnExteriorWeylQuotient_eq_jumpWeylCandidate
      hab hWAlpha hWBeta hWAlphaW hWBetaW
  change suzukiScalarPickKernel m z w = _
  rw [show suzukiScalarPickKernel m z w =
      suzukiScalarPickKernel candidate z w by
    simp only [suzukiScalarPickKernel, hz, hw]]
  exact suzukiScalarPickKernel_jumpWeylCandidate hab
    (suzukiShiftedXiMultiplier 0) qAlpha qBeta z w

end

end RHTower
