import GaloisForLFunctions.RHTower.SuzukiAffineSewnWeilRobinFarTailFactorization

/-!
# Suzuki causal-entry third-jet boundary law

After `z^(2 : ℕ)` removes the screw primitive, a delayed hinge crosses the aperture wall with matching
value, slope, and curvature.  Moving-boundary point evaluations cancel twice.  The first possible
wall defect is the third jet

`z^(2 : ℕ) * exp (I*a*z) * endpointTrace`.

Affine sewing turns this into one forced marked endpoint bracket.  Thus a prime delay does not
enter the completed channel as an instantaneous kernel jump; the source reporter for a causal
entry Ward law is the third-jet endpoint trace.  No RH premise, positivity hypothesis, estimate,
numerical computation, or Xi-zero data is used.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Denominator-matched entry jets -/

/-- Completed near-entry delayed-hinge channel after multiplication by `z^(2 : ℕ)`. -/
def suzukiDelayedHingeNearCompletedJet0
    (a ell : ℝ) (highMoment firstMoment mass z : ℂ) : ℂ :=
  suzukiOscillatoryKernel z a * (I * z * firstMoment - mass) -
    suzukiOscillatoryKernel z ell * highMoment

/-- Causal current left after the first moving-boundary cancellation. -/
def suzukiDelayedHingeEntryCurrent
    (a ell : ℝ) (highMoment mass z : ℂ) : ℂ :=
  suzukiOscillatoryKernel z a * mass +
    suzukiOscillatoryKernel z ell * highMoment

/-- First delay jet of the completed near-entry channel. -/
def suzukiDelayedHingeNearCompletedJet1
    (a ell : ℝ) (highMoment mass z : ℂ) : ℂ :=
  -I * z * suzukiDelayedHingeEntryCurrent a ell highMoment mass z

/-- Second delay jet: only the moving upper Fourier window survives. -/
def suzukiDelayedHingeNearCompletedJet2
    (ell : ℝ) (highMoment z : ℂ) : ℂ :=
  z ^ (2 : ℕ) * suzukiOscillatoryKernel z ell * highMoment

/-- Third delay jet: the first source-density term is the endpoint trace. -/
def suzukiDelayedHingeNearCompletedJet3
    (a ell : ℝ) (highMoment endpointTrace z : ℂ) : ℂ :=
  I * z ^ (3 : ℕ) * suzukiOscillatoryKernel z ell * highMoment +
    z ^ (2 : ℕ) * suzukiOscillatoryKernel z a * endpointTrace

/-- Far delayed-hinge completed channel after multiplication by `z^(2 : ℕ)`. -/
def suzukiDelayedHingeFarCompletedJet0
    (ell : ℝ) (wholeMoment z : ℂ) : ℂ :=
  -suzukiOscillatoryKernel z ell * wholeMoment

def suzukiDelayedHingeFarCompletedJet1
    (ell : ℝ) (wholeMoment z : ℂ) : ℂ :=
  -I * z * suzukiOscillatoryKernel z ell * wholeMoment

def suzukiDelayedHingeFarCompletedJet2
    (ell : ℝ) (wholeMoment z : ℂ) : ℂ :=
  z ^ (2 : ℕ) * suzukiOscillatoryKernel z ell * wholeMoment

def suzukiDelayedHingeFarCompletedJet3
    (ell : ℝ) (wholeMoment z : ℂ) : ℂ :=
  I * z ^ (3 : ℕ) * suzukiOscillatoryKernel z ell * wholeMoment

/-- The jet-zero definition is exactly the existing causal Weil--Robin completed channel. -/
theorem suzukiDelayedHingeNearCompletedJet0_eq_weilRobinCompletedChannel
    (a ell : ℝ) (highMoment firstMoment mass z : ℂ) :
    suzukiDelayedHingeNearCompletedJet0 a ell highMoment firstMoment mass z =
      suzukiCausalWeilRobinCompletedChannel a firstMoment mass
        (suzukiDelayedHingeWeilExterior ell highMoment z) z := by
  simp only [suzukiDelayedHingeNearCompletedJet0,
    suzukiCausalWeilRobinCompletedChannel, suzukiDelayedHingeWeilExterior,
    suzukiOscillatoryKernel]
  ring_nf

private theorem suzukiOscillatoryKernel_mul_sub
    (a ell : ℝ) (z : ℂ) :
    suzukiOscillatoryKernel z ell *
        suzukiOscillatoryKernel z (a - ell) =
      suzukiOscillatoryKernel z a := by
  simp only [suzukiOscillatoryKernel, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## Exact moving-boundary transport -/

/-- First cancellation.  The derivative hypotheses are exactly
`A'=-B`, `B'=-v(a-ell)`, and `H'=exp(I*z*(a-ell))*v(a-ell)` obtained from the
moving-cut integrals. -/
theorem hasDerivAt_suzukiDelayedHingeNearCompletedJet0
    (a ell : ℝ) (z endpointTrace : ℂ)
    (highMoment firstMoment mass : ℝ → ℂ)
    (hFirst : HasDerivAt firstMoment (-mass ell) ell)
    (hMass : HasDerivAt mass (-endpointTrace) ell)
    (hHigh : HasDerivAt highMoment
      (suzukiOscillatoryKernel z (a - ell) * endpointTrace) ell) :
    HasDerivAt
      (fun u => suzukiDelayedHingeNearCompletedJet0 a u
        (highMoment u) (firstMoment u) (mass u) z)
      (suzukiDelayedHingeNearCompletedJet1 a ell
        (highMoment ell) (mass ell) z) ell := by
  have hKa : HasDerivAt (fun _ : ℝ => suzukiOscillatoryKernel z a) 0 ell :=
    hasDerivAt_const ell _
  have hInner : HasDerivAt
      (fun u => I * z * firstMoment u - mass u)
      (I * z * (-mass ell) - (-endpointTrace)) ell :=
    (hFirst.const_mul (I * z)).sub hMass
  have hLow := hKa.mul hInner
  have hOsc := hasDerivAt_suzukiOscillatoryKernel z ell
  have hTail := hOsc.mul hHigh
  have hEntryPhase :
      suzukiOscillatoryKernel z ell *
          (suzukiOscillatoryKernel z (a - ell) * endpointTrace) =
        suzukiOscillatoryKernel z a * endpointTrace := by
    rw [← mul_assoc, suzukiOscillatoryKernel_mul_sub]
  refine (hLow.sub hTail).congr_deriv ?_
  rw [hEntryPhase]
  simp only [suzukiDelayedHingeNearCompletedJet1,
    suzukiDelayedHingeEntryCurrent]
  ring

/-- Second cancellation.  Endpoint density disappears from the derivative of the entry current. -/
theorem hasDerivAt_suzukiDelayedHingeEntryCurrent
    (a ell : ℝ) (z endpointTrace : ℂ)
    (highMoment mass : ℝ → ℂ)
    (hMass : HasDerivAt mass (-endpointTrace) ell)
    (hHigh : HasDerivAt highMoment
      (suzukiOscillatoryKernel z (a - ell) * endpointTrace) ell) :
    HasDerivAt
      (fun u => suzukiDelayedHingeEntryCurrent a u (highMoment u) (mass u) z)
      ((I * z) * suzukiOscillatoryKernel z ell * highMoment ell) ell := by
  have hKa : HasDerivAt (fun _ : ℝ => suzukiOscillatoryKernel z a) 0 ell :=
    hasDerivAt_const ell _
  have hMassTerm := hKa.mul hMass
  have hOsc := hasDerivAt_suzukiOscillatoryKernel z ell
  have hTail := hOsc.mul hHigh
  have hEntryPhase :
      suzukiOscillatoryKernel z ell *
          (suzukiOscillatoryKernel z (a - ell) * endpointTrace) =
        suzukiOscillatoryKernel z a * endpointTrace := by
    rw [← mul_assoc, suzukiOscillatoryKernel_mul_sub]
  refine (hMassTerm.add hTail).congr_deriv ?_
  rw [hEntryPhase]
  ring

/-- The first jet differentiates to the window-only second jet. -/
theorem hasDerivAt_suzukiDelayedHingeNearCompletedJet1
    (a ell : ℝ) (z endpointTrace : ℂ)
    (highMoment mass : ℝ → ℂ)
    (hMass : HasDerivAt mass (-endpointTrace) ell)
    (hHigh : HasDerivAt highMoment
      (suzukiOscillatoryKernel z (a - ell) * endpointTrace) ell) :
    HasDerivAt
      (fun u => suzukiDelayedHingeNearCompletedJet1 a u
        (highMoment u) (mass u) z)
      (suzukiDelayedHingeNearCompletedJet2 ell (highMoment ell) z) ell := by
  have hCurrent := hasDerivAt_suzukiDelayedHingeEntryCurrent
    a ell z endpointTrace highMoment mass hMass hHigh
  refine (hCurrent.const_mul (-I * z)).congr_deriv ?_
  symm
  simp only [suzukiDelayedHingeNearCompletedJet2]
  calc
    z ^ (2 : ℕ) * suzukiOscillatoryKernel z ell * highMoment ell =
        -(I * I) * z ^ (2 : ℕ) * suzukiOscillatoryKernel z ell * highMoment ell := by
          rw [Complex.I_mul_I]
          ring
    _ = -I * z * (I * z * suzukiOscillatoryKernel z ell * highMoment ell) := by
          ring

/-- The second jet differentiates to the third jet, where the endpoint trace first appears. -/
theorem hasDerivAt_suzukiDelayedHingeNearCompletedJet2
    (a ell : ℝ) (z endpointTrace : ℂ)
    (highMoment : ℝ → ℂ)
    (hHigh : HasDerivAt highMoment
      (suzukiOscillatoryKernel z (a - ell) * endpointTrace) ell) :
    HasDerivAt
      (fun u => suzukiDelayedHingeNearCompletedJet2 u (highMoment u) z)
      (suzukiDelayedHingeNearCompletedJet3 a ell
        (highMoment ell) endpointTrace z) ell := by
  have hOsc := hasDerivAt_suzukiOscillatoryKernel z ell
  have hProduct := hOsc.mul hHigh
  have hfun : (fun u => suzukiDelayedHingeNearCompletedJet2 u (highMoment u) z) =
      fun y => z ^ (2 : ℕ) * ((suzukiOscillatoryKernel z * highMoment) y) := by
    funext u
    simp only [suzukiDelayedHingeNearCompletedJet2, Pi.mul_apply]
    ring
  rw [hfun]
  refine (hProduct.const_mul (z ^ (2 : ℕ))).congr_deriv ?_
  symm
  rw [← mul_assoc (suzukiOscillatoryKernel z ell)
    (suzukiOscillatoryKernel z (a - ell)) endpointTrace,
    suzukiOscillatoryKernel_mul_sub]
  simp only [suzukiDelayedHingeNearCompletedJet3]
  ring

/-! ## Entry-wall classification -/

/-- Near and far completed channels agree at the entry wall. -/
theorem suzukiDelayedHingeCompletedJet0_entryWall
    (a : ℝ) (wholeMoment z : ℂ) :
    suzukiDelayedHingeNearCompletedJet0 a (2 * a) wholeMoment 0 0 z =
      suzukiDelayedHingeFarCompletedJet0 (2 * a) wholeMoment z := by
  simp [suzukiDelayedHingeNearCompletedJet0, suzukiDelayedHingeFarCompletedJet0]

/-- Their first delay jets agree at the entry wall. -/
theorem suzukiDelayedHingeCompletedJet1_entryWall
    (a : ℝ) (wholeMoment z : ℂ) :
    suzukiDelayedHingeNearCompletedJet1 a (2 * a) wholeMoment 0 z =
      suzukiDelayedHingeFarCompletedJet1 (2 * a) wholeMoment z := by
  simp [suzukiDelayedHingeNearCompletedJet1, suzukiDelayedHingeEntryCurrent,
    suzukiDelayedHingeFarCompletedJet1]
  ring

/-- Their second delay jets agree at the entry wall. -/
theorem suzukiDelayedHingeCompletedJet2_entryWall
    (a : ℝ) (wholeMoment z : ℂ) :
    suzukiDelayedHingeNearCompletedJet2 (2 * a) wholeMoment z =
      suzukiDelayedHingeFarCompletedJet2 (2 * a) wholeMoment z := by
  rfl

/-- **Third-jet entry law.**  The first possible near/far defect is exactly the endpoint trace. -/
theorem suzukiDelayedHingeCompletedJet3_entryWall_sub
    (a : ℝ) (wholeMoment endpointTrace z : ℂ) :
    suzukiDelayedHingeNearCompletedJet3 a (2 * a)
        wholeMoment endpointTrace z -
      suzukiDelayedHingeFarCompletedJet3 (2 * a) wholeMoment z =
        z ^ (2 : ℕ) * suzukiOscillatoryKernel z a * endpointTrace := by
  simp only [suzukiDelayedHingeNearCompletedJet3,
    suzukiDelayedHingeFarCompletedJet3]
  ring

/-! ## Affine-sewn entry trace -/

/-- **Affine-sewn third-jet boundary law.**  Sewing preserves the order-two wall matching.  Its
first possible defect is one forced marked endpoint bracket, with no free leakage coordinate. -/
theorem suzukiAffineSewnIntervalPart_entryThirdJet_sub
    (a : ℝ) (alpha beta gamma tauAlpha tauBeta : ℂ)
    (WAlpha WBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (fun u => suzukiDelayedHingeNearCompletedJet3 a (2 * a)
          (WAlpha u) tauAlpha u)
        (fun u => suzukiDelayedHingeNearCompletedJet3 a (2 * a)
          (WBeta u) tauBeta u) z -
      suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (fun u => suzukiDelayedHingeFarCompletedJet3 (2 * a) (WAlpha u) u)
        (fun u => suzukiDelayedHingeFarCompletedJet3 (2 * a) (WBeta u) u) z =
      z ^ (2 : ℕ) * suzukiOscillatoryKernel z a *
        ((beta - gamma) * WBeta z * tauAlpha -
          (alpha - gamma) * WAlpha z * tauBeta) := by
  simp only [suzukiAffineSewnIntervalPart,
    suzukiDelayedHingeNearCompletedJet3,
    suzukiDelayedHingeFarCompletedJet3]
  ring

/-- A common normalized endpoint trace survives affine sewing rather than cancelling. -/
theorem suzukiAffineSewnEntryThirdJet_commonNormalizedTrace
    (a : ℝ) (alpha beta gamma m tauAlpha tauBeta : ℂ)
    (WAlpha WBeta : ℂ → ℂ) (z : ℂ)
    (hAlpha : tauAlpha = m * WAlpha z)
    (hBeta : tauBeta = m * WBeta z) :
    z ^ (2 : ℕ) * suzukiOscillatoryKernel z a *
        ((beta - gamma) * WBeta z * tauAlpha -
          (alpha - gamma) * WAlpha z * tauBeta) =
      z ^ (2 : ℕ) * suzukiOscillatoryKernel z a * m *
        suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z := by
  rw [hAlpha, hBeta]
  simp only [suzukiAffineSewnCharacteristic]
  ring

end

end RHTower
