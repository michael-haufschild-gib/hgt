import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPoincareRadialDerivativePullback

/-!
# Full self-dual AdS two-jet vertex in the BM/Rindler chart

Equation (100) of Chowdhury--Doran--Lipstein--Monteiro--Nagy, arXiv:2411.04172,
contains ordinary Poincare-radial derivatives acting separately on the two scaled legs `P/Z`
and `Q/Z`.  Squaring the deformed bracket requires genuine second jets: replacing the square by
the square of its already-evaluated first-jet value loses both second derivatives.

This module first complexifies the exact chart vector

`partial_Z = rho * partial_sigma + (1-rho^(2 : ℕ))/sigma * partial_rho`.

On a pure BM profile `f(1-rho^(2 : ℕ))`, write `s = sigma^-1`.  Its first two Poincare jets are

`partial_Z f = C(rho) s f'`,

`partial_Z^(2 : ℕ) f = B(rho) s^(2 : ℕ) f' + C(rho)^(2 : ℕ) s^(2 : ℕ) f''`,

where `C(rho) = -2 rho (1-rho^(2 : ℕ))` and
`B(rho) = 2 (1-rho^(2 : ℕ)) (4 rho^(2 : ℕ)-1)`.  The `B f'` connection term is forced by differentiating
the chart coefficient; it is absent from a naive squared-chain-rule substitution.

The complete bidifferential SDG vertex is then defined on two arbitrary complex two-jets.  After
the exact BM pullback, it is proved to be a Laurent polynomial of degree exactly at most two in
`sigma^-1`; all three coefficients are explicit.  The zeroth-order coefficient is the flat
double-copy bracket, while the first and second coefficients retain respectively the one-jet,
connection, second-jet, and AdS-curvature data.  The physical substitution `s = sigma^-1` is an
unconditional corollary, with no nonzero-coordinate hypothesis.

This closes the full radial bidifferential operator and its chart transport.  It deliberately
does not identify a Birmingham--Mokhtari master field with the light-cone Plebanski scalar `P/Z`:
that requires the still-missing gauge-invariant metric/light-cone reconstruction before the
negative leg and left-QNM projection can be attached.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [FULL TWO-JET VERTEX]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Value and first two ordinary Poincare-radial derivatives of a scaled light-cone leg. -/
structure D4ComplexRadialTwoJet where
  value : ℂ
  first : ℂ
  second : ℂ

/-- Numerator of the first Poincare derivative of a pure BM radial profile. -/
def d4BMPoincareFirstPullbackNumerator (rho : ℂ) : ℂ :=
  -2 * rho * (1 - rho ^ (2 : ℕ))

/-- Connection numerator in the second Poincare derivative of a pure BM radial profile. -/
def d4BMPoincareSecondPullbackConnectionNumerator (rho : ℂ) : ℂ :=
  2 * (1 - rho ^ (2 : ℕ)) * (4 * rho ^ (2 : ℕ) - 1)

/-- Complexified second iterate of the pulled-back coordinate vector on a general symmetric
two-jet.  `sigmaInv` is an algebraic inverse-coordinate variable; using it keeps all identities
valid without a nonzero-coordinate premise. -/
def d4PoincareRadialSecondPullbackOperatorOnJet
    (rho sigmaInv : ℂ)
    (partialSigma partialRho partialSigmaSigma partialSigmaRho partialRhoRho : ℂ) : ℂ :=
  let a := (1 - rho ^ (2 : ℕ)) * sigmaInv
  rho ^ (2 : ℕ) * partialSigmaSigma +
    2 * rho * a * partialSigmaRho +
    a ^ (2 : ℕ) * partialRhoRho +
    a * partialSigma -
    3 * rho * (1 - rho ^ (2 : ℕ)) * sigmaInv ^ (2 : ℕ) * partialRho

/-- Exact second-order chain rule.  The first-jet connection coefficient is
`2(1-rho^(2 : ℕ))(4rho^(2 : ℕ)-1)`, not zero. -/
theorem d4PoincareRadialSecondPullbackOperatorOnBMSecondJet
    (rho sigmaInv firstBM secondBM : ℂ) :
    d4PoincareRadialSecondPullbackOperatorOnJet rho sigmaInv
        0 (-2 * rho * firstBM) 0 0 (-2 * firstBM + 4 * rho ^ (2 : ℕ) * secondBM) =
      d4BMPoincareSecondPullbackConnectionNumerator rho * sigmaInv ^ (2 : ℕ) * firstBM +
        d4BMPoincareFirstPullbackNumerator rho ^ (2 : ℕ) * sigmaInv ^ (2 : ℕ) * secondBM := by
  simp [d4PoincareRadialSecondPullbackOperatorOnJet,
    d4BMPoincareSecondPullbackConnectionNumerator,
    d4BMPoincareFirstPullbackNumerator]
  ring

/-- First Poincare derivative of a pure BM first jet, with algebraic inverse coordinate. -/
def d4PoincareRadialFirstDerivativeOnBMJetInv
    (rho sigmaInv firstBM : ℂ) : ℂ :=
  d4BMPoincareFirstPullbackNumerator rho * sigmaInv * firstBM

/-- Second Poincare derivative of a pure BM second jet, including the chart connection term. -/
def d4PoincareRadialSecondDerivativeOnBMJetInv
    (rho sigmaInv firstBM secondBM : ℂ) : ℂ :=
  d4BMPoincareSecondPullbackConnectionNumerator rho * sigmaInv ^ (2 : ℕ) * firstBM +
    d4BMPoincareFirstPullbackNumerator rho ^ (2 : ℕ) * sigmaInv ^ (2 : ℕ) * secondBM

/-- Exact Poincare two-jet obtained from a pure BM radial two-jet. -/
def d4PoincareRadialTwoJetOfBMInv
    (rho sigmaInv : ℂ) (J : D4ComplexRadialTwoJet) : D4ComplexRadialTwoJet where
  value := J.value
  first := d4PoincareRadialFirstDerivativeOnBMJetInv rho sigmaInv J.first
  second := d4PoincareRadialSecondDerivativeOnBMJetInv rho sigmaInv J.first J.second

/-- Physical real-chart specialization of the exact BM-to-Poincare two-jet transport. -/
def d4PoincareRadialTwoJetOfBM
    (rho sigma : ℝ) (J : D4ComplexRadialTwoJet) : D4ComplexRadialTwoJet :=
  d4PoincareRadialTwoJetOfBMInv (rho : ℂ) (sigma : ℂ)⁻¹ J

/-- First action of `(q + partial_Z)` on one radial jet. -/
def ads4SelfDualShiftedRadialFirstAction
    (q : ℂ) (J : D4ComplexRadialTwoJet) : ℂ :=
  q * J.value + J.first

/-- Second action of `(q + partial_Z)^(2 : ℕ)` on one radial jet. -/
def ads4SelfDualShiftedRadialSecondAction
    (q : ℂ) (J : D4ComplexRadialTwoJet) : ℂ :=
  q ^ (2 : ℕ) * J.value + 2 * q * J.first + J.second

/-- The exact `Xleftrightarrow^(2 : ℕ)` term of the self-dual gravity vertex, already evaluated on the
two scaled-leg two-jets. -/
def ads4SelfDualDeformedBracketSquareOnTwoJets
    (xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  xBracket ^ (2 : ℕ) * P.value * Q.value -
    (1 / 4 : ℂ) *
      (q1w ^ (2 : ℕ) * P.value * ads4SelfDualShiftedRadialSecondAction q2 Q +
        q2w ^ (2 : ℕ) * ads4SelfDualShiftedRadialSecondAction q1 P * Q.value -
        2 * q1w * q2w * ads4SelfDualShiftedRadialFirstAction q1 P *
          ads4SelfDualShiftedRadialFirstAction q2 Q)

/-- Exact `Xleftrightarrow/Z` term.  `inverseZ` is outside every left/right derivative, matching
the fixed-denominator convention in the source formula. -/
def ads4SelfDualDeformedBracketOverZOnTwoJets
    (inverseZ xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  inverseZ *
    (xBracket * P.value * Q.value +
      (Complex.I / 2) *
        (q1w * P.value * ads4SelfDualShiftedRadialFirstAction q2 Q -
          q2w * ads4SelfDualShiftedRadialFirstAction q1 P * Q.value))

/-- Full equation-(100) self-dual AdS gravity vertex on arbitrary scaled-leg radial two-jets. -/
def ads4SelfDualDeformedVertexOnTwoJets
    (inverseZ xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  (1 / 2 : ℂ) *
    (ads4SelfDualDeformedBracketSquareOnTwoJets xBracket q1 q2 q1w q2w P Q +
      Complex.I *
        ads4SelfDualDeformedBracketOverZOnTwoJets
          inverseZ xBracket q1 q2 q1w q2w P Q * (q2w - q1w))

/-- Exchange of the two scaled legs preserves the full deformed vertex when the alternating
kinematic bracket changes sign.  This checks the left/right-derivative bookkeeping in the exact
two-jet definition. -/
theorem ads4SelfDualDeformedVertexOnTwoJets_exchange
    (inverseZ xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) :
    ads4SelfDualDeformedVertexOnTwoJets inverseZ (-xBracket) q2 q1 q2w q1w Q P =
      ads4SelfDualDeformedVertexOnTwoJets inverseZ xBracket q1 q2 q1w q2w P Q := by
  simp [ads4SelfDualDeformedVertexOnTwoJets,
    ads4SelfDualDeformedBracketSquareOnTwoJets,
    ads4SelfDualDeformedBracketOverZOnTwoJets,
    ads4SelfDualShiftedRadialFirstAction,
    ads4SelfDualShiftedRadialSecondAction]
  ring

/-- Scaled bulk-to-boundary exponential jet `exp(-q Z)`. -/
def ads4SelfDualBulkToBoundaryScaledTwoJet (q : ℂ) : D4ComplexRadialTwoJet where
  value := 1
  first := -q
  second := q ^ (2 : ℕ)

@[simp]
theorem ads4SelfDualShiftedRadialFirstAction_bulkToBoundary (q : ℂ) :
    ads4SelfDualShiftedRadialFirstAction q
      (ads4SelfDualBulkToBoundaryScaledTwoJet q) = 0 := by
  simp [ads4SelfDualShiftedRadialFirstAction,
    ads4SelfDualBulkToBoundaryScaledTwoJet]

@[simp]
theorem ads4SelfDualShiftedRadialSecondAction_bulkToBoundary (q : ℂ) :
    ads4SelfDualShiftedRadialSecondAction q
      (ads4SelfDualBulkToBoundaryScaledTwoJet q) = 0 := by
  simp [ads4SelfDualShiftedRadialSecondAction,
    ads4SelfDualBulkToBoundaryScaledTwoJet]
  ring

/-- On two bulk-to-boundary legs, the full bidifferential definition recovers the corpus's exact
curvature-corrected plane-wave vertex. -/
theorem ads4SelfDualDeformedVertexOnTwoJets_bulkToBoundary_eq_planeWaveVertex
    (inverseZ p h q k radial1 radial2 : ℂ) :
    ads4SelfDualDeformedVertexOnTwoJets inverseZ
        (ads4SelfDualKinematicBracket p h q k) radial1 radial2 h k
        (ads4SelfDualBulkToBoundaryScaledTwoJet radial1)
        (ads4SelfDualBulkToBoundaryScaledTwoJet radial2) =
      ads4SelfDualPlaneWaveVertex (Complex.I * inverseZ) p h q k := by
  simp [ads4SelfDualDeformedVertexOnTwoJets,
    ads4SelfDualDeformedBracketSquareOnTwoJets,
    ads4SelfDualDeformedBracketOverZOnTwoJets,
    ads4SelfDualShiftedRadialFirstAction,
    ads4SelfDualShiftedRadialSecondAction,
    ads4SelfDualPlaneWaveVertex, ads4SelfDualKinematicBracket,
    ads4SelfDualBulkToBoundaryScaledTwoJet]
  ring

/-- Radial deformation determinant `q1w*q2-q2w*q1`. -/
def ads4SelfDualRadialDeformationDelta
    (q1 q2 q1w q2w : ℂ) : ℂ :=
  q1w * q2 - q2w * q1

/-- Alternating first-BM-jet pairing carried by the radial deformation. -/
def ads4SelfDualBMRadialFirstJetCross
    (q1w q2w : ℂ) (P Q : D4ComplexRadialTwoJet) : ℂ :=
  q1w * P.value * Q.first - q2w * P.first * Q.value

/-- Zeroth Laurent coefficient of the pulled-back squared bracket. -/
def ads4SelfDualBMSquareLaurentCoefficientZero
    (xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  (xBracket ^ (2 : ℕ) -
      (1 / 4 : ℂ) * ads4SelfDualRadialDeformationDelta q1 q2 q1w q2w ^ (2 : ℕ)) *
    P.value * Q.value

/-- First Laurent coefficient of the pulled-back squared bracket. -/
def ads4SelfDualBMSquareLaurentCoefficientOne
    (rho _xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  -(1 / 2 : ℂ) * d4BMPoincareFirstPullbackNumerator rho *
    ads4SelfDualRadialDeformationDelta q1 q2 q1w q2w *
    ads4SelfDualBMRadialFirstJetCross q1w q2w P Q

/-- Second Laurent coefficient of the pulled-back squared bracket.  Its first line is the chart
connection term; its second line contains the genuine two-jet double copy. -/
def ads4SelfDualBMSquareLaurentCoefficientTwo
    (rho _xBracket _q1 _q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  -(1 / 4 : ℂ) *
    (d4BMPoincareSecondPullbackConnectionNumerator rho *
        (q1w ^ (2 : ℕ) * P.value * Q.first + q2w ^ (2 : ℕ) * P.first * Q.value) +
      d4BMPoincareFirstPullbackNumerator rho ^ (2 : ℕ) *
        (q1w ^ (2 : ℕ) * P.value * Q.second + q2w ^ (2 : ℕ) * P.second * Q.value -
          2 * q1w * q2w * P.first * Q.first))

/-- First Laurent coefficient of `Xleftrightarrow/Z` after the physical `Z=rho*sigma` pullback. -/
def ads4SelfDualBMCurvatureLaurentCoefficientOne
    (rho xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  rho⁻¹ *
    (xBracket * P.value * Q.value +
      (Complex.I / 2) * ads4SelfDualRadialDeformationDelta q1 q2 q1w q2w *
        P.value * Q.value)

/-- Second Laurent coefficient of `Xleftrightarrow/Z`, coupling curvature to first BM jets. -/
def ads4SelfDualBMCurvatureLaurentCoefficientTwo
    (rho _xBracket _q1 _q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  rho⁻¹ * (Complex.I / 2) * d4BMPoincareFirstPullbackNumerator rho *
    ads4SelfDualBMRadialFirstJetCross q1w q2w P Q

/-- Constant Laurent coefficient of the full pulled-back vertex. -/
def ads4SelfDualBMVertexLaurentCoefficientZero
    (_rho xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  (1 / 2 : ℂ) *
    ads4SelfDualBMSquareLaurentCoefficientZero xBracket q1 q2 q1w q2w P Q

/-- Linear Laurent coefficient of the full pulled-back vertex. -/
def ads4SelfDualBMVertexLaurentCoefficientOne
    (rho xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  (1 / 2 : ℂ) *
    (ads4SelfDualBMSquareLaurentCoefficientOne
        rho xBracket q1 q2 q1w q2w P Q +
      Complex.I * (q2w - q1w) *
        ads4SelfDualBMCurvatureLaurentCoefficientOne
          rho xBracket q1 q2 q1w q2w P Q)

/-- Quadratic Laurent coefficient of the full pulled-back vertex. -/
def ads4SelfDualBMVertexLaurentCoefficientTwo
    (rho xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) : ℂ :=
  (1 / 2 : ℂ) *
    (ads4SelfDualBMSquareLaurentCoefficientTwo
        rho xBracket q1 q2 q1w q2w P Q +
      Complex.I * (q2w - q1w) *
        ads4SelfDualBMCurvatureLaurentCoefficientTwo
          rho xBracket q1 q2 q1w q2w P Q)

/-- Full exact Laurent decomposition after pulling two arbitrary BM radial two-jets through the
Rindler/Poincare chart.  This is polynomial in the algebraic inverse-coordinate `sigmaInv`, so it
has no coordinate nonvanishing premise. -/
theorem ads4SelfDualDeformedVertexOnBMPulledTwoJets_eq_laurent
    (rho sigmaInv xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) :
    ads4SelfDualDeformedVertexOnTwoJets (rho⁻¹ * sigmaInv)
        xBracket q1 q2 q1w q2w
        (d4PoincareRadialTwoJetOfBMInv rho sigmaInv P)
        (d4PoincareRadialTwoJetOfBMInv rho sigmaInv Q) =
      ads4SelfDualBMVertexLaurentCoefficientZero
          rho xBracket q1 q2 q1w q2w P Q +
        ads4SelfDualBMVertexLaurentCoefficientOne
            rho xBracket q1 q2 q1w q2w P Q * sigmaInv +
          ads4SelfDualBMVertexLaurentCoefficientTwo
              rho xBracket q1 q2 q1w q2w P Q * sigmaInv ^ (2 : ℕ) := by
  simp [ads4SelfDualDeformedVertexOnTwoJets,
    ads4SelfDualDeformedBracketSquareOnTwoJets,
    ads4SelfDualDeformedBracketOverZOnTwoJets,
    ads4SelfDualShiftedRadialFirstAction,
    ads4SelfDualShiftedRadialSecondAction,
    d4PoincareRadialTwoJetOfBMInv,
    d4PoincareRadialFirstDerivativeOnBMJetInv,
    d4PoincareRadialSecondDerivativeOnBMJetInv,
    ads4SelfDualBMVertexLaurentCoefficientZero,
    ads4SelfDualBMVertexLaurentCoefficientOne,
    ads4SelfDualBMVertexLaurentCoefficientTwo,
    ads4SelfDualBMSquareLaurentCoefficientZero,
    ads4SelfDualBMSquareLaurentCoefficientOne,
    ads4SelfDualBMSquareLaurentCoefficientTwo,
    ads4SelfDualBMCurvatureLaurentCoefficientOne,
    ads4SelfDualBMCurvatureLaurentCoefficientTwo,
    ads4SelfDualRadialDeformationDelta,
    ads4SelfDualBMRadialFirstJetCross]
  ring

/-- Physical real-chart form of the complete Laurent decomposition. -/
theorem ads4SelfDualDeformedVertexOnBMPulledTwoJets_eq_physicalLaurent
    (rho sigma : ℝ) (xBracket q1 q2 q1w q2w : ℂ)
    (P Q : D4ComplexRadialTwoJet) :
    ads4SelfDualDeformedVertexOnTwoJets ((rho : ℂ)⁻¹ * (sigma : ℂ)⁻¹)
        xBracket q1 q2 q1w q2w
        (d4PoincareRadialTwoJetOfBM rho sigma P)
        (d4PoincareRadialTwoJetOfBM rho sigma Q) =
      ads4SelfDualBMVertexLaurentCoefficientZero
          (rho : ℂ) xBracket q1 q2 q1w q2w P Q +
        ads4SelfDualBMVertexLaurentCoefficientOne
            (rho : ℂ) xBracket q1 q2 q1w q2w P Q * (sigma : ℂ)⁻¹ +
          ads4SelfDualBMVertexLaurentCoefficientTwo
              (rho : ℂ) xBracket q1 q2 q1w q2w P Q * (sigma : ℂ)⁻¹ ^ (2 : ℕ) := by
  exact ads4SelfDualDeformedVertexOnBMPulledTwoJets_eq_laurent
    (rho : ℂ) (sigma : ℂ)⁻¹ xBracket q1 q2 q1w q2w P Q

end

end RHTower
