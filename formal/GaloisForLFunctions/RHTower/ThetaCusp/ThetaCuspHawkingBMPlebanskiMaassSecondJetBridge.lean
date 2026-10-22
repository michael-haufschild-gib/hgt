import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPlebanskiBalancedSpinTwoSource

/-!
# Maass-operator realization of the balanced BM Plebanski source

The balanced spin-two word in the BM-pulled Plebanski source must be translated into modular
Eisenstein operators before the completed angular projection can be computed.  With the standard
non-holomorphic Maass convention

`R_k = 2 i sigma partial_z + k/2`,

`L_k = -2 i sigma partial_zbar - k/2`,

one geometric spin step changes modular weight by two.  A traceless Hessian component therefore
has modular weight `+4` or `-4`, obtained by `R_2 R_0` or `L_(-2) L_0`.

This module evaluates both two-step words on an arbitrary complete BM second jet.  They are
exactly the negatives of the corresponding connection-corrected covariant spin components.  On
the pure traceless sector from the preceding module, the connection terms vanish and the pulled
Eq. (63) source is exactly the balanced Maass product.  This closes the local tensor-to-operator
bridge; regularized projection of that word is the next analytic burden.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [MAASS SECOND-JET BRIDGE]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Weight-zero Maass raising operator evaluated on a complete BM second jet. -/
def d4BMMaassRaiseZeroOnFullSecondJet (sigmaScale : ℂ) (J : D4BMFullSecondJet) : ℂ :=
  sigmaScale * (J.first.sigma + Complex.I * J.first.horizonX)

/-- Weight-zero Maass lowering operator evaluated on a complete BM second jet. -/
def d4BMMaassLowerZeroOnFullSecondJet (sigmaScale : ℂ) (J : D4BMFullSecondJet) : ℂ :=
  sigmaScale * (J.first.sigma - Complex.I * J.first.horizonX)

/-- Two raising steps `R_2 R_0`, including the weight and connection terms. -/
def d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
    (sigmaScale : ℂ) (J : D4BMFullSecondJet) : ℂ :=
  sigmaScale ^ (2 : ℕ) *
      (J.sigmaSigma - J.horizonXHorizonX + 2 * Complex.I * J.horizonXSigma) +
    2 * sigmaScale * (J.first.sigma + Complex.I * J.first.horizonX)

/-- Two lowering steps `L_(-2) L_0`, including the weight and connection terms. -/
def d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
    (sigmaScale : ℂ) (J : D4BMFullSecondJet) : ℂ :=
  sigmaScale ^ (2 : ℕ) *
      (J.sigmaSigma - J.horizonXHorizonX - 2 * Complex.I * J.horizonXSigma) +
    2 * sigmaScale * (J.first.sigma - Complex.I * J.first.horizonX)

/-- Connection-corrected geometric spin `+2` Hessian component. -/
def d4BMCovariantHorizonSpinPlus (sigmaScale : ℂ) (J : D4BMFullSecondJet) : ℂ :=
  sigmaScale ^ (2 : ℕ) *
      (J.horizonXHorizonX - J.sigmaSigma + 2 * Complex.I * J.horizonXSigma) -
    2 * sigmaScale * (J.first.sigma - Complex.I * J.first.horizonX)

/-- Connection-corrected geometric spin `-2` Hessian component. -/
def d4BMCovariantHorizonSpinMinus (sigmaScale : ℂ) (J : D4BMFullSecondJet) : ℂ :=
  sigmaScale ^ (2 : ℕ) *
      (J.horizonXHorizonX - J.sigmaSigma - 2 * Complex.I * J.horizonXSigma) -
    2 * sigmaScale * (J.first.sigma + Complex.I * J.first.horizonX)

/-- `R_2 R_0` is exactly minus the covariant spin `-2` Hessian component. -/
theorem d4BMMaassRaiseTwoRaiseZero_eq_neg_covariantSpinMinus
    (sigmaScale : ℂ) (J : D4BMFullSecondJet) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet sigmaScale J =
      -d4BMCovariantHorizonSpinMinus sigmaScale J := by
  simp [d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet, d4BMCovariantHorizonSpinMinus]
  ring

/-- `L_(-2) L_0` is exactly minus the covariant spin `+2` Hessian component. -/
theorem d4BMMaassLowerNegTwoLowerZero_eq_neg_covariantSpinPlus
    (sigmaScale : ℂ) (J : D4BMFullSecondJet) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet sigmaScale J =
      -d4BMCovariantHorizonSpinPlus sigmaScale J := by
  simp [d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet, d4BMCovariantHorizonSpinPlus]
  ring

/-- On a pure traceless Hessian, `R_2 R_0` recovers minus its `-2` component. -/
@[simp] theorem d4BMMaassRaiseTwoRaiseZero_pureSpinTwo
    (spinPlus spinMinus : ℂ) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet 1
        (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) =
      -spinMinus := by
  simp [d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet,
    d4BMPureSpinTwoHorizonHessianSecondJet]
  field_simp [Complex.I_ne_zero]
  ring

/-- On a pure traceless Hessian, `L_(-2) L_0` recovers minus its `+2` component. -/
@[simp] theorem d4BMMaassLowerNegTwoLowerZero_pureSpinTwo
    (spinPlus spinMinus : ℂ) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet 1
        (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) =
      -spinPlus := by
  simp [d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet,
    d4BMPureSpinTwoHorizonHessianSecondJet]
  field_simp [Complex.I_ne_zero]
  ring

/-- Exact local factorization of the pure spin-two Eq. (63) source through the balanced
`R_2 R_0`--`L_(-2) L_0` Maass word. -/
theorem ads4PlebanskiJacobiDoubleBracket_pureSpinTwo_eq_maassBalanced
    (inverseUV spinPlus spinMinus : ℂ) (xi : {x : ℝ // 0 < x}) :
    ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        inverseUV
        ((Real.tanh (xi : ℝ) : ℂ)⁻¹)
        ((d4BMRindlerRapiditySech (xi : ℝ) : ℂ)⁻¹)
        0 (xi : ℝ) 1
        (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus)
        (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) =
      -(d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ^ (2 : ℕ) / 64 *
        d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet 1
          (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) *
        d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet 1
          (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) := by
  rw [ads4PlebanskiJacobiDoubleBracket_pureSpinTwo_eq]
  simp
  ring

end

end RHTower
