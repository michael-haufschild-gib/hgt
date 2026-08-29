import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMXiPlebanskiPolarizedSourceExistence

/-!
# Balanced spin-two sector of the BM-pulled Plebanski source

The complete coordinate pullback of Plebanski Eq. (63) detects more than the scalar hyperbolic
two-jet.  This module extracts the exact local helicity pairing at `sigma = 1`.

For a pure traceless horizon Hessian with vanishing value and first jet, write

`spinPlus  = f_xx - f_sigma,sigma + 2 i f_x,sigma`,

`spinMinus = f_xx - f_sigma,sigma - 2 i f_x,sigma`.

These two components are recovered exactly from the constructed jet, while its scalar two-jet
data agree with the zero jet.  Nevertheless, at every positive physical rapidity, its diagonal
BM-pulled Plebanski bracket is

`-sech(xi)^2 * spinPlus * spinMinus / 64`.

Thus the local angular source is balanced: it pairs one `+2` component with one `-2` component,
and no scalar Laplacian signature can recover the product.  Because the first jet vanishes, the
displayed components also equal the covariant traceless Hessian components at the chart point;
the theorem makes no claim that a generic separated mode has vanishing connection corrections.
It identifies the exact tensor word whose modular Eisenstein projection is the next HC94 input.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [BALANCED SPIN TWO]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Pure traceless horizon Hessian with prescribed local `+2` and `-2` components. -/
def d4BMPureSpinTwoHorizonHessianSecondJet (spinPlus spinMinus : ℂ) :
    D4BMFullSecondJet :=
  { first := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    tauTau := 0
    tauHorizonX := 0
    tauSigma := 0
    tauXi := 0
    horizonXHorizonX := (spinPlus + spinMinus) / 4
    horizonXSigma := (spinPlus - spinMinus) / (4 * Complex.I)
    horizonXXi := 0
    sigmaSigma := -(spinPlus + spinMinus) / 4
    sigmaXi := 0
    xiXi := 0 }

/-- Local `+2` component of the horizon Hessian at `sigma = 1`. -/
def d4BMHorizonSpinPlus (J : D4BMFullSecondJet) : ℂ :=
  J.horizonXHorizonX - J.sigmaSigma + 2 * Complex.I * J.horizonXSigma

/-- Local `-2` component of the horizon Hessian at `sigma = 1`. -/
def d4BMHorizonSpinMinus (J : D4BMFullSecondJet) : ℂ :=
  J.horizonXHorizonX - J.sigmaSigma - 2 * Complex.I * J.horizonXSigma

/-- The pure spin-two jet recovers its prescribed `+2` component. -/
@[simp] theorem d4BMHorizonSpinPlus_pureSpinTwo (spinPlus spinMinus : ℂ) :
    d4BMHorizonSpinPlus (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) =
      spinPlus := by
  simp [d4BMHorizonSpinPlus, d4BMPureSpinTwoHorizonHessianSecondJet]
  field_simp [Complex.I_ne_zero]
  ring

/-- The pure spin-two jet recovers its prescribed `-2` component. -/
@[simp] theorem d4BMHorizonSpinMinus_pureSpinTwo (spinPlus spinMinus : ℂ) :
    d4BMHorizonSpinMinus (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) =
      spinMinus := by
  simp [d4BMHorizonSpinMinus, d4BMPureSpinTwoHorizonHessianSecondJet]
  field_simp [Complex.I_ne_zero]
  ring

/-- Every pure spin-two jet is invisible to value/first-jet/Laplacian scalar data. -/
theorem d4BMPureSpinTwoHorizonHessian_scalarData_eq_zero
    (spinPlus spinMinus : ℂ) :
    d4BMHyperbolicScalarTwoJetDataOfFull
        (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) =
      d4BMHyperbolicScalarTwoJetDataOfFull d4BMZeroFullSecondJet := by
  simp [d4BMHyperbolicScalarTwoJetDataOfFull,
    d4BMPureSpinTwoHorizonHessianSecondJet, d4BMZeroFullSecondJet]
  ring

/-- Exact balanced-spin classification of the diagonal BM-pulled Eq. (63) source at `sigma = 1`.
The result is independent of the inverse-UV scale and holds at every positive rapidity. -/
theorem ads4PlebanskiJacobiDoubleBracket_pureSpinTwo_eq
    (inverseUV spinPlus spinMinus : ℂ) (xi : {x : ℝ // 0 < x}) :
    ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        inverseUV
        ((Real.tanh (xi : ℝ) : ℂ)⁻¹)
        ((d4BMRindlerRapiditySech (xi : ℝ) : ℂ)⁻¹)
        0 (xi : ℝ) 1
        (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus)
        (d4BMPureSpinTwoHorizonHessianSecondJet spinPlus spinMinus) =
      -(d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ^ 2 * spinPlus * spinMinus / 64 := by
  have haR : Real.tanh (xi : ℝ) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr (ne_of_gt xi.property))
      (ne_of_gt (Real.cosh_pos xi))
  have ha : (Real.tanh (xi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast haR
  have hbR : d4BMRindlerRapiditySech (xi : ℝ) ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.cosh_pos xi))
  have hb : (d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hbR
  have haComplex : Complex.tanh ((xi : ℝ) : ℂ) ≠ 0 := by
    simpa using ha
  have haCancel :
      (Complex.tanh ((xi : ℝ) : ℂ))⁻¹ * Complex.tanh ((xi : ℝ) : ℂ) ^ 2 =
        Complex.tanh ((xi : ℝ) : ℂ) := by
    field_simp [haComplex]
  have hbCancel :
      (d4BMRindlerRapiditySech (xi : ℝ) : ℂ)⁻¹ *
          (d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ^ 2 =
        (d4BMRindlerRapiditySech (xi : ℝ) : ℂ) := by
    field_simp [hb]
  simp [ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets,
    d4PlebanskiLightConeTwoJetOfBMFormalInv,
    d4PoincareLightConeUVectorFieldFirstJetOnBMFormalInv,
    d4PoincareLightConeWVectorFieldFirstJetOnBMFormalInv,
    d4BMVectorFieldFirstJetLinearCombination,
    d4BMFullFirstJetLinearCombination,
    d4BMDirectionalDerivativeOnFullFirstJet,
    d4BMOrderedSecondDirectionalDerivative,
    d4PoincareTimeVectorFieldFirstJetOnBMFormalInv,
    d4PoincareHorizonYVectorFieldFirstJetOnBMFormalInv,
    d4PoincareRadialVectorFieldFirstJetOnBMFormalInv,
    d4PoincareHorizonXVectorFieldFirstJetOnBM,
    d4BMPureSpinTwoHorizonHessianSecondJet,
    ads4PlebanskiJacobiDoubleBracketOnTwoJets]
  rw [haCancel, hbCancel]
  field_simp [Complex.I_ne_zero]
  simp only [pow_two]
  rw [Complex.I_mul_I]
  ring

/-- The balanced spin pair is genuinely active at every positive rapidity. -/
theorem ads4PlebanskiJacobiDoubleBracket_unitPureSpinTwo_ne_zero
    (inverseUV : ℂ) (xi : {x : ℝ // 0 < x}) :
    ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        inverseUV
        ((Real.tanh (xi : ℝ) : ℂ)⁻¹)
        ((d4BMRindlerRapiditySech (xi : ℝ) : ℂ)⁻¹)
        0 (xi : ℝ) 1
        (d4BMPureSpinTwoHorizonHessianSecondJet 1 1)
        (d4BMPureSpinTwoHorizonHessianSecondJet 1 1) ≠ 0 := by
  rw [ads4PlebanskiJacobiDoubleBracket_pureSpinTwo_eq]
  have hbR : d4BMRindlerRapiditySech (xi : ℝ) ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.cosh_pos xi))
  have hb : (d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hbR
  simpa only [mul_one] using
    (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hb)) (by norm_num) :
      -(d4BMRindlerRapiditySech (xi : ℝ) : ℂ) ^ 2 / 64 ≠ 0)

end

end RHTower
