import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPoincareLightConeSecondJetPullback

/-!
# Scalar angular data do not determine the BM-pulled Plebanski source

The existing completed Eisenstein cubic vertex records scalar angular overlap data.  The exact
coordinate Plebanski bracket, after the full BM Hessian pullback, also detects the traceless part
of the horizon Hessian.  This module gives an unconditional local classification witness.

At the physical rapidity-chart point `(tau,xi,sigma)=(0,1,1)`, compare the zero jet with a jet
whose only second derivatives are

`partial_x^(2 : ℕ) f = -1`, `partial_sigma^(2 : ℕ) f = 1`.

Their value, complete first jet, and hyperbolic Laplacian trace agree.  Nevertheless the diagonal
flat Plebanski bracket of the traceless jet is exactly `-sech(1)^(2 : ℕ)/16`, hence nonzero.  Therefore
the scalar angular eigenvalue and scalar triple vertex cannot reconstruct the HC94 source.  The
positive survivor is precise: the angular input must retain a spin-two/traceless-Hessian
polarization (or an equivalent derivative Eisenstein vertex).

`[FALSIFIED] [PAPER-PROVED] [LEAN-PROVED] [HC94] [ANGULAR POLARIZATION NO-GO]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Scalar horizon data visible to a value/first-jet/Laplacian-only angular reduction at
`sigma=1`. -/
structure D4BMHyperbolicScalarTwoJetData where
  value : ℂ
  horizonX : ℂ
  sigma : ℂ
  laplacianTrace : ℂ

/-- Forget the traceless and mixed horizon Hessian components. -/
def d4BMHyperbolicScalarTwoJetDataOfFull
    (J : D4BMFullSecondJet) : D4BMHyperbolicScalarTwoJetData where
  value := J.first.value
  horizonX := J.first.horizonX
  sigma := J.first.sigma
  laplacianTrace := J.horizonXHorizonX + J.sigmaSigma

/-- Zero complete BM two-jet. -/
def d4BMZeroFullSecondJet : D4BMFullSecondJet :=
  { first := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    tauTau := 0
    tauHorizonX := 0
    tauSigma := 0
    tauXi := 0
    horizonXHorizonX := 0
    horizonXSigma := 0
    horizonXXi := 0
    sigmaSigma := 0
    sigmaXi := 0
    xiXi := 0 }

/-- Unit traceless horizon-Hessian direction, invisible to scalar Laplacian data. -/
def d4BMUnitTracelessHorizonHessianSecondJet : D4BMFullSecondJet :=
  { first := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    tauTau := 0
    tauHorizonX := 0
    tauSigma := 0
    tauXi := 0
    horizonXHorizonX := -1
    horizonXSigma := 0
    horizonXXi := 0
    sigmaSigma := 1
    sigmaXi := 0
    xiXi := 0 }

/-- Zero and the traceless witness have exactly the same scalar angular signature. -/
theorem d4BMUnitTracelessHorizonHessian_scalarData_eq_zero :
    d4BMHyperbolicScalarTwoJetDataOfFull
        d4BMUnitTracelessHorizonHessianSecondJet =
      d4BMHyperbolicScalarTwoJetDataOfFull d4BMZeroFullSecondJet := by
  norm_num [d4BMHyperbolicScalarTwoJetDataOfFull,
    d4BMUnitTracelessHorizonHessianSecondJet, d4BMZeroFullSecondJet]

/-- Exact physical-chart evaluation: the diagonal coordinate Plebanski bracket detects the
traceless horizon Hessian by the nonzero coefficient `-sech(1)^(2 : ℕ)/16`. -/
theorem ads4PlebanskiJacobiDoubleBracket_tracelessHorizonWitness_eq :
    ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        0
        ((Real.tanh (1 : ℝ) : ℂ)⁻¹)
        ((d4BMRindlerRapiditySech 1 : ℂ)⁻¹)
        0 1 1
        d4BMUnitTracelessHorizonHessianSecondJet
        d4BMUnitTracelessHorizonHessianSecondJet =
      -(d4BMRindlerRapiditySech 1 : ℂ) ^ (2 : ℕ) / 16 := by
  have haR : Real.tanh (1 : ℝ) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr one_ne_zero)
      (ne_of_gt (Real.cosh_pos 1))
  have ha : (Real.tanh (1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast haR
  have hbR : d4BMRindlerRapiditySech (1 : ℝ) ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.cosh_pos 1))
  have hb : (d4BMRindlerRapiditySech (1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hbR
  have haComplex : Complex.tanh (1 : ℂ) ≠ 0 := by
    simpa using ha
  have haCancel :
      (Complex.tanh (1 : ℂ))⁻¹ * Complex.tanh (1 : ℂ) ^ (2 : ℕ) =
        Complex.tanh (1 : ℂ) := by
    field_simp [haComplex]
  have hbCancel :
      (d4BMRindlerRapiditySech 1 : ℂ)⁻¹ *
          (d4BMRindlerRapiditySech 1 : ℂ) ^ (2 : ℕ) =
        (d4BMRindlerRapiditySech 1 : ℂ) := by
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
    d4BMUnitTracelessHorizonHessianSecondJet,
    ads4PlebanskiJacobiDoubleBracketOnTwoJets]
  rw [haCancel, hbCancel]
  ring

/-- The zero BM two-jet has zero pulled Plebanski self-bracket. -/
theorem ads4PlebanskiJacobiDoubleBracket_zeroFullSecondJet_eq_zero :
    ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        0
        ((Real.tanh (1 : ℝ) : ℂ)⁻¹)
        ((d4BMRindlerRapiditySech 1 : ℂ)⁻¹)
        0 1 1 d4BMZeroFullSecondJet d4BMZeroFullSecondJet = 0 := by
  simp [ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets,
    d4PlebanskiLightConeTwoJetOfBMFormalInv,
    d4BMDirectionalDerivativeOnFullFirstJet,
    d4BMOrderedSecondDirectionalDerivative,
    d4BMZeroFullSecondJet,
    ads4PlebanskiJacobiDoubleBracketOnTwoJets]

/-- Scalar-only angular reconstruction is impossible: equal scalar signatures can have distinct
physical Plebanski source values. -/
theorem not_forall_pulledPlebanskiSelfBracket_eq_of_hyperbolicScalarData_eq :
    ¬ ∀ P Q : D4BMFullSecondJet,
      d4BMHyperbolicScalarTwoJetDataOfFull P =
          d4BMHyperbolicScalarTwoJetDataOfFull Q →
        ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
            0
            ((Real.tanh (1 : ℝ) : ℂ)⁻¹)
            ((d4BMRindlerRapiditySech 1 : ℂ)⁻¹)
            0 1 1 P P =
          ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
            0
            ((Real.tanh (1 : ℝ) : ℂ)⁻¹)
            ((d4BMRindlerRapiditySech 1 : ℂ)⁻¹)
            0 1 1 Q Q := by
  intro hscalar
  have h := hscalar d4BMUnitTracelessHorizonHessianSecondJet d4BMZeroFullSecondJet
    d4BMUnitTracelessHorizonHessian_scalarData_eq_zero
  rw [ads4PlebanskiJacobiDoubleBracket_tracelessHorizonWitness_eq,
    ads4PlebanskiJacobiDoubleBracket_zeroFullSecondJet_eq_zero] at h
  have hbR : d4BMRindlerRapiditySech (1 : ℝ) ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.cosh_pos 1))
  have hb : (d4BMRindlerRapiditySech (1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hbR
  have hsquare : (d4BMRindlerRapiditySech 1 : ℂ) ^ (2 : ℕ) = 0 := by
    calc
      (d4BMRindlerRapiditySech 1 : ℂ) ^ (2 : ℕ) =
          -16 * (-(d4BMRindlerRapiditySech 1 : ℂ) ^ (2 : ℕ) / 16) := by ring
      _ = -16 * 0 := by rw [h]
      _ = 0 := by ring
  exact (pow_ne_zero 2 hb) hsquare

end

end RHTower
