import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflectedScalars
import GaloisForLFunctions.RHTower.ThetaCuspOddCompensationCoefficient
import GaloisForLFunctions.RHTower.ThetaCuspModularCompactTube

/-!
# Literal theta source in compact Lyapunov coordinates

All-order source and reflected jets retain the exact theta mass.
The odd determinant and its leading minor therefore realize the abstract
compact polynomials at every real center.
-/

open Set
namespace RHTower
noncomputable section
set_option maxHeartbeats 2000000

/-- Actual source derivatives at every center retain the exact Lyapunov mass factor. -/
theorem thetaCuspFullSource_jet_eq_lyapunovSourcePolynomial (n : ℕ) (x : ℝ) :
    ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
        MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
          (HTGeometry.modularThetaLyapunovNormalizedSourceJet n) := by
  have hfun : (fun y : ℝ => (thetaCuspFullSource y : ℂ)) =
      fun y => thetaCuspModularODEState HTGeometry.ModularThetaODEState.H y *
        MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j y)
          (HTGeometry.modularThetaLyapunovNormalizedSourceJet 0) := by
    funext y
    rw [ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ,
      HTGeometry.oddCompactSourceJet0_eq]
    simp only [HTGeometry.oddCompactSourceJet0, map_add, map_mul, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X, thetaCuspModularLyapunovState,
      thetaCuspModularSourcePositiveState]
    push_cast
    ring
  rw [← SchwartzMap.iteratedDeriv_ofReal thetaCuspFullSource contDiff_thetaCuspFullSource,
    hfun, HTGeometry.iteratedDeriv_mass_mul_eval_lyapunovSourceJet
      thetaCuspModularLyapunovState hasDerivAt_thetaCuspModularLyapunovState
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
      hasDerivAt_thetaCuspModularMass_lyapunov]

/-- Every native reflected jet is the literal squared mass times its reflected polynomial. -/
theorem thetaCuspNativeReflectionJet_eq_lyapunovPolynomial (n : ℕ) (x : ℝ) :
    (thetaCuspNativeReflectionJet n x : ℂ) =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x^2 *
        MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
          (HTGeometry.oddCompactReflectedJetPolynomial n) := by
  rw [thetaCuspNativeReflectionJet_eq]
  push_cast
  simp_rw [thetaCuspFullSource_jet_eq_lyapunovSourcePolynomial]
  rw [HTGeometry.eval_oddCompactReflectedJetPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem compactState_eq (x : ℝ) :
    (fun j => thetaCuspModularLyapunovState j x) =
      HTGeometry.oddCompactState (-(thetaCuspModularDrift x).re)
        (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) := by
  funext j
  cases j <;> simp [thetaCuspModularLyapunovState, HTGeometry.oddCompactState]

/-- Exact arbitrary-center source realization of the normalized odd determinant. -/
theorem thetaCuspNativeOddHankelThreeDet_eq_compactPolynomial (x : ℝ) :
    thetaCuspNativeOddHankelThreeDet x = Bottcher.completedThetaProfile x^6 *
      HTGeometry.oddCompactDet (-(thetaCuspModularDrift x).re)
        (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) := by
  have hc : (thetaCuspNativeOddHankelThreeDet x : ℂ) =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x^6 *
        MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
          HTGeometry.oddCompactDetPolynomial := by
    unfold thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
    push_cast
    simp_rw [thetaCuspNativeReflectionJet_eq_lyapunovPolynomial]
    rw [HTGeometry.eval_oddCompactDetPolynomial]
    dsimp only
    ring
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile, compactState_eq] at hc
  have hr := congrArg Complex.re hc
  simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, HTGeometry.oddCompactDet] using hr

/-- Exact arbitrary-center source realization of the leading odd minor. -/
theorem thetaCuspNativeOddHeadDet_eq_compactPolynomial (x : ℝ) :
    thetaCuspNativeOddHeadDet x = Bottcher.completedThetaProfile x^4 *
      HTGeometry.oddCompactHead (-(thetaCuspModularDrift x).re)
        (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) := by
  have hc : (thetaCuspNativeOddHeadDet x : ℂ) =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x^4 *
        MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
          HTGeometry.oddCompactHeadPolynomial := by
    unfold thetaCuspNativeOddHeadDet
    push_cast
    simp_rw [thetaCuspNativeReflectionJet_eq_lyapunovPolynomial]
    rw [HTGeometry.eval_oddCompactHeadPolynomial]
    ring
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile, compactState_eq] at hc
  have hr := congrArg Complex.re hc
  simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, HTGeometry.oddCompactHead] using hr

/-- The source value in the nonnegative compact coordinates. -/
theorem thetaCuspFullSource_eq_compactSourceZero (x : ℝ) :
    thetaCuspFullSource x = Bottcher.completedThetaProfile x *
      HTGeometry.oddCompactSourceZero (-(thetaCuspModularDrift x).re)
        (thetaCuspModularGapAmplitude x) := by
  have h := thetaCuspFullSource_jet_eq_lyapunovSourcePolynomial 0 x
  rw [HTGeometry.oddCompactSourceJet0_eq,
    thetaCuspModularODEState_H_eq_completedThetaProfile, compactState_eq] at h
  simp only [HTGeometry.oddCompactSourceJet0, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, HTGeometry.oddCompactState,
    neg_neg, iteratedDeriv_zero] at h
  apply Complex.ofReal_injective
  unfold HTGeometry.oddCompactSourceZero
  push_cast
  convert h using 1 <;> ring

/-- The first source derivative in the same compact coordinates. -/
theorem deriv_thetaCuspFullSource_eq_compactSourceFirst (x : ℝ) :
    deriv thetaCuspFullSource x = Bottcher.completedThetaProfile x *
      HTGeometry.oddCompactSourceFirst (-(thetaCuspModularDrift x).re)
        (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) := by
  have h := thetaCuspFullSource_jet_eq_lyapunovSourcePolynomial 1 x
  rw [HTGeometry.oddCompactSourceJet1_eq,
    thetaCuspModularODEState_H_eq_completedThetaProfile, compactState_eq] at h
  simp only [HTGeometry.oddCompactSourceJet1, map_add, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, HTGeometry.oddCompactState,
    neg_neg, iteratedDeriv_one] at h
  apply Complex.ofReal_injective
  unfold HTGeometry.oddCompactSourceFirst
  push_cast
  convert h using 1 <;> ring


end
end RHTower
