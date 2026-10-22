import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthNativeSeam
import GaloisForLFunctions.RHTower.PrimeArchThetaModularDifferentialClosure

/-!
# Arbitrary-basepoint modular closure of theta D1

The actual raw rank-three reflected eighth curvature is exactly the universal polynomial obtained
by iterating the four-state modular theta Lie derivative.  This identifies the remaining compact
D1 burden with positivity of one explicit multivariate polynomial along the physical modular
trajectory, including every reflection-odd jet omitted by the seam specialization.
-/

namespace RHTower

noncomputable section

/-- Raw theta D1 is the universal arbitrary-basepoint modular polynomial. -/
theorem ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular
    (x : ℝ) :
    (thetaCuspFullSourceReflectionEighthHankelCurvature x : ℂ) =
      thetaCuspReflectedEighthGeneralModularValue x := by
  simpa [thetaCuspFullSourceReflectionEighthHankelCurvature] using
    thetaCuspFullSource_reflectedEighthHankel_eq_generalModular x

/-- Universal modular D1 is real-valued on the actual theta trajectory. -/
theorem thetaCuspReflectedEighthGeneralModularValue_im_eq_zero (x : ℝ) :
    (thetaCuspReflectedEighthGeneralModularValue x).im = 0 := by
  rw [← ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular]
  simp

/-- Real part of universal modular D1 is the literal raw curvature. -/
theorem thetaCuspReflectedEighthGeneralModularValue_re_eq (x : ℝ) :
    (thetaCuspReflectedEighthGeneralModularValue x).re =
      thetaCuspFullSourceReflectionEighthHankelCurvature x := by
  rw [← ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular]
  simp

/-- Exact positive-cone formulation of the remaining arbitrary-basepoint modular problem. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_generalModular
    (x : ℝ) :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature x ↔
      0 < (thetaCuspReflectedEighthGeneralModularValue x).re := by
  rw [thetaCuspReflectedEighthGeneralModularValue_re_eq]

/-- The mass-normalized modular D1 remains real-valued on the physical trajectory. -/
theorem thetaCuspReflectedEighthNormalizedModularValue_im_eq_zero (x : ℝ) :
    (thetaCuspReflectedEighthNormalizedModularValue x).im = 0 := by
  have hfac := congrArg Complex.im
    (thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_normalized x)
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile] at hfac
  rw [← Complex.ofReal_pow] at hfac
  simp only [Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero] at hfac
  have hm : 0 < Bottcher.completedThetaProfile x ^ (6 : ℕ) :=
    pow_pos (thetaCuspCompletedThetaProfile_pos x) 6
  have hzero := thetaCuspReflectedEighthGeneralModularValue_im_eq_zero x
  rw [hzero] at hfac
  nlinarith

/-- The genuine three-state D1 value is real on the physical theta orbit. -/
theorem thetaCuspReflectedEighthReducedModularValue_im_eq_zero (x : ℝ) :
    (thetaCuspReflectedEighthReducedModularValue x).im = 0 := by
  rw [thetaCuspReflectedEighthReducedModularValue_eq_normalized]
  exact thetaCuspReflectedEighthNormalizedModularValue_im_eq_zero x

/-- The Lyapunov-chart D1 value is real on the physical theta orbit. -/
theorem thetaCuspReflectedEighthLyapunovModularValue_im_eq_zero (x : ℝ) :
    (thetaCuspReflectedEighthLyapunovModularValue x).im = 0 := by
  rw [thetaCuspReflectedEighthLyapunovModularValue_eq_normalized]
  exact thetaCuspReflectedEighthNormalizedModularValue_im_eq_zero x

/-- The positive-chamber D1 value is real on the physical theta orbit. -/
theorem thetaCuspReflectedEighthPositiveModularValue_im_eq_zero (x : ℝ) :
    (thetaCuspReflectedEighthPositiveModularValue x).im = 0 := by
  rw [thetaCuspReflectedEighthPositiveModularValue_eq_normalized]
  exact thetaCuspReflectedEighthNormalizedModularValue_im_eq_zero x

/-- Source-positive D1 is real-valued on physical theta orbit. -/
theorem thetaCuspReflectedEighthSourcePositiveModularValue_im_eq_zero (x : ℝ) :
    (thetaCuspReflectedEighthSourcePositiveModularValue x).im = 0 := by
  rw [thetaCuspReflectedEighthSourcePositiveModularValue_eq_normalized]
  exact thetaCuspReflectedEighthNormalizedModularValue_im_eq_zero x

/-- Raw theta D1 is positive mass to the sixth times the normalized three-state value. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_eq_mass_pow_six_mul_normalized_re
    (x : ℝ) :
    thetaCuspFullSourceReflectionEighthHankelCurvature x =
      Bottcher.completedThetaProfile x ^ (6 : ℕ) *
        (thetaCuspReflectedEighthNormalizedModularValue x).re := by
  have hfac := congrArg Complex.re
    (thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_normalized x)
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile] at hfac
  rw [thetaCuspReflectedEighthGeneralModularValue_re_eq] at hfac
  have hpRe : (((Bottcher.completedThetaProfile x : ℂ) ^ (6 : ℕ)).re) =
      Bottcher.completedThetaProfile x ^ (6 : ℕ) := by norm_cast
  have hpIm : (((Bottcher.completedThetaProfile x : ℂ) ^ (6 : ℕ)).im) = 0 := by
    change ((Bottcher.completedThetaProfile x : ℂ) ^ (6 : ℕ)).im =
      (((Bottcher.completedThetaProfile x ^ (6 : ℕ) : ℝ) : ℂ)).im
    exact congrArg Complex.im
      (Complex.ofReal_pow (Bottcher.completedThetaProfile x) 6).symm
  rw [Complex.mul_re, hpRe, hpIm, zero_mul, sub_zero] at hfac
  exact hfac

/-- Positive raw D1 is exactly positivity of the normalized three-state modular polynomial. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_normalizedModular
    (x : ℝ) :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature x ↔
      0 < (thetaCuspReflectedEighthNormalizedModularValue x).re := by
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_eq_mass_pow_six_mul_normalized_re]
  exact mul_pos_iff_of_pos_left (pow_pos (thetaCuspCompletedThetaProfile_pos x) 6)

/-- The remaining arbitrary-basepoint D1 burden is exactly a three-variable polynomial sign. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_reducedModular
    (x : ℝ) :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature x ↔
      0 < (thetaCuspReflectedEighthReducedModularValue x).re := by
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_normalizedModular,
    thetaCuspReflectedEighthReducedModularValue_eq_normalized]

/-- Remaining physical D1 burden is exactly positivity of one polynomial in `(S,A,W)`. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_lyapunovModular
    (x : ℝ) :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature x ↔
      0 < (thetaCuspReflectedEighthLyapunovModularValue x).re := by
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_normalizedModular,
    thetaCuspReflectedEighthLyapunovModularValue_eq_normalized]

/-- Remaining physical D1 burden is positivity of one polynomial on the strict positive orthant. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_positiveModular
    (x : ℝ) :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature x ↔
      0 < (thetaCuspReflectedEighthPositiveModularValue x).re := by
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_normalizedModular,
    thetaCuspReflectedEighthPositiveModularValue_eq_normalized]

/-- Remaining physical D1 burden is positivity of source-positive `(U,B,Q)` polynomial. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_sourcePositiveModular
    (x : ℝ) :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature x ↔
      0 < (thetaCuspReflectedEighthSourcePositiveModularValue x).re := by
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_normalizedModular,
    thetaCuspReflectedEighthSourcePositiveModularValue_eq_normalized]

/-- Physical positive half-orbit lies in source-positive chamber, with reconstructed gap positive. -/
theorem thetaCuspModularSourcePositiveState_mem_strictPhysicalChamber
    {x : ℝ} (hx : 0 < x) :
    (∀ i, 0 < (thetaCuspModularSourcePositiveState i x).re) ∧
      0 < (MvPolynomial.eval
        (fun j => thetaCuspModularSourcePositiveState j x)
          HTGeometry.modularThetaSourcePositiveGap).re := by
  refine ⟨thetaCuspModularSourcePositiveState_re_pos hx, ?_⟩
  rw [eval_modularThetaSourcePositiveGap_eq_gapAmplitude]
  simpa using thetaCuspModularGapAmplitude_pos x

/-- On the positive half-line the Lyapunov state lies in the strict physical chamber:
negative drift, positive gap, positive transverse shear, and the diagonal source cone. -/
theorem thetaCuspModularLyapunovState_mem_strictPhysicalChamber
    {x : ℝ} (hx : 0 < x) :
    (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.S x).re < 0 ∧
      0 < (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.A x).re ∧
      0 < (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.W x).re ∧
      18 <
        2 * (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.S x).re ^ (2 : ℕ) +
          3 * (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.A x).re ∧
      -(1 / 3 : ℝ) *
          (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.S x).re <
        (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.W x).re := by
  simp only [thetaCuspModularLyapunovState, Complex.ofReal_re]
  refine ⟨thetaCuspModularDrift_re_neg_of_pos hx,
    thetaCuspModularGapAmplitude_pos x,
    thetaCuspModularTransverseShear_pos_of_pos hx, ?_,
    neg_one_third_mul_thetaCuspModularDrift_re_lt_transverseShear hx⟩
  have hcone := thetaCuspModularSourceDriftCone_pos x
  unfold thetaCuspModularGapAmplitude
  nlinarith

/-- The general polynomial specializes to the independently eliminated modular seam value. -/
theorem thetaCuspReflectedEighthGeneralModularValue_zero_eq_seam :
    thetaCuspReflectedEighthGeneralModularValue 0 =
      (thetaCuspReflectedEighthSeamModularClosureValue : ℂ) := by
  rw [← ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular,
    thetaCuspFullSourceReflectionEighthHankelCurvature_zero_eq_modularClosure]

/-- The universal modular polynomial is strict at the actual self-dual state. -/
theorem thetaCuspReflectedEighthGeneralModularValue_zero_re_pos :
    0 < (thetaCuspReflectedEighthGeneralModularValue 0).re := by
  rw [thetaCuspReflectedEighthGeneralModularValue_re_eq]
  exact thetaCuspFullSourceReflectionEighthHankelCurvature_zero_pos

end


end RHTower
