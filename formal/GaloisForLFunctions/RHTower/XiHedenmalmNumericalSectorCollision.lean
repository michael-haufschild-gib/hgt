import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision

/-!
# Hedenmalm multiplicity--orientation product criterion

The reciprocal Xi operator is diagonal on the exact divisor-copy carrier.  At a simple Xi zero,
the evaluated Hedenmalm eigenfunction is a nonzero eigenvector, so its numerical value records the
imaginary part of the reciprocal centered spectral point.  Functional-equation reflection supplies
the opposite eigenvalue.  A one-sided upper numerical-sector condition on both vectors therefore
forces that spectral point to be real.

At a multiple zero, however, the first Hedenmalm evaluation vector is exactly zero, and the same
numerical value vanishes automatically.  The sector condition is consequently blind to precisely
the fibers seen by local Jordan normality.  Right-half local Jordan normality and the numerical
sector are complementary constraints; neither contains RH alone, while their conjunction is
equivalent to RH.
-/

open Complex

noncomputable section

namespace RHTower

/-- Numerical value of the reciprocal Xi operator on one evaluated Hedenmalm eigenfunction. -/
def xiThetaReciprocalNumericalValue (q : XiZeroCopy) : ℂ :=
  inner ℂ (xiThetaEigenEvaluationLp q)
    (xiReciprocalOperator (xiThetaEigenEvaluationLp q))

/-- Orientation-only condition: every evaluated Hedenmalm mode lies in the closed upper numerical
sector of the reciprocal Xi operator.  Multiple-zero modes are zero and hence invisible here. -/
def XiThetaReciprocalNumericalUpperSector : Prop :=
  ∀ q : XiZeroCopy, 0 ≤ (xiThetaReciprocalNumericalValue q).im

/-- The reciprocal operator eigenvector identity needs only simplicity at this one divisor point,
not global Xi simplicity. -/
theorem xiReciprocalOperator_thetaEigen_of_deriv_ne_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) :
    xiReciprocalOperator (xiThetaEigenEvaluationLp q) =
      (xiSpectralPoint q)⁻¹ • xiThetaEigenEvaluationLp q := by
  rw [xiThetaEigenEvaluationLp_eq_smul_single_of_deriv_ne_zero q hderiv,
    map_smul, xiReciprocalOperator_single, smul_smul, smul_smul]
  congr 1
  ring

/-- At a locally simple divisor point, the numerical value is the reciprocal spectral coordinate
times the squared norm of the nonzero Hedenmalm evaluation vector. -/
theorem xiThetaReciprocalNumericalValue_eq_of_deriv_ne_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) :
    xiThetaReciprocalNumericalValue q =
      (xiSpectralPoint q)⁻¹ *
        Complex.ofReal (‖xiThetaEigenEvaluationLp q‖ ^ 2) := by
  rw [xiThetaReciprocalNumericalValue,
    xiReciprocalOperator_thetaEigen_of_deriv_ne_zero q hderiv,
    inner_smul_right, inner_self_eq_norm_sq_to_K]
  congr 1
  norm_cast

/-- Imaginary numerical value at one locally simple divisor point. -/
theorem xiThetaReciprocalNumericalValue_im_eq_of_deriv_ne_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) :
    (xiThetaReciprocalNumericalValue q).im =
      (xiSpectralPoint q)⁻¹.im * ‖xiThetaEigenEvaluationLp q‖ ^ 2 := by
  rw [xiThetaReciprocalNumericalValue_eq_of_deriv_ne_zero q hderiv, mul_im]
  have hre : (Complex.ofReal (‖xiThetaEigenEvaluationLp q‖ ^ 2)).re =
      ‖xiThetaEigenEvaluationLp q‖ ^ 2 := Complex.ofReal_re _
  have him : (Complex.ofReal (‖xiThetaEigenEvaluationLp q‖ ^ 2)).im = 0 :=
    Complex.ofReal_im _
  rw [hre, him]
  ring

/-- A locally simple Xi divisor point produces a genuinely nonzero Hedenmalm evaluation vector. -/
theorem xiThetaEigenEvaluationLp_ne_zero_of_deriv_ne_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) :
    xiThetaEigenEvaluationLp q ≠ 0 := by
  intro hzero
  have hq := congrArg
    (fun v : lp (fun _ : XiZeroCopy => ℂ) 2 => v q) hzero
  change xiThetaEigenEvaluationLp q q = 0 at hq
  rw [xiThetaEigenEvaluationLp_apply, xiThetaEigenFourier_self] at hq
  exact (mul_ne_zero I_ne_zero hderiv) hq

/-- **Multiplicity blindness of the numerical sector.**  At a multiple Xi zero the first
Hedenmalm evaluation vector, and therefore its reciprocal numerical value, is exactly zero. -/
theorem xiThetaReciprocalNumericalValue_eq_zero_of_deriv_eq_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) = 0) :
    xiThetaReciprocalNumericalValue q = 0 := by
  rw [xiThetaReciprocalNumericalValue,
    xiThetaEigenEvaluationLp_eq_zero_of_deriv_eq_zero q hderiv,
    map_zero, inner_zero_right]

/-- Simplicity at one Xi divisor point is preserved by functional-equation reflection. -/
theorem deriv_XiC_reflected_spectralPoint_ne_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) :
    deriv XiC (xiSpectralPoint (xiZeroCopyReflectEquiv q)) ≠ 0 := by
  have hm : xiSupportMultiplicity q.1 = 1 :=
    xiDivisorMultiplicity_eq_one_of_deriv_ne_zero q.1 (by
      simpa only [xiSpectralPoint_eq_support] using hderiv)
  have hmref : xiSupportMultiplicity (xiZeroCopyReflectEquiv q).1 = 1 := by
    change Int.toNat ((MeromorphicOn.divisor xi Set.univ)
      (1 - (q.1 : ℂ))) = 1
    rw [xi_divisor_one_sub]
    exact hm
  have hvalue :=
    (xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one
      (xiZeroCopyReflectEquiv q).1).mpr hmref
  rw [xiThetaEigenFourier_self] at hvalue
  simpa only [xiSpectralPoint_eq_support] using
    (fun hzero => hvalue (by rw [hzero, mul_zero]))

/-- The upper numerical-sector condition forces the centered spectral coordinate of every locally
simple Xi zero to be real.  Reflection supplies the opposite reciprocal eigenvalue, so the two
one-sided inequalities squeeze its imaginary part to zero. -/
theorem xiSpectralPoint_real_of_numericalUpperSector_of_deriv_ne_zero
    (hupper : XiThetaReciprocalNumericalUpperSector)
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) :
    ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) := by
  let qr : XiZeroCopy := xiZeroCopyReflectEquiv q
  have hderivR : deriv XiC (xiSpectralPoint qr) ≠ 0 :=
    deriv_XiC_reflected_spectralPoint_ne_zero q hderiv
  have hq := hupper q
  have hr := hupper qr
  rw [xiThetaReciprocalNumericalValue_im_eq_of_deriv_ne_zero q hderiv] at hq
  rw [xiThetaReciprocalNumericalValue_im_eq_of_deriv_ne_zero qr hderivR,
    xiSpectralPoint_reflect q] at hr
  have hnq : 0 < ‖xiThetaEigenEvaluationLp q‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr
      (xiThetaEigenEvaluationLp_ne_zero_of_deriv_ne_zero q hderiv))
  have hnr : 0 < ‖xiThetaEigenEvaluationLp qr‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr
      (xiThetaEigenEvaluationLp_ne_zero_of_deriv_ne_zero qr hderivR))
  have himInv : (xiSpectralPoint q)⁻¹.im = 0 := by
    have hr' : 0 ≤ -(xiSpectralPoint q)⁻¹.im *
        ‖xiThetaEigenEvaluationLp qr‖ ^ 2 := by
      simpa using hr
    nlinarith
  have hnorm : 0 < normSq (xiSpectralPoint q) :=
    normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  rw [inv_im] at himInv
  have him : (xiSpectralPoint q).im = 0 := by
    apply neg_eq_zero.mp
    exact (div_eq_zero_iff.mp himInv).resolve_right hnorm.ne'
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext <;> simp [him]

/-- A support multiplicity of one gives a nonzero XiC derivative at the corresponding centered
spectral point. -/
theorem deriv_XiC_spectralPointSupport_ne_zero_of_multiplicity_one
    (rho : XiDivisorSupport) (hm : xiSupportMultiplicity rho = 1) :
    deriv XiC (xiSpectralPointSupport rho) ≠ 0 := by
  have hvalue :=
    (xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one rho).mpr hm
  rw [xiThetaEigenFourier_self] at hvalue
  intro hzero
  exact hvalue (by rw [hzero, mul_zero])

/-- **Multiplicity--orientation collision.**  Right-half local Jordan normality makes every
hypothetical right-half Xi zero simple.  The upper numerical sector then makes its centered
spectral point real, contradicting strict right-half location. -/
theorem riemannHypothesis_of_rightHalfLocalJordanNormal_of_numericalUpperSector
    (hnormal : XiRightHalfLocalJordanNormal)
    (hupper : XiThetaReciprocalNumericalUpperSector) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hsnormal : XiLocalJordanNormal support := by
    apply hnormal support
    simpa only [support] using hrho
  have hm : xiSupportMultiplicity support = 1 :=
    (xiLocalJordanNormal_iff_multiplicity_one support).mp hsnormal
  let q : XiZeroCopy :=
    ⟨support, ⟨0, by change 0 < xiSupportMultiplicity support; omega⟩⟩
  have hderiv : deriv XiC (xiSpectralPoint q) ≠ 0 := by
    simpa only [q, xiSpectralPoint_eq_support] using
      deriv_XiC_spectralPointSupport_ne_zero_of_multiplicity_one support hm
  obtain ⟨t, ht⟩ :=
    xiSpectralPoint_real_of_numericalUpperSector_of_deriv_ne_zero hupper q hderiv
  have him := congrArg Complex.im ht
  have hrhoHalf : rho.re = 1 / 2 := by
    dsimp only [q, support, xiSpectralPoint] at him
    simp [mul_im] at him
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hrhoHalf

/-- RH makes the upper numerical-sector condition true.  At a multiple zero the theta vector is
zero; at a simple zero the reciprocal spectral coordinate is real. -/
theorem xiThetaReciprocalNumericalUpperSector_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiThetaReciprocalNumericalUpperSector := by
  intro q
  by_cases hderiv : deriv XiC (xiSpectralPoint q) = 0
  · rw [xiThetaReciprocalNumericalValue_eq_zero_of_deriv_eq_zero q hderiv]
    simp
  · rw [xiThetaReciprocalNumericalValue_im_eq_of_deriv_ne_zero q hderiv]
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [ht]
    simp

/-- Under RH there are no right-half Xi divisor points, so right-half local Jordan normality holds
without any global simplicity assumption. -/
theorem xiRightHalfLocalJordanNormal_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiRightHalfLocalJordanNormal := by
  intro rho hrho
  have hhalf := xi_divisor_support_re_eq_half_of_rh hRH rho
  exact (ne_of_gt (mem_rightHalf.mp hrho) hhalf).elim

/-- **Exact constraint times orientation factorization of RH.**  The multiplicity constraint is
right-half local Jordan normality; the complementary orientation constraint is the one-sided
numerical sector on Hedenmalm evaluations.  Each condition is blind to the defect seen by the
other. -/
theorem riemannHypothesis_iff_rightHalfLocalJordanNormal_and_numericalUpperSector :
    RiemannHypothesis ↔
      XiRightHalfLocalJordanNormal ∧ XiThetaReciprocalNumericalUpperSector := by
  constructor
  · intro hRH
    exact ⟨xiRightHalfLocalJordanNormal_of_riemannHypothesis hRH,
      xiThetaReciprocalNumericalUpperSector_of_riemannHypothesis hRH⟩
  · rintro ⟨hnormal, hupper⟩
    exact riemannHypothesis_of_rightHalfLocalJordanNormal_of_numericalUpperSector
      hnormal hupper

/-- A source-to-source closure provider for simplicity, together with the numerical orientation
sector, already forces RH. -/
theorem riemannHypothesis_of_xiContinuedCauchyToHedenmalmClosure_of_numericalUpperSector
    (hclosure : XiContinuedCauchyToHedenmalmClosure)
    (hupper : XiThetaReciprocalNumericalUpperSector) :
    RiemannHypothesis := by
  have hsimple : XiZerosSimple :=
    xiContinuedCauchyToHedenmalmClosure_iff_simple.mp hclosure
  apply riemannHypothesis_of_rightHalfLocalJordanNormal_of_numericalUpperSector
    (hupper := hupper)
  intro rho _hrho
  apply (xiLocalJordanNormal_iff_multiplicity_one rho).mpr
  exact xiDivisorMultiplicity_eq_one_of_simple hsimple rho

end RHTower
