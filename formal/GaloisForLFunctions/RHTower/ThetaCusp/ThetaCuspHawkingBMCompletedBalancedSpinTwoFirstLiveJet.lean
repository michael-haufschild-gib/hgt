import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompletedBalancedSpinTwoAmputationOrderNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinScalarLandingNoGo
import GaloisForLFunctions.RHTower.XiWeilArithmeticGram

/-!
# First live completed balanced spin-two jet

The exact amputation threshold is `2m`, where `m` is the support multiplicity of
the projecting Xi zero.  This module proves that this first permitted jet is
always nonzero at the actual repeated Eisenstein leg `s=2` (`u=3/2`).

At this leg the two shifted completed factors become `XiC(z-3I)` and
`XiC(-z-3I)`, both in the unconditional zero-free half-plane.  The remaining
Bochner coefficient factors as

`(4 z^(2 : ℕ) + 1)(4 z^(2 : ℕ) + 25)/32`.

Its four possible roots lie outside the strict centered Xi strip.  Thus the
angular source is unconditionally active on every Xi copy.  Full HB incidence
is consequently equivalent to one explicit value of the radial/left-QNM scale;
no angular existence premise remains.  This equivalence does not construct the
physical radial scale and cannot be used as a target-fitted RH argument.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Actual repeated positive Eisenstein leg `s=2`, in centered coordinates. -/
def d4BMActualRepeatedEisensteinCenteredParameter : ℂ := 3 / 2

theorem d4BMActualRepeatedEisensteinCenteredParameter_eq_parameterTwo :
    d4BMActualRepeatedEisensteinCenteredParameter =
      d4BMActualCenteredEisensteinParameter
        d4BMEisensteinAbsoluteConvergenceParameterTwo := by
  norm_num [d4BMActualRepeatedEisensteinCenteredParameter,
    d4BMActualCenteredEisensteinParameter,
    d4BMEisensteinAbsoluteConvergenceParameterTwo]

theorem thetaCuspHawkingCompletedEisensteinXiFactor_actualRepeated_plus_projecting_ne_zero
    (q : XiZeroCopy) :
    thetaCuspHawkingCompletedEisensteinXiFactor
        (2 * d4BMActualRepeatedEisensteinCenteredParameter +
          Complex.I * xiSpectralPoint q) ≠ 0 := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
    d4BMActualRepeatedEisensteinCenteredParameter
  rw [show -Complex.I * (2 * (3 / 2 : ℂ) + Complex.I * xiSpectralPoint q) =
      xiSpectralPoint q - 3 * Complex.I by
    calc
      -Complex.I * (2 * (3 / 2 : ℂ) + Complex.I * xiSpectralPoint q) =
          -3 * Complex.I - (Complex.I * Complex.I) * xiSpectralPoint q := by ring
      _ = xiSpectralPoint q - 3 * Complex.I := by rw [Complex.I_mul_I]; ring]
  apply XiC_ne_zero_of_im_lt_neg_half
  have hz := xiSpectralPoint_im_mem_openHalf q
  norm_num [Complex.sub_im, Complex.mul_im]
  linarith

theorem thetaCuspHawkingCompletedEisensteinXiFactor_actualRepeated_minus_projecting_ne_zero
    (q : XiZeroCopy) :
    thetaCuspHawkingCompletedEisensteinXiFactor
        (2 * d4BMActualRepeatedEisensteinCenteredParameter -
          Complex.I * xiSpectralPoint q) ≠ 0 := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
    d4BMActualRepeatedEisensteinCenteredParameter
  rw [show -Complex.I * (2 * (3 / 2 : ℂ) - Complex.I * xiSpectralPoint q) =
      -xiSpectralPoint q - 3 * Complex.I by
    calc
      -Complex.I * (2 * (3 / 2 : ℂ) - Complex.I * xiSpectralPoint q) =
          -3 * Complex.I + (Complex.I * Complex.I) * xiSpectralPoint q := by ring
      _ = -xiSpectralPoint q - 3 * Complex.I := by rw [Complex.I_mul_I]; ring]
  apply XiC_ne_zero_of_im_lt_neg_half
  have hz := xiSpectralPoint_im_mem_openHalf q
  norm_num [Complex.sub_im, Complex.neg_im, Complex.mul_im]
  linarith

/-- At the actual repeated leg, the Bochner coefficient splits into four exterior-strip roots. -/
theorem thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_actualRepeated_projecting_factorization
    (z : ℂ) :
    thetaCuspHawkingBalancedSpinTwoBochnerCoefficient
        d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * z) =
      ((4 * z ^ (2 : ℕ) + 1) * (4 * z ^ (2 : ℕ) + 25)) / 32 := by
  have hleft :
      thetaCuspHawkingEisensteinGeometricEigenvalue
          d4BMActualRepeatedEisensteinCenteredParameter = 2 := by
    norm_num [thetaCuspHawkingEisensteinGeometricEigenvalue,
      d4BMActualRepeatedEisensteinCenteredParameter]
  have hright :
      thetaCuspHawkingEisensteinGeometricEigenvalue (Complex.I * z) =
        -z ^ (2 : ℕ) - 1 / 4 := by
    unfold thetaCuspHawkingEisensteinGeometricEigenvalue
    rw [show (Complex.I * z) ^ (2 : ℕ) = -z ^ (2 : ℕ) by
      calc
        (Complex.I * z) ^ (2 : ℕ) = (Complex.I * Complex.I) * z ^ (2 : ℕ) := by ring
        _ = -z ^ (2 : ℕ) := by rw [Complex.I_mul_I]; ring]
  unfold thetaCuspHawkingBalancedSpinTwoBochnerCoefficient
  rw [hleft, hright]
  simp [d4BMHyperbolicBalancedSpinTwoBochnerCoefficient,
    d4BMHyperbolicDiagonalGradientShift]
  ring

theorem four_mul_xiSpectralPoint_sq_add_one_ne_zero (q : XiZeroCopy) :
    4 * xiSpectralPoint q ^ (2 : ℕ) + 1 ≠ 0 := by
  intro h
  have hfactor :
      (2 * xiSpectralPoint q - Complex.I) *
          (2 * xiSpectralPoint q + Complex.I) = 0 := by
    rw [show (2 * xiSpectralPoint q - Complex.I) *
        (2 * xiSpectralPoint q + Complex.I) =
          4 * xiSpectralPoint q ^ (2 : ℕ) + 1 by
      calc
        (2 * xiSpectralPoint q - Complex.I) *
            (2 * xiSpectralPoint q + Complex.I) =
          4 * xiSpectralPoint q ^ (2 : ℕ) - Complex.I * Complex.I := by ring
        _ = 4 * xiSpectralPoint q ^ (2 : ℕ) + 1 := by rw [Complex.I_mul_I]; ring]
    exact h
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · have him := congrArg Complex.im hminus
    have hz := xiSpectralPoint_im_mem_openHalf q
    norm_num at him
    linarith
  · have him := congrArg Complex.im hplus
    have hz := xiSpectralPoint_im_mem_openHalf q
    norm_num at him
    linarith

theorem four_mul_xiSpectralPoint_sq_add_twentyFive_ne_zero (q : XiZeroCopy) :
    4 * xiSpectralPoint q ^ (2 : ℕ) + 25 ≠ 0 := by
  intro h
  have hfactor :
      (2 * xiSpectralPoint q - 5 * Complex.I) *
          (2 * xiSpectralPoint q + 5 * Complex.I) = 0 := by
    rw [show (2 * xiSpectralPoint q - 5 * Complex.I) *
        (2 * xiSpectralPoint q + 5 * Complex.I) =
          4 * xiSpectralPoint q ^ (2 : ℕ) + 25 by
      calc
        (2 * xiSpectralPoint q - 5 * Complex.I) *
            (2 * xiSpectralPoint q + 5 * Complex.I) =
          4 * xiSpectralPoint q ^ (2 : ℕ) - 25 * (Complex.I * Complex.I) := by ring
        _ = 4 * xiSpectralPoint q ^ (2 : ℕ) + 25 := by rw [Complex.I_mul_I]; ring]
    exact h
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · have him := congrArg Complex.im hminus
    have hz := xiSpectralPoint_im_mem_openHalf q
    norm_num at him
    linarith
  · have him := congrArg Complex.im hplus
    have hz := xiSpectralPoint_im_mem_openHalf q
    norm_num at him
    linarith

theorem thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_actualRepeated_projecting_ne_zero
    (q : XiZeroCopy) :
    thetaCuspHawkingBalancedSpinTwoBochnerCoefficient
        d4BMActualRepeatedEisensteinCenteredParameter
        (Complex.I * xiSpectralPoint q) ≠ 0 := by
  rw [thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_actualRepeated_projecting_factorization]
  exact div_ne_zero
    (mul_ne_zero (four_mul_xiSpectralPoint_sq_add_one_ne_zero q)
      (four_mul_xiSpectralPoint_sq_add_twentyFive_ne_zero q))
    (by norm_num)

theorem d4BMCompletedBalancedSpinTwoProjectingSideFactor_actualRepeated_ne_zero
    (q : XiZeroCopy) :
    d4BMCompletedBalancedSpinTwoProjectingSideFactor
        d4BMActualRepeatedEisensteinCenteredParameter
        (d4BMXiProjectingEisensteinCenteredParameter q) ≠ 0 := by
  unfold d4BMCompletedBalancedSpinTwoProjectingSideFactor
    d4BMXiProjectingEisensteinCenteredParameter
  exact mul_ne_zero
    (mul_ne_zero
      (thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_actualRepeated_projecting_ne_zero q)
      (thetaCuspHawkingCompletedEisensteinXiFactor_actualRepeated_plus_projecting_ne_zero q))
    (thetaCuspHawkingCompletedEisensteinXiFactor_actualRepeated_minus_projecting_ne_zero q)

/-- The first multiplicity-permitted completed balanced source jet is always genuinely active. -/
theorem iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_actualRepeated_at_twiceMultiplicity_ne_zero
    (q : XiZeroCopy) :
    iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
        (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
          d4BMActualRepeatedEisensteinCenteredParameter v)
        (d4BMXiProjectingEisensteinCenteredParameter q) ≠ 0 := by
  exact (iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_ne_zero_iff_side
    d4BMActualRepeatedEisensteinCenteredParameter q).mpr
      (d4BMCompletedBalancedSpinTwoProjectingSideFactor_actualRepeated_ne_zero q)

/-- Canonical angular coefficient at the first live projecting-leg grade. -/
def d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet
    (q : XiZeroCopy) : ℂ :=
  iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
    (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
      d4BMActualRepeatedEisensteinCenteredParameter v)
    (d4BMXiProjectingEisensteinCenteredParameter q)

theorem d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet_ne_zero
    (q : XiZeroCopy) :
    d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q ≠ 0 := by
  exact iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_actualRepeated_at_twiceMultiplicity_ne_zero q

/-- Unique radial/left-QNM scale required by full HB incidence after angular amputation. -/
def d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoRequiredRadialScale
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus 0 (xiSpectralPoint q) *
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q -
    d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)) /
    d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q

theorem d4BMMultiplicityMatchedCompletedBalancedSpinTwoRadialScale_eq_requiredIncidence_iff
    (n : ℕ) (amplitude : ℂ) (radialScale : ℂ → ℂ) (q : XiZeroCopy) :
    radialScale (xiSpectralPoint q) *
        d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q =
      d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus 0 (xiSpectralPoint q) *
          d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q -
        d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) ↔
      radialScale (xiSpectralPoint q) =
        d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoRequiredRadialScale
          n amplitude q := by
  unfold d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoRequiredRadialScale
  exact (eq_div_iff
    (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet_ne_zero q)).symm

/-- Radial multiplication of the exact first live angular jet. -/
def d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
    (q : XiZeroCopy) (radialScale : ℂ → ℂ) (z : ℂ) : ℂ :=
  radialScale z *
    iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
      (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
        d4BMActualRepeatedEisensteinCenteredParameter v)
      (Complex.I * z)

theorem d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq
    (q : XiZeroCopy) (radialScale : ℂ → ℂ) :
    d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
        q radialScale (xiSpectralPoint q) =
      radialScale (xiSpectralPoint q) *
        d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q := by
  unfold d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
    d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet
    d4BMXiProjectingEisensteinCenteredParameter
  rfl

/-- Full HB incidence is exactly one radial-scale equation; angular existence is discharged. -/
theorem d4FullCrossBranchProjectedResidue_actualMultiplicityMatched_eq_unitBMTarget_iff_radialScale
    (n : ℕ) (amplitude : ℂ) (radialScale : ℂ → ℂ) (q : XiZeroCopy) :
    d4FullCrossBranchProjectedResidue amplitude
        (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder
          q radialScale)
        (xiSpectralPoint q) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q ↔
    radialScale (xiSpectralPoint q) =
      d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoRequiredRadialScale
        n amplitude q := by
  rw [d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_samePoleSource
    n amplitude
    (d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder q radialScale)
    q]
  rw [d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq]
  exact d4BMMultiplicityMatchedCompletedBalancedSpinTwoRadialScale_eq_requiredIncidence_iff
    n amplitude radialScale q

end

end RHTower
