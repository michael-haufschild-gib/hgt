import GaloisForLFunctions.RHTower.DeningerMeyerXiGaussianResidueNonadmission
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCountertransport
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalBound
import GaloisForLFunctions.RHTower.XiDivisorHilbertCarrier

/-!
# Reflected Gaussian horizon admission for the singular Xi residue packet

The forced Gaussian--Gamma residue packet is not in unweighted divisor
`ℓ²`, and its analytic normalizer alone leaves the nonsummable constant
packet.  This file constructs the independent horizon grade from an actual
source before divisor restriction.

We restrict the Mellin transform of the fixed Paugam-invariant centered
Meyer Gaussian to the multiplicity-exact Xi divisor.  Its values are exactly
a positive-time centered Xi heat multiplier.  Hence the grade is nonzero at
every divisor copy, reflection invariant, compatible with line conjugation,
and square-summable.  Multiplication by the forced residue normalizer then
turns the actual singular residue packet into this source-derived grade.

This supplies a coefficient-faithful singular `ℓ²` admission.  It does not
assert augmentation transversality or the post-descent Hermitian Gram bound.
-/

open Complex

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- Positive heat time selected by the centered reflected Gaussian source. -/
def reflectedGaussianHorizonTime : ℝ := 1 / (4 * Real.pi)

theorem reflectedGaussianHorizonTime_pos : 0 < reflectedGaussianHorizonTime := by
  unfold reflectedGaussianHorizonTime
  positivity

/-- Horizon grade obtained by evaluating one fixed, reflection-invariant Meyer source
before restricting it to the Xi divisor. -/
def reflectedGaussianHorizonGrade (q : XiZeroCopy) : ℂ :=
  deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (q.1 : ℂ)

/-- The horizon grade is literally the zeroth Xi evaluation of the fixed Meyer cohomology class. -/
theorem reflectedGaussianHorizonGrade_eq_sourceEvaluation (q : XiZeroCopy) :
    reflectedGaussianHorizonGrade q =
      deningerMeyerXiSupportJetEvaluationLM q.1
        (⟨0, xiSupportMultiplicity_pos q.1⟩ : DeningerArithmeticJetIndex q.1)
        deningerMeyerReflectedLogGaussianCohomologyClass := by
  rw [reflectedGaussianHorizonGrade,
    deningerMeyerReflectedLogGaussianCohomologyClass,
    deningerMeyerXiSupportJetEvaluationLM_mk]
  rfl

/-- The source restriction is the centered Xi heat multiplier at its forced positive time. -/
theorem reflectedGaussianHorizonGrade_eq_heat (q : XiZeroCopy) :
    reflectedGaussianHorizonGrade q =
      xiGaussianHeatTerm reflectedGaussianHorizonTime q := by
  rw [reflectedGaussianHorizonGrade,
    deningerMeyerReflectedLogGaussianSource_mellin]
  unfold xiGaussianHeatTerm
  have hspectral : xiSpectralPoint q ^ (2 : ℕ) =
      -(((q.1 : ℂ) - 1 / 2) ^ (2 : ℕ)) := by
    rw [xiSpectralPoint, mul_pow]
    have hI : (-Complex.I) ^ (2 : ℕ) = (-1 : ℂ) := by
      rw [pow_two]
      simp
    rw [hI]
    ring
  rw [hspectral]
  congr 1
  push_cast [reflectedGaussianHorizonTime]
  field_simp [Real.pi_ne_zero]

/-- No actual divisor copy is erased by the source-derived horizon grade. -/
theorem reflectedGaussianHorizonGrade_ne_zero (q : XiZeroCopy) :
    reflectedGaussianHorizonGrade q ≠ 0 := by
  rw [reflectedGaussianHorizonGrade]
  exact deningerMeyerReflectedLogGaussianSource_mellin_ne_zero (q.1 : ℂ)

/-- The grade preserves functional-equation reflection exactly. -/
theorem reflectedGaussianHorizonGrade_reflect (q : XiZeroCopy) :
    reflectedGaussianHorizonGrade (xiZeroCopyReflectEquiv q) =
      reflectedGaussianHorizonGrade q := by
  rw [reflectedGaussianHorizonGrade_eq_heat,
    reflectedGaussianHorizonGrade_eq_heat]
  simp [xiGaussianHeatTerm, xiSpectralPoint_reflect]

/-- The grade respects the Hermitian line-conjugation sector. -/
theorem reflectedGaussianHorizonGrade_lineConj (q : XiZeroCopy) :
    reflectedGaussianHorizonGrade (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (reflectedGaussianHorizonGrade q) := by
  rw [reflectedGaussianHorizonGrade_eq_heat,
    reflectedGaussianHorizonGrade_eq_heat]
  rw [xiGaussianHeatTerm, xiGaussianHeatTerm, xiSpectralPoint_lineConj,
    ← Complex.exp_conj]
  congr 1
  simp

/-- The single fixed reflected Gaussian supplies the missing square-summable horizon grade. -/
theorem summable_norm_sq_reflectedGaussianHorizonGrade :
    Summable (fun q : XiZeroCopy => ‖reflectedGaussianHorizonGrade q‖ ^ (2 : ℕ)) := by
  have htime : 0 < 2 * reflectedGaussianHorizonTime := by
    positivity [reflectedGaussianHorizonTime_pos]
  have hsum : Summable (fun q : XiZeroCopy =>
      ‖xiGaussianHeatTerm (2 * reflectedGaussianHorizonTime) q‖) :=
    summable_norm_iff.mpr (summable_xiGaussianHeatTerm htime)
  refine hsum.congr fun q => ?_
  rw [reflectedGaussianHorizonGrade_eq_heat,
    norm_xiGaussianHeatTerm, norm_xiGaussianHeatTerm]
  conv_rhs => rw [pow_two]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The global source-derived horizon grade as an actual completed Xi-divisor vector. -/
def reflectedGaussianHorizonGradeL2 : XiDivisorL2 :=
  ⟨reflectedGaussianHorizonGrade,
    HilbertSchmidt.memℓp_of_sq
      summable_norm_sq_reflectedGaussianHorizonGrade⟩

@[simp]
theorem reflectedGaussianHorizonGradeL2_apply (q : XiZeroCopy) :
    reflectedGaussianHorizonGradeL2 q = reflectedGaussianHorizonGrade q := rfl

/-- The completed horizon vector is nonzero on every coordinate, hence in particular nonzero. -/
theorem reflectedGaussianHorizonGradeL2_ne_zero :
    reflectedGaussianHorizonGradeL2 ≠ 0 := by
  intro hzero
  let q : XiZeroCopy := Classical.choice inferInstance
  have hq := congrArg (fun x : XiDivisorL2 => x q) hzero
  exact reflectedGaussianHorizonGrade_ne_zero q (by simpa using hq)

/-- Source-faithful diagonal weight: forced analytic normalizer times the
independently constructed reflected Gaussian horizon grade. -/
def reflectedGaussianHorizonAdmissionWeight (q : XiZeroCopy) : ℂ :=
  reflectedGaussianHorizonGrade q * xiGaussianGammaResidueNormalizer q

/-- The weighted singular residue packet is exactly the source-derived horizon grade. -/
theorem reflectedGaussianHorizonAdmissionWeight_mul_packet (q : XiZeroCopy) :
    reflectedGaussianHorizonAdmissionWeight q *
        xiGaussianGammaResiduePacket q = reflectedGaussianHorizonGrade q := by
  exact horizonGrade_mul_normalizer_mul_packet reflectedGaussianHorizonGrade q

/-- The resulting actual singular residue packet belongs to the divisor `ℓ²` carrier. -/
theorem summable_reflectedGaussianHorizonAdmissionPacket :
    Summable (fun q : XiZeroCopy =>
      ‖reflectedGaussianHorizonAdmissionWeight q *
        xiGaussianGammaResiduePacket q‖ ^ (2 : ℕ)) := by
  unfold reflectedGaussianHorizonAdmissionWeight
  exact (summable_weighted_packet_iff_horizonGrade
    reflectedGaussianHorizonGrade).2
      summable_norm_sq_reflectedGaussianHorizonGrade

/-- Weighting is coefficient-faithful: neither the source grade nor the forced normalizer
vanishes at any actual divisor copy. -/
theorem reflectedGaussianHorizonAdmissionWeight_ne_zero (q : XiZeroCopy) :
    reflectedGaussianHorizonAdmissionWeight q ≠ 0 := by
  apply mul_ne_zero (reflectedGaussianHorizonGrade_ne_zero q)
  intro hzero
  have hflat := xiGaussianGammaResidueNormalizer_mul_packet q
  rw [hzero, zero_mul] at hflat
  norm_num at hflat

end

end DeningerMeyerGaussianGreen
end RHTower
