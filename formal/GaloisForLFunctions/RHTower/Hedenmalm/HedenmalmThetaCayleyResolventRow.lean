import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaBoundaryDirectCayleyFlow
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaComplexResolventRow

/-!
# Exact direct-Cayley resolvent row

The disk resolvent of the direct Cayley clock is exactly the source pencil under the Cayley
parameter map.  Consequently its singularities are precisely the completed theta divisor, and
its pinned mean is an explicit source-character quotient.  This identifies the complete observed
transfer function, not only its asymptotic growth rate.
-/

open Complex MeasureTheory

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmClosedWeightedDerivative

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Source-pencil coordinate of a disk point for the direct Cayley clock. -/
def thetaBoundaryDirectCayleyDiskParameter (w : ℂ) : ℂ :=
  -((1 + w) / (1 - w)) *
    (Complex.I * (thetaBoundaryDirectCayleyStep : ℂ))

/-- Resolvent generating the full direct-Cayley orbit. -/
def thetaBoundaryDirectCayleyGeneratingResolvent (w : ℂ) : ThetaH →L[ℂ] ThetaH :=
  Ring.inverse (1 - w • thetaBoundaryDirectCayleyClock)

/-- The source pencil is the direct generator pencil in Cayley coordinates. -/
theorem thetaSourcePencil_directCayleyDiskParameter {w : ℂ} (hw : w ≠ 1) :
    thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w) =
      1 - ((1 + w) / (1 - w)) • thetaBoundaryDirectScaledGenerator := by
  rw [thetaSourcePencil, thetaBoundaryDirectCayleyDiskParameter,
    thetaBoundaryDirectScaledGenerator, smul_smul]
  have hden : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hcoeff :
      -((1 + w) / (1 - w)) *
          (Complex.I * (thetaBoundaryDirectCayleyStep : ℂ)) =
        -(((1 + w) / (1 - w)) *
          (Complex.I * (thetaBoundaryDirectCayleyStep : ℂ))) := by ring
  rw [hcoeff]
  module

/-- Exact factorization carrying the clock resolvent back to the source pencil. -/
theorem one_sub_smul_thetaBoundaryDirectCayleyClock_factor {w : ℂ} (hw : w ≠ 1) :
    1 - w • thetaBoundaryDirectCayleyClock =
      ((1 - w) • thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w)) *
        Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) := by
  let X : ThetaH →L[ℂ] ThetaH := thetaBoundaryDirectScaledGenerator
  let D : ThetaH →L[ℂ] ThetaH := 1 - X
  let N : ThetaH →L[ℂ] ThetaH := 1 + X
  let P : ThetaH →L[ℂ] ThetaH :=
    thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w)
  have hDR : D * Ring.inverse D = 1 := by
    simpa only [D, X] using thetaBoundaryDirectCayleyDenominator_mul_inverse
  have hc :
      (1 - w) * ((1 + w) / (1 - w)) = 1 + w := by
    field_simp [sub_ne_zero.mpr hw.symm]
  have hlinear : D - w • N = (1 - w) • P := by
    rw [show P = 1 - ((1 + w) / (1 - w)) • X by
      simpa only [P, X] using thetaSourcePencil_directCayleyDiskParameter hw]
    dsimp only [D, N]
    rw [smul_sub, smul_smul, hc]
    module
  change 1 - w • (N * Ring.inverse D) =
    ((1 - w) • P) * Ring.inverse D
  rw [← hlinear, sub_mul, hDR, smul_mul_assoc]

/-- Clock resolvent is singular exactly when the Cayley-mapped completed theta transform vanishes. -/
theorem one_sub_smul_thetaBoundaryDirectCayleyClock_not_isUnit_iff {w : ℂ}
    (hw : w ≠ 1) :
    ¬ IsUnit (1 - w • thetaBoundaryDirectCayleyClock) ↔
      XiC (thetaBoundaryDirectCayleyDiskParameter w) = 0 := by
  have hw0 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hscalar : IsUnit
      (algebraMap ℂ (ThetaH →L[ℂ] ThetaH) (1 - w)) :=
    IsUnit.map (algebraMap ℂ (ThetaH →L[ℂ] ThetaH))
      ((isUnit_iff_ne_zero).mpr hw0)
  rw [one_sub_smul_thetaBoundaryDirectCayleyClock_factor hw,
    (isUnit_thetaBoundaryDirectCayleyDenominator.ringInverse).mul_right_iff,
    Algebra.smul_def, hscalar.mul_left_iff,
    thetaSourcePencil_not_isUnit_iff_XiC_eq_zero]

theorem isUnit_one_sub_smul_thetaBoundaryDirectCayleyClock {w : ℂ}
    (hw : w ≠ 1)
    (hz : IsUnit (thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w))) :
    IsUnit (1 - w • thetaBoundaryDirectCayleyClock) := by
  have hw0 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hscalar : IsUnit
      (algebraMap ℂ (ThetaH →L[ℂ] ThetaH) (1 - w)) :=
    IsUnit.map (algebraMap ℂ (ThetaH →L[ℂ] ThetaH))
      ((isUnit_iff_ne_zero).mpr hw0)
  rw [one_sub_smul_thetaBoundaryDirectCayleyClock_factor hw, Algebra.smul_def]
  exact (hscalar.mul hz).mul isUnit_thetaBoundaryDirectCayleyDenominator.ringInverse

/-- First exact form of the Cayley orbit resolvent. -/
theorem thetaBoundaryDirectCayleyGeneratingResolvent_eq_sourceResolvent {w : ℂ}
    (hw : w ≠ 1)
    (hz : IsUnit (thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w))) :
    thetaBoundaryDirectCayleyGeneratingResolvent w =
      (1 - w)⁻¹ •
        ((1 - thetaBoundaryDirectScaledGenerator) *
          thetaComplexResolvent (thetaBoundaryDirectCayleyDiskParameter w)) := by
  let P : ThetaH →L[ℂ] ThetaH :=
    thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w)
  have hw0 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hscalar : IsUnit
      (algebraMap ℂ (ThetaH →L[ℂ] ThetaH) (1 - w)) :=
    IsUnit.map (algebraMap ℂ (ThetaH →L[ℂ] ThetaH))
      ((isUnit_iff_ne_zero).mpr hw0)
  have hscaled : IsUnit ((1 - w) • P) := by
    rw [Algebra.smul_def]
    exact hscalar.mul hz
  have hinvScaled : Ring.inverse ((1 - w) • P) =
      (1 - w)⁻¹ • Ring.inverse P := by
    apply hscaled.mul_left_cancel
    rw [Ring.mul_inverse_cancel _ hscaled]
    symm
    change ((1 - w) • P) * ((1 - w)⁻¹ • Ring.inverse P) = 1
    rw [smul_mul_smul, Ring.mul_inverse_cancel P hz,
      mul_inv_cancel₀ hw0, one_smul]
  rw [thetaBoundaryDirectCayleyGeneratingResolvent,
    one_sub_smul_thetaBoundaryDirectCayleyClock_factor hw,
    Ring.inverse_mul (Or.inl hscaled),
    Ring.inverse_inverse isUnit_thetaBoundaryDirectCayleyDenominator,
    hinvScaled]
  simp only [P, thetaComplexResolvent]
  rw [mul_smul_comm]

/-- Two-term transfer decomposition: direct Cayley orbit equals feed-through plus source row. -/
theorem thetaBoundaryDirectCayleyGeneratingResolvent_eq_twoTerm {w : ℂ}
    (hw : w ≠ 1) (hwneg : w ≠ -1)
    (hz : IsUnit (thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w))) :
    thetaBoundaryDirectCayleyGeneratingResolvent w =
      (1 + w)⁻¹ • (1 : ThetaH →L[ℂ] ThetaH) +
        (2 * w / ((1 - w) * (1 + w))) •
          thetaComplexResolvent (thetaBoundaryDirectCayleyDiskParameter w) := by
  rw [thetaBoundaryDirectCayleyGeneratingResolvent_eq_sourceResolvent hw hz]
  apply hz.mul_right_cancel
  rw [thetaComplexResolvent, smul_mul_assoc, mul_assoc,
    Ring.inverse_mul_cancel (thetaSourcePencil
      (thetaBoundaryDirectCayleyDiskParameter w)) hz, mul_one,
    add_mul, smul_mul_assoc, smul_mul_assoc,
    one_mul,
    Ring.inverse_mul_cancel (thetaSourcePencil
      (thetaBoundaryDirectCayleyDiskParameter w)) hz]
  rw [thetaSourcePencil_directCayleyDiskParameter hw]
  have hw0 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hwp0 : 1 + w ≠ 0 := by
    intro hzero
    apply hwneg
    linear_combination hzero
  have hconst :
      (1 + w)⁻¹ + 2 * w / ((1 - w) * (1 + w)) = (1 - w)⁻¹ := by
    field_simp [hw0, hwp0]
    ring
  have hgenerator :
      (1 + w)⁻¹ * ((1 + w) / (1 - w)) = (1 - w)⁻¹ := by
    field_simp [hw0, hwp0]
  rw [smul_sub]
  rw [smul_sub, smul_smul, hgenerator]
  rw [← hconst]
  module

/-- Exact scalar observed transfer function of the direct Cayley orbit. -/
theorem pinnedMean_thetaBoundaryDirectCayleyGeneratingResolvent {w : ℂ}
    (hw : w ≠ 1) (hwneg : w ≠ -1)
    (hz : IsUnit (thetaSourcePencil (thetaBoundaryDirectCayleyDiskParameter w)))
    (f : ThetaH) :
    pinnedMean (thetaBoundaryDirectCayleyGeneratingResolvent w f) =
      (1 + w)⁻¹ * pinnedMean f +
        (2 * w / ((1 - w) * (1 + w))) *
          (thetaComplexResolventMoment
              (thetaBoundaryDirectCayleyDiskParameter w) f /
            rootA thetaSource (thetaBoundaryDirectCayleyDiskParameter w) 1) := by
  rw [thetaBoundaryDirectCayleyGeneratingResolvent_eq_twoTerm hw hwneg hz]
  change pinnedMean
      ((1 + w)⁻¹ • f +
        (2 * w / ((1 - w) * (1 + w))) •
          thetaComplexResolvent (thetaBoundaryDirectCayleyDiskParameter w) f) = _
  calc
    pinnedMean
        ((1 + w)⁻¹ • f +
          (2 * w / ((1 - w) * (1 + w))) •
            thetaComplexResolvent (thetaBoundaryDirectCayleyDiskParameter w) f) =
      thetaPinnedMeanCLM
        ((1 + w)⁻¹ • f +
          (2 * w / ((1 - w) * (1 + w))) •
            thetaComplexResolvent (thetaBoundaryDirectCayleyDiskParameter w) f) :=
      (thetaPinnedMeanCLM_apply _).symm
    _ = (1 + w)⁻¹ * pinnedMean f +
        (2 * w / ((1 - w) * (1 + w))) *
          pinnedMean
            (thetaComplexResolvent (thetaBoundaryDirectCayleyDiskParameter w) f) := by
      rw [map_add, map_smul, map_smul,
        thetaPinnedMeanCLM_apply, thetaPinnedMeanCLM_apply]
      simp only [smul_eq_mul]
    _ = _ := by
      rw [pinnedMean_thetaComplexResolvent_eq hz]

end

end RHTower.HedenmalmThetaSource
