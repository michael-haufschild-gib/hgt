import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaBoundaryDirectCayleyFlow
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaGreenReflectionPairNoGo

/-!
# Direct theta-Cayley reflection port defect

Formalizes resolved direct-Cayley source orbit before divisor scalarization. Its port defect retains
exact Xi multiplicity and horizontal orientation. Functional-equation reflection inverts Cayley
multiplier and yields forced weighted same-time annihilation with coefficient `‖k_q‖^(4n+2)`.
-/

open Complex MeasureTheory

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile

private abbrev ThetaH_hedenmalmThetaGreenSquareBoundaryLaw_hedenmalmThetaDirectCayleyReflectionPortDefect := Lp ℂ 2 unitIntervalMeasure

def thetaBoundaryDirectCayleyResolvent : ThetaH_hedenmalmThetaGreenSquareBoundaryLaw_hedenmalmThetaDirectCayleyReflectionPortDefect →L[ℂ] ThetaH_hedenmalmThetaGreenSquareBoundaryLaw_hedenmalmThetaDirectCayleyReflectionPortDefect :=
  Ring.inverse (1 - thetaBoundaryDirectScaledGenerator)

def thetaXiBoundaryDirectCayleyResolvedCoefficient
    (q : XiZeroCopy) (n : ℕ) : ℂ :=
  thetaXiBoundaryDirectCayleyMultiplier q ^ n /
    (1 - thetaXiBoundaryDirectScaledEigenvalue q)

def thetaXiBoundaryDirectCayleyResolvedMode
    (q : XiZeroCopy) (n : ℕ) : ThetaH_hedenmalmThetaGreenSquareBoundaryLaw_hedenmalmThetaDirectCayleyReflectionPortDefect :=
  thetaBoundaryDirectCayleyResolvent
    ((thetaBoundaryDirectCayleyClock ^ n) (thetaXiDivisorEigenvector q))

def thetaXiBoundaryDirectCayleyPortDefect
    (q : XiZeroCopy) (n : ℕ) : ℝ :=
  (inner ℂ
    (pinnedBoundaryCLM (thetaXiBoundaryDirectCayleyResolvedMode q n))
    (thetaXiBoundaryDirectCayleyResolvedMode q n)).re

theorem thetaXiBoundaryDirectScaledEigenvalue_reflect (q : XiZeroCopy) :
    thetaXiBoundaryDirectScaledEigenvalue (xiZeroCopyReflectEquiv q) =
      -thetaXiBoundaryDirectScaledEigenvalue q := by
  rw [thetaXiBoundaryDirectScaledEigenvalue,
    thetaXiBoundaryDirectScaledEigenvalue,
    thetaXiReciprocalEigenvalue_reflect]
  ring

theorem one_add_thetaXiBoundaryDirectScaledEigenvalue_ne_zero (q : XiZeroCopy) :
    1 + thetaXiBoundaryDirectScaledEigenvalue q ≠ 0 := by
  have h := one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero
    (xiZeroCopyReflectEquiv q)
  rw [thetaXiBoundaryDirectScaledEigenvalue_reflect, sub_neg_eq_add] at h
  exact h

theorem thetaXiBoundaryDirectCayleyMultiplier_ne_zero (q : XiZeroCopy) :
    thetaXiBoundaryDirectCayleyMultiplier q ≠ 0 := by
  rw [thetaXiBoundaryDirectCayleyMultiplier]
  exact div_ne_zero
    (one_add_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q)
    (one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q)

theorem thetaXiBoundaryDirectCayleyMultiplier_reflect (q : XiZeroCopy) :
    thetaXiBoundaryDirectCayleyMultiplier (xiZeroCopyReflectEquiv q) =
      (thetaXiBoundaryDirectCayleyMultiplier q)⁻¹ := by
  rw [thetaXiBoundaryDirectCayleyMultiplier,
    thetaXiBoundaryDirectCayleyMultiplier,
    thetaXiBoundaryDirectScaledEigenvalue_reflect]
  field_simp [one_add_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q,
    one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q]
  ring

theorem norm_thetaXiBoundaryDirectCayleyMultiplier_reflect (q : XiZeroCopy) :
    ‖thetaXiBoundaryDirectCayleyMultiplier (xiZeroCopyReflectEquiv q)‖ =
      ‖thetaXiBoundaryDirectCayleyMultiplier q‖⁻¹ := by
  rw [thetaXiBoundaryDirectCayleyMultiplier_reflect, norm_inv]

theorem thetaXiBoundaryDirectCayleyResolvedMode_eq
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyResolvedMode q n =
      thetaXiBoundaryDirectCayleyResolvedCoefficient q n •
        thetaXiDivisorEigenvector q := by
  rw [thetaXiBoundaryDirectCayleyResolvedMode,
    pow_apply_of_complex_eigen (thetaBoundaryDirectCayleyClock_thetaXi_eigen q) n,
    map_smul, thetaBoundaryDirectCayleyResolvent,
    ringInverse_one_sub_apply_of_eigen
      isUnit_thetaBoundaryDirectCayleyDenominator
      (thetaXiDivisorEigenvector_ne_zero q)
      (thetaBoundaryDirectScaledGenerator_thetaXi_eigen q),
    smul_smul]
  rfl

theorem thetaXiBoundaryDirectCayleyResolvedCoefficient_ne_zero
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyResolvedCoefficient q n ≠ 0 := by
  rw [thetaXiBoundaryDirectCayleyResolvedCoefficient]
  exact div_ne_zero
    (pow_ne_zero n (thetaXiBoundaryDirectCayleyMultiplier_ne_zero q))
    (one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q)

theorem thetaXiBoundaryDirectCayleyPortDefect_eq
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyPortDefect q n =
      ‖thetaXiBoundaryDirectCayleyResolvedCoefficient q n‖ ^ (2 : ℕ) *
        thetaXiRankTwoBoundaryFlux q := by
  rw [thetaXiBoundaryDirectCayleyPortDefect,
    thetaXiBoundaryDirectCayleyResolvedMode_eq,
    map_smul, inner_smul_left, inner_smul_right]
  rw [thetaXiRankTwoBoundaryFlux]
  let c := thetaXiBoundaryDirectCayleyResolvedCoefficient q n
  let a := inner ℂ (pinnedBoundaryCLM (thetaXiDivisorEigenvector q))
    (thetaXiDivisorEigenvector q)
  rw [← mul_assoc]
  change (star c * c * a).re = ‖c‖ ^ (2 : ℕ) * a.re
  rw [show star c = (starRingEnd ℂ) c by rfl]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The resolved port defect keeps every positive source factor explicit. -/
theorem thetaXiBoundaryDirectCayleyPortDefect_eq_oriented_source_flux
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyPortDefect q n =
      ‖thetaXiBoundaryDirectCayleyResolvedCoefficient q n‖ ^ (2 : ℕ) *
        (2 * thetaSource.mass * (xiSpectralPoint q).im * thetaXiRootEnergy q) := by
  rw [thetaXiBoundaryDirectCayleyPortDefect_eq,
    thetaXiRankTwoBoundaryFlux_eq]

theorem thetaXiBoundaryDirectCayleyPortDefect_eq_zero_iff
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyPortDefect q n = 0 ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [thetaXiBoundaryDirectCayleyPortDefect_eq, mul_eq_zero]
  simp [thetaXiBoundaryDirectCayleyResolvedCoefficient_ne_zero q n]

theorem thetaXiBoundaryDirectCayleyPortDefect_eq_zero_iff_line
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyPortDefect q n = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiBoundaryDirectCayleyPortDefect_eq_zero_iff,
    thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero,
    xiSpectralPoint_im_eq]
  constructor <;> intro h <;> linarith

theorem thetaXiBoundaryDirectCayleyResolvedCoefficient_reflect_mul
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyResolvedCoefficient
        (xiZeroCopyReflectEquiv q) n *
          thetaXiBoundaryDirectCayleyMultiplier q ^ (2 * n + 1) =
      thetaXiBoundaryDirectCayleyResolvedCoefficient q n := by
  rw [thetaXiBoundaryDirectCayleyResolvedCoefficient,
    thetaXiBoundaryDirectCayleyResolvedCoefficient,
    thetaXiBoundaryDirectCayleyMultiplier_reflect,
    thetaXiBoundaryDirectScaledEigenvalue_reflect]
  have hk := thetaXiBoundaryDirectCayleyMultiplier_ne_zero q
  have hminus := one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q
  have hplus := one_add_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q
  rw [inv_pow]
  have hkrel :
      thetaXiBoundaryDirectCayleyMultiplier q *
          (1 - thetaXiBoundaryDirectScaledEigenvalue q) =
        1 + thetaXiBoundaryDirectScaledEigenvalue q := by
    rw [thetaXiBoundaryDirectCayleyMultiplier]
    field_simp [hminus]
  field_simp [pow_ne_zero n hk, hminus, hplus, hk]
  rw [sub_neg_eq_add, ← hkrel]
  ring

theorem thetaXiBoundaryDirectCayleyResolvedCoefficient_reflection_weight
    (q : XiZeroCopy) (n : ℕ) :
    ‖thetaXiBoundaryDirectCayleyMultiplier q‖ ^ (4 * n + 2) *
        ‖thetaXiBoundaryDirectCayleyResolvedCoefficient
          (xiZeroCopyReflectEquiv q) n‖ ^ (2 : ℕ) =
      ‖thetaXiBoundaryDirectCayleyResolvedCoefficient q n‖ ^ (2 : ℕ) := by
  have h := congrArg norm
    (thetaXiBoundaryDirectCayleyResolvedCoefficient_reflect_mul q n)
  simp only [norm_mul, norm_pow] at h
  rw [show 4 * n + 2 = (2 * n + 1) * 2 by omega, pow_mul]
  rw [← h]
  ring

theorem thetaXiBoundaryDirectCayleyPortDefect_weighted_reflect
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyPortDefect q n +
        ‖thetaXiBoundaryDirectCayleyMultiplier q‖ ^ (4 * n + 2) *
          thetaXiBoundaryDirectCayleyPortDefect
            (xiZeroCopyReflectEquiv q) n = 0 := by
  rw [thetaXiBoundaryDirectCayleyPortDefect_eq,
    thetaXiBoundaryDirectCayleyPortDefect_eq,
    thetaXiRankTwoBoundaryFlux_reflect]
  have h := thetaXiBoundaryDirectCayleyResolvedCoefficient_reflection_weight q n
  rw [← h]
  ring

/-- Eigenline effect of centering the reflection clock at its forced half-time `-1/2`. -/
def thetaXiBoundaryDirectCayleyHalfCenteredPortDefect
    (q : XiZeroCopy) (n : ℕ) : ℝ :=
  thetaXiBoundaryDirectCayleyPortDefect q n /
    ‖thetaXiBoundaryDirectCayleyMultiplier q‖ ^ (2 * n + 1)

/-- Half-step coefficient neutralization gives equal-coefficient reflected cancellation
unconditionally.  It does not make either individual fibre defect vanish. -/
theorem thetaXiBoundaryDirectCayleyHalfCenteredPortDefect_reflect_cancel
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyHalfCenteredPortDefect q n +
      thetaXiBoundaryDirectCayleyHalfCenteredPortDefect
        (xiZeroCopyReflectEquiv q) n = 0 := by
  rw [thetaXiBoundaryDirectCayleyHalfCenteredPortDefect,
    thetaXiBoundaryDirectCayleyHalfCenteredPortDefect,
    norm_thetaXiBoundaryDirectCayleyMultiplier_reflect, inv_pow, div_inv_eq_mul]
  have hk : ‖thetaXiBoundaryDirectCayleyMultiplier q‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (thetaXiBoundaryDirectCayleyMultiplier_ne_zero q)
  have h := thetaXiBoundaryDirectCayleyPortDefect_weighted_reflect q n
  rw [show 4 * n + 2 = (2 * n + 1) + (2 * n + 1) by omega, pow_add] at h
  field_simp [pow_ne_zero (2 * n + 1) hk]
  nlinarith

theorem thetaXiBoundaryDirectCayleyHalfCenteredPortDefect_eq_zero_iff_line
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiBoundaryDirectCayleyHalfCenteredPortDefect q n = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiBoundaryDirectCayleyHalfCenteredPortDefect, div_eq_zero_iff,
    thetaXiBoundaryDirectCayleyPortDefect_eq_zero_iff_line]
  simp [norm_ne_zero_iff.mpr (thetaXiBoundaryDirectCayleyMultiplier_ne_zero q)]

end

end RHTower.HedenmalmThetaSource
