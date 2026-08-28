import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPeierlsResponseOddChargeClassification

/-!
# Division-free reflected cross-pair response compensator

The earlier punctured-height response countermodel used division by the vanishing physical source,
leaving open whether analytic/causal regularity could restore RH force. This module closes that
loophole at the algebraic level.

Let `F_n(q)` be literal unit unsquared BM source amplitude times complementary exponent. The
cross-pair correction

`K_n(q) = (2q-1) F_n(reflect q)`

uses no division. Its composite charge is
`(2q-1) F_n(q) F_n(reflect q)`, hence is reflection-odd by involution. Both correction and charge
vanish exactly on the critical wall, yet the corrected current cancels on every Xi fibre
unconditionally. Off wall two nonzero charges cancel while canonical Peierls optical power remains
strictly positive.

Thus excluding singular response corrections is insufficient. Remaining physical gate must impose
source independence, reflection locality, or derive the left-QNM response from a literal action.

`[NEW] [DIVISION-FREE COUNTERMODEL] [CROSS-PAIR CLASSIFICATION] [NO-GO] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Literal unit-source radial response factor before an added correction. -/
def d4BMXiSecondHarmonicBareResponseFactor
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude q *
    d4BMXiPlusPlusComplementaryExponent n q

theorem d4BMXiSecondHarmonicBareResponseFactor_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicBareResponseFactor n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  unfold d4BMXiSecondHarmonicBareResponseFactor
    d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude
  rw [mul_eq_zero]
  simp only [d4BMXiPlusPlusComplementaryExponent_ne_zero n q, or_false]
  exact d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q

/-- Division-free reflected cross-pair response correction. -/
def d4BMXiSecondHarmonicCrossPairResponseCorrection
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  (2 * (q.1 : ℂ) - 1) *
    d4BMXiSecondHarmonicBareResponseFactor n (xiZeroCopyReflectEquiv q)

theorem d4BMXiSecondHarmonicCrossPairResponseCorrection_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicCrossPairResponseCorrection n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have ht : 2 * (q.1 : ℂ) - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    exact xi_divisor_support_im_ne_zero q.1 (by linarith)
  rw [d4BMXiSecondHarmonicCrossPairResponseCorrection, mul_eq_zero]
  simp only [ht, false_or]
  rw [d4BMXiSecondHarmonicBareResponseFactor_eq_zero_iff]
  have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
    xiZeroReflectEquiv_apply q.1
  rw [href]
  norm_num
  constructor <;> intro h <;> linarith

/-- Exact nonlocal cross-pair factorization of the corrected response charge. -/
theorem d4BMXiSecondHarmonicCrossPairResponseCharge_eq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsResponseCharge n
        (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q =
      (2 * (q.1 : ℂ) - 1) *
        d4BMXiSecondHarmonicBareResponseFactor n q *
        d4BMXiSecondHarmonicBareResponseFactor n
          (xiZeroCopyReflectEquiv q) := by
  unfold d4BMXiSecondHarmonicPeierlsResponseCharge
    d4BMXiSecondHarmonicCrossPairResponseCorrection
    d4BMXiSecondHarmonicBareResponseFactor
  ring

theorem d4BMXiSecondHarmonicCrossPairResponseCharge_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsResponseCharge n
        (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hfactor :
      d4BMXiSecondHarmonicPeierlsResponseCharge n
          (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q =
        d4BMXiSecondHarmonicCrossPairResponseCorrection n q *
          d4BMXiSecondHarmonicBareResponseFactor n q := by
    unfold d4BMXiSecondHarmonicPeierlsResponseCharge
      d4BMXiSecondHarmonicBareResponseFactor
    ring
  rw [hfactor, mul_eq_zero,
    d4BMXiSecondHarmonicCrossPairResponseCorrection_eq_zero_iff,
    d4BMXiSecondHarmonicBareResponseFactor_eq_zero_iff, or_self]

/-- The division-free cross-pair charge is reflection-odd by involution. -/
theorem d4BMXiSecondHarmonicCrossPairResponseCharge_reflection_odd
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsResponseCharge n
        (d4BMXiSecondHarmonicCrossPairResponseCorrection n)
        (xiZeroCopyReflectEquiv q) =
      -d4BMXiSecondHarmonicPeierlsResponseCharge n
        (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q := by
  rw [d4BMXiSecondHarmonicCrossPairResponseCharge_eq,
    d4BMXiSecondHarmonicCrossPairResponseCharge_eq,
    xiZeroCopyReflectEquiv_apply_apply]
  have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
    xiZeroReflectEquiv_apply q.1
  rw [href]
  ring

/-- Division-free reflected cross-pair compensation cancels every Xi fibre unconditionally. -/
theorem forall_d4BMXiSecondHarmonicCrossPairResponseCorrectedReflectionCurrent_eq_zero
    (n : ℕ) :
    ∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n
        (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q = 0 := by
  intro q
  exact (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff n
    (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q).mpr
      (d4BMXiSecondHarmonicCrossPairResponseCharge_reflection_odd n q)

/-- Off wall, two nonzero cross-pair charges cancel while passive optical power stays positive. -/
theorem d4BMXiSecondHarmonicCrossPairCancellation_nontrivial_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiSecondHarmonicPeierlsResponseCharge n
          (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q ≠ 0 ∧
      d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n
          (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q = 0 ∧
      0 < hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q := by
  refine ⟨?_, forall_d4BMXiSecondHarmonicCrossPairResponseCorrectedReflectionCurrent_eq_zero
    n q, ?_⟩
  · exact (d4BMXiSecondHarmonicCrossPairResponseCharge_eq_zero_iff n q).not.mpr htilt
  · have hnonneg := hbXiPeierlsFESchwarzOrbitRadiationPower_nonneg
      (d4BMGaugeFixedSecondHarmonicRadiationMap q)
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient (1 : ℂ)
        (xiSpectralPoint q), 0) n q
    have hne : hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q ≠ 0 :=
      (hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_line n q).not.mpr htilt
    exact lt_of_le_of_ne hnonneg hne.symm

end


end RHTower

