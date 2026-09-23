import GaloisForLFunctions.RHTower.SuzukiAdmissibleTwoShiftAffineSewing
import GaloisForLFunctions.RHTower.SuzukiCarlemanJumpEulerDefectWeld
import GaloisForLFunctions.RHTower.SuzukiOppositeShiftCrossSewnExterior
import GaloisForLFunctions.RHTower.SuzukiShiftedXiTargetFlatPencil

/-!
# Xi--Suzuki pole--zero normal-form universality

At every Xi zero, shifted target coordinates, cross-sewn and affine-sewn projective exteriors,
the admissible exterior Weyl quotient, and its Euler defect have one source-independent local
normal form.  The target is a simple zero, the projective exteriors and Weyl quotient are simple
poles, and the Euler defect is a double pole.  Their normalized leading coefficients are not
merely separately universal: the target coefficient is the reciprocal of both exterior
coefficients and the negative reciprocal of the Weyl coefficient.
-/

open Complex WithTop
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Complete local normal form shared by Suzuki target, sewing, Weyl, and Euler-defect charts at
one Xi zero.  The final five fields are cross-chart laws rather than repetitions of the component
theorems. -/
structure XiSuzukiPoleZeroNormalFormUniversalCertificate
    (eta alpha beta gamma z : ℂ)
    (WAlpha WBeta intervalAlpha intervalBeta rightAlpha rightBeta : ℂ → ℂ) : Prop where
  targetSimpleZero :
    meromorphicOrderAt (suzukiShiftedXiTarget eta) z = 1
  crossSewnSimplePole :
    meromorphicOrderAt
        (suzukiCrossSewnNormalizedExterior eta
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((-1 : ℤ) : WithTop ℤ)
  affineSewnSimplePole :
    meromorphicOrderAt
        (suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((-1 : ℤ) : WithTop ℤ)
  exteriorWeylSimplePole :
    meromorphicOrderAt
        (suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta) z =
      ((-1 : ℤ) : WithTop ℤ)
  exteriorWeylEulerDoublePole :
    meromorphicOrderAt
        (GaloisForLFunctions.RHTower.suzukiEulerDefect
          (suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta)) z =
      ((-2 : ℤ) : WithTop ℤ)
  targetCoefficient :
    meromorphicTrailingCoeffAt (suzukiShiftedXiTarget eta) z =
      z ^ (2 : ℕ) / ((analyticOrderAt XiC z).toNat : ℂ)
  crossSewnCoefficient :
    meromorphicTrailingCoeffAt
        (suzukiCrossSewnNormalizedExterior eta
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((analyticOrderAt XiC z).toNat : ℂ) / z ^ (2 : ℕ)
  affineSewnCoefficient :
    meromorphicTrailingCoeffAt
        (suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z =
      ((analyticOrderAt XiC z).toNat : ℂ) / z ^ (2 : ℕ)
  exteriorWeylCoefficient :
    meromorphicTrailingCoeffAt
        (suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta) z =
      -((analyticOrderAt XiC z).toNat : ℂ) / z ^ (2 : ℕ)
  crossAffineCoefficientAgreement :
    meromorphicTrailingCoeffAt
        (suzukiCrossSewnNormalizedExterior eta
          WAlpha WBeta intervalAlpha intervalBeta) z =
      meromorphicTrailingCoeffAt
        (suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z
  affineWeylCoefficientOpposition :
    meromorphicTrailingCoeffAt
        (suzukiAffineSewnNormalizedExterior alpha beta gamma
          WAlpha WBeta intervalAlpha intervalBeta) z =
      -meromorphicTrailingCoeffAt
        (suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta) z
  targetCrossReciprocal :
    meromorphicTrailingCoeffAt (suzukiShiftedXiTarget eta) z *
        meromorphicTrailingCoeffAt
          (suzukiCrossSewnNormalizedExterior eta
            WAlpha WBeta intervalAlpha intervalBeta) z = 1
  targetAffineReciprocal :
    meromorphicTrailingCoeffAt (suzukiShiftedXiTarget eta) z *
        meromorphicTrailingCoeffAt
          (suzukiAffineSewnNormalizedExterior alpha beta gamma
            WAlpha WBeta intervalAlpha intervalBeta) z = 1
  targetWeylOrientedReciprocal :
    meromorphicTrailingCoeffAt (suzukiShiftedXiTarget eta) z *
        meromorphicTrailingCoeffAt
          (suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta) z = -1

/-- **Xi--Suzuki pole--zero normal-form universality law.**  Every Xi zero induces the same
order ladder `+1, -1, -1, -1, -2` in shifted-target, cross-sewn, affine-sewn, Weyl, and
Euler-defect coordinates.  Projective normalization cancels all source data, and the corresponding
leading coefficients pair to `1`, `1`, and `-1` across the zero/pole duality. -/
theorem xiZero_suzukiPoleZeroNormalFormUniversalCertificate
    {eta alpha beta gamma z : ℂ}
    {WAlpha WBeta intervalAlpha intervalBeta rightAlpha rightBeta : ℂ → ℂ}
    (hab : alpha ≠ beta) (hz : XiC z = 0)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hWAlpha0 : WAlpha z ≠ 0) (hWBeta0 : WBeta z ≠ 0)
    (hIAlpha : ∀ w, AnalyticAt ℂ intervalAlpha w)
    (hIBeta : ∀ w, AnalyticAt ℂ intervalBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w) :
    XiSuzukiPoleZeroNormalFormUniversalCertificate eta alpha beta gamma z
      WAlpha WBeta intervalAlpha intervalBeta rightAlpha rightBeta := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact XiC_zero_ne hz
  obtain ⟨m, hm, hmOrder, _⟩ :=
    exists_multiplicity_meromorphicTrailingCoeffAt_suzukiShiftedXiTarget
      (eta := eta) hz
  have htoNat : (analyticOrderAt XiC z).toNat = m := by
    rw [hmOrder]
    simp
  have hm0 : (((analyticOrderAt XiC z).toNat : ℕ) : ℂ) ≠ 0 := by
    rw [htoNat]
    exact_mod_cast Nat.ne_of_gt hm
  have hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hWAlpha0) hWBeta0
  have htargetOrder :=
    meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero
      (eta := eta) hz
  have hcrossOrder :=
    meromorphicOrderAt_suzukiCrossSewnNormalizedExterior_eq_neg_one
      (eta := eta) hz (hWAlpha z) hWAlpha0 (hWBeta z) hWBeta0
        (hIAlpha z) (hIBeta z)
  have haffineOrder :=
    meromorphicOrderAt_suzukiAffineSewnNormalizedExterior_eq_neg_one
      (gamma := gamma) hab hz (hWAlpha z) hWAlpha0 (hWBeta z) hWBeta0
        (hIAlpha z) (hIBeta z)
  have hweylOrder :=
    meromorphicOrderAt_suzukiAffineSewnExteriorWeylQuotient_eq_neg_one
      hz hWAlpha hWBeta hP0 hRAlpha hRBeta
  have heulerOrder :=
    meromorphicOrderAt_suzukiEulerDefect_affineSewnExteriorWeylQuotient_eq_neg_two
      hz hWAlpha hWBeta hP0 hRAlpha hRBeta
  have htargetCoeff :=
    meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero
      (eta := eta) hz
  have hcrossCoeff :=
    meromorphicTrailingCoeffAt_suzukiCrossSewnNormalizedExterior
      (eta := eta) hz (hWAlpha z) hWAlpha0 (hWBeta z) hWBeta0
        (hIAlpha z) (hIBeta z)
  have haffineCoeff :=
    meromorphicTrailingCoeffAt_suzukiAffineSewnNormalizedExterior
      (gamma := gamma) hab hz (hWAlpha z) hWAlpha0 (hWBeta z) hWBeta0
        (hIAlpha z) (hIBeta z)
  have hweylCoeff :=
    meromorphicTrailingCoeffAt_suzukiAffineSewnExteriorWeylQuotient_of_XiC_zero
      hz hWAlpha hWBeta hP0 hRAlpha hRBeta
  refine {
    targetSimpleZero := htargetOrder
    crossSewnSimplePole := hcrossOrder
    affineSewnSimplePole := haffineOrder
    exteriorWeylSimplePole := hweylOrder
    exteriorWeylEulerDoublePole := heulerOrder
    targetCoefficient := htargetCoeff
    crossSewnCoefficient := hcrossCoeff
    affineSewnCoefficient := haffineCoeff
    exteriorWeylCoefficient := hweylCoeff
    crossAffineCoefficientAgreement := ?_
    affineWeylCoefficientOpposition := ?_
    targetCrossReciprocal := ?_
    targetAffineReciprocal := ?_
    targetWeylOrientedReciprocal := ?_ }
  · rw [hcrossCoeff, haffineCoeff]
  · rw [haffineCoeff, hweylCoeff]
    ring
  · rw [htargetCoeff, hcrossCoeff]
    field_simp [hz0, hm0]
  · rw [htargetCoeff, haffineCoeff]
    field_simp [hz0, hm0]
  · rw [htargetCoeff, hweylCoeff]
    field_simp [hz0, hm0]

end

end RHTower
