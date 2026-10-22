import GaloisForLFunctions.RHTower.CCM.CCMFiniteEulerDenominator
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Inverse-free four-leg Euler current of the finite scattering source

Subtract the literal Gamma differential from the full finite spherical source.
Clearing its actual Euler denominator gives a difference of two physical source
Grams. On a fixed Sonin carrier this cleared current has the opposite Gram sign
from the original projection difference; the carrier change cannot be discarded.
-/

noncomputable section

open IsDedekindDomain

namespace RHTower

private abbrev EOp := evenSubspace →L[ℂ] evenSubspace

/-- Relative current of the actual full spherical and pure Gamma sources. -/
def ccmFiniteScatteringRelativeCurrent (S : Finset (HeightOneSpectrum ℤ)) : EOp :=
  ccmFiniteScatteringLogDifferential S - ccmArchimedeanGeometricScatteringLogDifferential

/-- The Gamma and physical walls cancel exactly, leaving the twisted Fourier projection pair. -/
theorem ccmFiniteScatteringRelativeCurrent_eq_fourierDifference
    (S : Finset (HeightOneSpectrum ℤ)) :
    ccmFiniteScatteringRelativeCurrent S =
      (ccmFiniteEulerPhysicalUnitary S).symm.toLinearIsometry.toContinuousLinearMap *
        evenFourierCutoff 1 * (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap -
          evenFourierCutoff 1 := by
  rw [ccmFiniteScatteringRelativeCurrent, ccmFiniteScatteringLogDifferential_eq_cutoffs,
    ccmArchimedeanGeometricScatteringLogDifferential_eq_cutoffs]
  abel

/-- Independent four-leg construction from the actual physical Euler polynomial. -/
def ccmFiniteEulerSourceCurrent (S : Finset (HeightOneSpectrum ℤ)) : EOp :=
  ccmFiniteEulerDenominator S * evenFourierCutoff 1 *
      ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) -
    ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) * evenFourierCutoff 1 *
      ccmFiniteEulerDenominator S

/-- Exact inverse-free congruence between the scattering projection pair and the four source legs. -/
theorem ccmFiniteScatteringRelativeCurrent_euler_congruence
    (S : Finset (HeightOneSpectrum ℤ)) :
    ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) *
      ccmFiniteScatteringRelativeCurrent S * ccmFiniteEulerDenominator S =
        ccmFiniteEulerSourceCurrent S := by
  let A := ccmFiniteEulerDenominator S
  let V := ccmFiniteEulerPhysicalUnitary S
  let v := V.toLinearIsometry.toContinuousLinearMap
  let w := V.symm.toLinearIsometry.toContinuousLinearMap
  have hVA : v * A = ContinuousLinearMap.adjoint A :=
    ccmFiniteEulerPhysicalUnitary_mul_denominator S
  have hvstar : ContinuousLinearMap.adjoint v = w := LinearIsometryEquiv.adjoint_eq_symm V
  have hVAstar : ContinuousLinearMap.adjoint (v * A) = A :=
    (congrArg ContinuousLinearMap.adjoint hVA).trans (ContinuousLinearMap.adjoint_adjoint A)
  have hleft : ContinuousLinearMap.adjoint A * w = A :=
    ((congrArg (fun T : EOp => ContinuousLinearMap.adjoint A * T) hvstar).symm.trans
      (ContinuousLinearMap.adjoint_comp v A).symm).trans hVAstar
  rw [ccmFiniteScatteringRelativeCurrent_eq_fourierDifference]
  change ContinuousLinearMap.adjoint A * (w * evenFourierCutoff 1 * v - evenFourierCutoff 1) * A =
    A * evenFourierCutoff 1 * ContinuousLinearMap.adjoint A -
      ContinuousLinearMap.adjoint A * evenFourierCutoff 1 * A
  rw [mul_sub, sub_mul]
  have hmain : ContinuousLinearMap.adjoint A * (w * evenFourierCutoff 1 * v) * A =
      A * evenFourierCutoff 1 * ContinuousLinearMap.adjoint A := by
    calc
      _ = (ContinuousLinearMap.adjoint A * w) * evenFourierCutoff 1 * (v * A) := by
        simp only [mul_assoc]
      _ = _ := congrArg₂ (fun X Y : EOp => X * evenFourierCutoff 1 * Y) hleft hVA
  rw [hmain]

private theorem unitFourier_gram (T : EOp) :
    ContinuousLinearMap.adjoint (evenFourierCutoff 1 * T) * (evenFourierCutoff 1 * T) =
      ContinuousLinearMap.adjoint T * evenFourierCutoff 1 * T := by
  let R := evenFourierCutoff 1
  have hRstar : ContinuousLinearMap.adjoint R = R := adjoint_evenFourierCutoff 1
  have hRR : R * R = R := evenFourierCutoff_mul_of_le 1 1 le_rfl
  have hstar : ContinuousLinearMap.adjoint (R * T) = ContinuousLinearMap.adjoint T * R :=
    (ContinuousLinearMap.adjoint_comp R T).trans
      (congrArg (fun U : EOp => ContinuousLinearMap.adjoint T * U) hRstar)
  change ContinuousLinearMap.adjoint (R * T) * (R * T) = _
  rw [hstar]
  calc
    _ = ContinuousLinearMap.adjoint T * (R * R) * T := by simp only [mul_assoc]
    _ = _ := by rw [hRR]

/-- Exact two-Gram decomposition before any compression, with all four physical source legs. -/
theorem ccmFiniteEulerSourceCurrent_eq_gram_difference
    (S : Finset (HeightOneSpectrum ℤ)) :
    ccmFiniteEulerSourceCurrent S =
      ContinuousLinearMap.adjoint
          (evenFourierCutoff 1 * ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)) *
        (evenFourierCutoff 1 * ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)) -
      ContinuousLinearMap.adjoint (evenFourierCutoff 1 * ccmFiniteEulerDenominator S) *
        (evenFourierCutoff 1 * ccmFiniteEulerDenominator S) := by
  rw [unitFourier_gram, unitFourier_gram, ContinuousLinearMap.adjoint_adjoint]
  rfl

private theorem sandwiched_unitFourier_gram (T : EOp) (b : ℝ) :
    ContinuousLinearMap.adjoint (evenFourierCutoff 1 * T * evenCentralSoninProjection b) *
      (evenFourierCutoff 1 * T * evenCentralSoninProjection b) =
        evenCentralSoninProjection b * ContinuousLinearMap.adjoint T *
          evenFourierCutoff 1 * T * evenCentralSoninProjection b := by
  let Q := evenCentralSoninProjection b
  have hstar : ContinuousLinearMap.adjoint (T * Q) = Q * ContinuousLinearMap.adjoint T :=
    (ContinuousLinearMap.adjoint_comp T Q).trans
      (congrArg (fun U : EOp => U * ContinuousLinearMap.adjoint T)
        (adjoint_evenCentralSoninProjection b))
  rw [mul_assoc (evenFourierCutoff 1) T (evenCentralSoninProjection b), unitFourier_gram]
  change ContinuousLinearMap.adjoint (T * Q) * evenFourierCutoff 1 * (T * Q) = _
  rw [hstar]
  simp only [mul_assoc, Q]

private theorem unitFourier_mul_sonin {b : ℝ} (hb : 1 ≤ b) :
    evenFourierCutoff 1 * evenCentralSoninProjection b = 0 := by
  rw [← (evenCentralSoninProjection_mul_of_le hb).2, ← mul_assoc,
    evenFourierCutoff_mul_evenCentralSoninProjection, zero_mul]

/-- On the fixed Sonin carrier the original relative scattering current is a positive Gram. -/
theorem ccmFiniteScatteringRelativeCurrent_sonin_gram
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    evenCentralSoninProjection b * ccmFiniteScatteringRelativeCurrent S *
        evenCentralSoninProjection b =
      ContinuousLinearMap.adjoint (evenFourierCutoff 1 *
          (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap *
          evenCentralSoninProjection b) *
        (evenFourierCutoff 1 *
          (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap *
          evenCentralSoninProjection b) := by
  have hRQ : evenCentralSoninProjection b * evenFourierCutoff 1 * evenCentralSoninProjection b = 0 := by
    rw [mul_assoc, unitFourier_mul_sonin hb, mul_zero]
  have hstar := LinearIsometryEquiv.adjoint_eq_symm (ccmFiniteEulerPhysicalUnitary S)
  change ContinuousLinearMap.adjoint
    (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap =
      (ccmFiniteEulerPhysicalUnitary S).symm.toLinearIsometry.toContinuousLinearMap at hstar
  rw [ccmFiniteScatteringRelativeCurrent_eq_fourierDifference, mul_sub, sub_mul, hRQ, sub_zero,
    sandwiched_unitFourier_gram, hstar]
  simp only [mul_assoc]

/-- The cleared current on that same carrier is the negative Euler-denominator boundary Gram. -/
theorem ccmFiniteEulerSourceCurrent_sonin_negative_gram
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    evenCentralSoninProjection b * ccmFiniteEulerSourceCurrent S * evenCentralSoninProjection b =
      -(ContinuousLinearMap.adjoint (evenFourierCutoff 1 * ccmFiniteEulerDenominator S *
          evenCentralSoninProjection b) *
        (evenFourierCutoff 1 * ccmFiniteEulerDenominator S * evenCentralSoninProjection b)) := by
  have hzero := evenFourierCutoff_mul_adjoint_ccmFiniteEulerDenominator_mul_soninProjection S hb
  let A := ccmFiniteEulerDenominator S
  let Q := evenCentralSoninProjection b
  let R := evenFourierCutoff 1
  have hgramzero : ContinuousLinearMap.adjoint (R * ContinuousLinearMap.adjoint A * Q) *
      (R * ContinuousLinearMap.adjoint A * Q) = 0 :=
    (congrArg (fun T : EOp => ContinuousLinearMap.adjoint T * T) hzero).trans (by simp)
  have hfirst : Q * A * R * ContinuousLinearMap.adjoint A * Q = 0 :=
    (congrArg (fun T : EOp => Q * T * R * ContinuousLinearMap.adjoint A * Q)
      (ContinuousLinearMap.adjoint_adjoint A)).symm.trans
        ((sandwiched_unitFourier_gram (ContinuousLinearMap.adjoint A) b).symm.trans hgramzero)
  rw [ccmFiniteEulerSourceCurrent, mul_sub, sub_mul]
  have hfirst' : evenCentralSoninProjection b *
      (ccmFiniteEulerDenominator S * evenFourierCutoff 1 *
        ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)) *
      evenCentralSoninProjection b = 0 := by
    simpa only [mul_assoc, Q, R, A] using hfirst
  rw [hfirst', zero_sub, sandwiched_unitFourier_gram]
  simp only [mul_assoc]

private theorem gram_eq_neg_gram_iff (X Y : EOp) :
    ContinuousLinearMap.adjoint X * X = -(ContinuousLinearMap.adjoint Y * Y) ↔
      X = 0 ∧ Y = 0 := by
  constructor
  · intro h
    have hx : 0 ≤ ContinuousLinearMap.adjoint X * X :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).2
        (ContinuousLinearMap.isPositive_adjoint_comp_self X)
    have hy : 0 ≤ ContinuousLinearMap.adjoint Y * Y :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).2
        (ContinuousLinearMap.isPositive_adjoint_comp_self Y)
    have hX : ContinuousLinearMap.adjoint X * X = 0 :=
      le_antisymm (h ▸ neg_nonpos.mpr hy) hx
    have hY : ContinuousLinearMap.adjoint Y * Y = 0 :=
      neg_eq_zero.mp (h.symm.trans hX)
    exact ⟨ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp hX,
      ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp hY⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- Exact boundary of identifying the original and cleared currents on an unchanged carrier. -/
theorem ccmFiniteScatteringRelativeCurrent_fixedCarrier_eq_iff
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    evenCentralSoninProjection b * ccmFiniteScatteringRelativeCurrent S *
        evenCentralSoninProjection b =
      evenCentralSoninProjection b * ccmFiniteEulerSourceCurrent S *
        evenCentralSoninProjection b ↔
      evenFourierCutoff 1 *
          (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap *
          evenCentralSoninProjection b = 0 ∧
        evenFourierCutoff 1 * ccmFiniteEulerDenominator S *
          evenCentralSoninProjection b = 0 := by
  rw [ccmFiniteScatteringRelativeCurrent_sonin_gram S hb,
    ccmFiniteEulerSourceCurrent_sonin_negative_gram S hb, gram_eq_neg_gram_iff]

end RHTower
