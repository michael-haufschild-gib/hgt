import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaComplexResolventRow
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaEsscherCyclicity
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion

/-!
# Exterior Esscher resolvent frame for the theta source

The all-complex source-resolvent row is represented by the Esscher--Fourier vector on the
corresponding horizontal line.  On every exterior line `|h| >= 1/2`, classical zero-freeness
makes all source pencils invertible.  Fixed-line Esscher cyclicity then upgrades the scalar row
to a dense adjoint-resolvent frame.
-/

open Complex MeasureTheory Set

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmClosedWeightedDerivative

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Source-pencil parameter represented by the `h`-Esscher vector at Fourier frequency `tau`. -/
def thetaEsscherResolventParameter (h tau : ℝ) : ℂ :=
  -(tau : ℂ) - (h : ℂ) * Complex.I

@[simp] theorem thetaEsscherResolventParameter_im (h tau : ℝ) :
    (thetaEsscherResolventParameter h tau).im = -h := by
  simp [thetaEsscherResolventParameter, Complex.mul_im]

/-- The Esscher--Fourier vector represents the all-complex source-character row. -/
theorem inner_thetaEsscherFourierFamily_eq_complexResolventMoment
    (h tau : ℝ) (f : ThetaH) :
    inner ℂ (thetaEsscherFourierFamily h tau) f =
      thetaComplexResolventMoment (thetaEsscherResolventParameter h tau) f := by
  rw [inner_lp_eq, thetaComplexResolventMoment]
  apply integral_congr_ae
  filter_upwards [thetaEsscherFourierFamily_ae h tau] with t ht
  rw [ht, map_mul, Complex.conj_ofReal]
  rw [Complex.ofReal_exp, realProbCharacter, sourceChar,
    ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [thetaEsscherResolventParameter]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact adjoint row: the inverse pencil sends the constant covector to the normalized
Esscher--Fourier vector. -/
theorem adjoint_thetaComplexResolvent_pinnedOne_eq_esscher
    {h tau : ℝ}
    (hz : IsUnit (thetaSourcePencil (thetaEsscherResolventParameter h tau))) :
    (thetaComplexResolvent (thetaEsscherResolventParameter h tau)).adjoint pinnedOne =
      ((starRingEnd ℂ)
        (rootA thetaSource (thetaEsscherResolventParameter h tau) 1))⁻¹ •
        thetaEsscherFourierFamily h tau := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hmean : inner ℂ pinnedOne
      (thetaComplexResolvent (thetaEsscherResolventParameter h tau) f) =
      pinnedMean
        (thetaComplexResolvent (thetaEsscherResolventParameter h tau) f) := by
    rw [inner_lp_eq, pinnedMean]
    apply integral_congr_ae
    filter_upwards [pinnedOne_coeFn] with t ht
    rw [ht, map_one, one_mul]
  rw [hmean, pinnedMean_thetaComplexResolvent_eq hz,
    inner_smul_left,
    inner_thetaEsscherFourierFamily_eq_complexResolventMoment]
  have hA : rootA thetaSource (thetaEsscherResolventParameter h tau) 1 ≠ 0 :=
    rootA_one_ne_zero_of_sourcePencil_isUnit hz
  simp only [map_inv₀, Complex.conj_conj]
  field_simp

/-- Every exterior Esscher line is unconditionally free of source-pencil singularities. -/
theorem isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs
    {h : ℝ} (hh : 1 / 2 ≤ |h|) (tau : ℝ) :
    IsUnit (thetaSourcePencil (thetaEsscherResolventParameter h tau)) := by
  by_contra hunit
  have hzero :=
    (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero
      (thetaEsscherResolventParameter h tau)).1 hunit
  obtain ⟨_hlower, hupper⟩ := xiC_zero_im_mem_openHalf hzero
  have habs : |(thetaEsscherResolventParameter h tau).im| < 1 / 2 :=
    abs_lt.mpr ⟨by linarith, hupper⟩
  rw [thetaEsscherResolventParameter_im, abs_neg] at habs
  linarith

/-- **Unconditional exterior resolvent frame.**  On every line `|h| >= 1/2`, the adjoint
source resolvents of the constant boundary vector have dense complex span in quantile `L²`. -/
theorem isCyclicFamily_adjoint_thetaComplexResolvent_pinnedOne_of_half_le_abs
    {h : ℝ} (hh : 1 / 2 ≤ |h|) :
    IsCyclicFamily (𝕜 := ℂ)
      (fun tau : ℝ =>
        (thetaComplexResolvent (thetaEsscherResolventParameter h tau)).adjoint pinnedOne) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  have hEsscher (tau : ℝ) : L (thetaEsscherFourierFamily h tau) = 0 := by
    let A : ℂ := rootA thetaSource (thetaEsscherResolventParameter h tau) 1
    have hz :=
      isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hh tau
    have hrow := adjoint_thetaComplexResolvent_pinnedOne_eq_esscher hz
    have hzero := hL tau
    rw [hrow, map_smul] at hzero
    have hA : A ≠ 0 := by
      exact rootA_one_ne_zero_of_sourcePencil_isUnit hz
    have hstarA : (starRingEnd ℂ) A ≠ 0 := by simpa using hA
    have hc : ((starRingEnd ℂ) A)⁻¹ ≠ 0 := inv_ne_zero hstarA
    exact (smul_eq_zero.mp hzero).resolve_left hc
  exact continuousLinearFunctional_eq_zero_of_isCyclicFamily
    (isCyclicFamily_thetaEsscherFourierFamily h) L hEsscher

end

end RHTower.HedenmalmThetaSource
