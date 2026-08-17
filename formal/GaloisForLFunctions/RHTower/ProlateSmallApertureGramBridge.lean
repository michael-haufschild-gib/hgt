import GaloisForLFunctions.RHTower.ProlateSmallApertureSpectralLowerBound
import GaloisForLFunctions.RHTower.SlepianKernelFourier
import GaloisForLFunctions.RHTower.ProlateIndexedApertureContinuity

/-!
# Exact Gram bridge from moment synthesis to the indexed Slepian operator

The all-rung moment synthesis and the fixed-unit Slepian operator were previously
developed in disjoint representations.  This file identifies them exactly.  If
`T_c` synthesizes the aperture character `exp (-i c x ξ)`, then

`T_c† T_c = (2π / c) K_c`

for every nonzero real `c`, where `K_c` is the complex fixed-unit Slepian
operator.  Thus the moment-deflation approximation spectrum is the Gram spectrum
of the actual indexed prolate family, with the normalization exposed rather than
absorbed into a branch choice.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- The aperture character used by the moment expansion is the real-parameter
specialization of the finite-aperture Fourier test vector. -/
theorem apertureFourierL2_eq_apertureChar (x : ℝ) :
    apertureFourierL2 1 x = apertureChar 1 (x : ℂ) := by
  unfold apertureFourierL2 apertureChar
  apply Lp.ext
  filter_upwards [
    (memLp_apertureFourier 1 x).coeFn_toLp,
    (apertureCharFun_memLp 1 (x : ℂ)).coeFn_toLp] with t ht hchar
  rw [ht, hchar]
  simp [apertureCharFun]
  congr 1
  ring

/-- Exact character Gram kernel on the unit aperture. -/
theorem inner_apertureFourierL2_eq_sincKernel
    {c : ℝ} (hc : c ≠ 0) (x y : UnitPhysicalInterval) :
    inner ℂ (apertureFourierL2 1 (c * (x : ℝ)))
        (apertureFourierL2 1 (c * (y : ℝ))) =
      ((2 * (Real.pi : ℝ) / c : ℝ) : ℂ) *
        (sincKernelSmooth c (x : ℝ) (y : ℝ) : ℂ) := by
  rw [apertureFourierL2_eq_apertureChar]
  change apertureFourier 1 (apertureFourierL2 1 (c * (y : ℝ)))
      (c * (x : ℝ) : ℝ) = _
  let fy := fun t : ℝ =>
    Complex.exp (-((c * (y : ℝ) : ℝ) : ℂ) * Complex.I * (t : ℂ))
  have hfy : MemLp fy 2 (apertureMeasure 1) :=
    memLp_apertureFourier 1 (c * (y : ℝ))
  change apertureFourier 1 (hfy.toLp fy) (c * (x : ℝ) : ℝ) = _
  rw [apertureFourier_toLp 1 zero_le_one fy hfy]
  have hint :
      (∫ t in (-1 : ℝ)..1,
        Complex.exp (Complex.I * ((c * (x : ℝ) : ℝ) : ℂ) * (t : ℂ)) * fy t) =
      ∫ t in (-1 : ℝ)..1,
        Complex.exp (Complex.I * ((c * (x : ℝ) : ℝ) : ℂ) * (t : ℂ)) *
          (starRingEnd ℂ)
            (Complex.exp (Complex.I * ((c * (y : ℝ) : ℝ) : ℂ) * (t : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro t _
    have hconj :
        (starRingEnd ℂ)
            (Complex.exp (Complex.I * ((c * (y : ℝ) : ℝ) : ℂ) * (t : ℂ))) =
          Complex.exp (-(Complex.I * ((c * (y : ℝ) : ℝ) : ℂ) * (t : ℂ))) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_I]
    have hexp : fy t =
        Complex.exp (-(Complex.I * ((c * (y : ℝ) : ℝ) : ℂ) * (t : ℂ))) := by
      simp only [fy]
      congr 1
      ring
    change
      Complex.exp (Complex.I * ((c * (x : ℝ) : ℝ) : ℂ) * (t : ℂ)) * fy t =
        Complex.exp (Complex.I * ((c * (x : ℝ) : ℝ) : ℂ) * (t : ℂ)) *
          (starRingEnd ℂ)
            (Complex.exp (Complex.I * ((c * (y : ℝ) : ℝ) : ℂ) * (t : ℂ)))
    rw [hexp, hconj]
  have hker := sincKernelSmooth_eq_integral c (x : ℝ) (y : ℝ) hc
  rw [hint, hker]
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hpiC : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring_nf

/-- Almost-everywhere kernel field of the undeflated moment synthesis. -/
theorem apertureMomentFourierFieldL2_zero_coeFn (c : ℝ) :
    (apertureMomentFourierFieldL2 0 c :
        UnitPhysicalInterval → UnitApertureL2) =ᵐ[volume]
      fun x => apertureFourierL2 1 (c * (x : ℝ)) := by
  have hfield :
      (apertureMomentFourierFieldL2 0 c :
          UnitPhysicalInterval → UnitApertureL2) =ᵐ[volume]
        fun x => apertureMomentFourierField 0 c x := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure UnitPhysicalInterval))
      (apertureMomentFourierField 0 c)
  filter_upwards [hfield] with x hx
  rw [hx, apertureMomentFourierField_zero_apply]

/-- **Exact moment--Slepian Gram identity.** The rectangular Fourier synthesis
has the fixed-unit complex Slepian operator as its domain Gram, with exact scalar
`2π/c`.  No compactness, eigenbranch, or asymptotic premise is used. -/
theorem adjoint_comp_apertureMomentFourierSynthesis_eq_bandOperator
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousLinearMap.adjoint (apertureMomentFourierSynthesis 0 c) ∘L
        apertureMomentFourierSynthesis 0 c =
      (((2 * Real.pi / c : ℝ) : ℂ) • complexBandOperatorL2 c) := by
  apply ContinuousLinearMap.ext
  intro f
  change l2SheetTargetIncidence
      (volume : Measure UnitPhysicalInterval)
      (volume : Measure UnitPhysicalInterval)
      (apertureMomentFourierFieldL2 0 c)
      (apertureMomentFourierFieldL2 0 c) f =
    (((2 * Real.pi / c : ℝ) : ℂ) • complexBandOperatorL2 c) f
  apply Lp.ext
  have hinc := l2SheetTargetIncidence_coeFn
    (volume : Measure UnitPhysicalInterval)
    (volume : Measure UnitPhysicalInterval)
    (apertureMomentFourierFieldL2 0 c)
    (apertureMomentFourierFieldL2 0 c) f
  have hfield := apertureMomentFourierFieldL2_zero_coeFn c
  have hband := complexBandOperatorL2_coeFn c f
  have hsmul := Lp.coeFn_smul (((2 * Real.pi / c : ℝ) : ℂ))
    (complexBandOperatorL2 c f)
  filter_upwards [hinc, hfield, hband, hsmul] with x hincx hfieldx hbandx hsmulx
  rw [hincx]
  change _ =
    ((((2 * Real.pi / c : ℝ) : ℂ) • complexBandOperatorL2 c f :
      ComplexUnitIntervalL2) : UnitPhysicalInterval → ℂ) x
  rw [hsmulx, Pi.smul_apply, hbandx]
  simp only [smul_eq_mul]
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hfield] with y hfieldy
  rw [hfieldx, hfieldy, inner_apertureFourierL2_eq_sincKernel hc x y]
  ring

/-- Undeflated Fourier synthesis restricted to the actual fixed-unit complex
even carrier used by the indexed prolate spectrum. -/
noncomputable def complexEvenApertureMomentSynthesis (c : ℝ) :
    complexUnitBandEvenSubspace →L[ℂ] UnitApertureL2 :=
  apertureMomentFourierSynthesis 0 c ∘L
    complexUnitBandEvenSubspace.subtypeL

/-- **Exact even indexed Gram identity.** Restricting the moment synthesis to
the reflection-even carrier gives precisely the indexed even Slepian block as
its Gram operator.  This is the direct bridge from the all-rung moment flag to
`complexUnitBandEvenValue`; no parity permutation is left implicit. -/
theorem adjoint_comp_complexEvenApertureMomentSynthesis_eq_evenBlock
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousLinearMap.adjoint (complexEvenApertureMomentSynthesis c) ∘L
        complexEvenApertureMomentSynthesis c =
      (((2 * Real.pi / c : ℝ) : ℂ) • complexUnitBandEvenBlock c) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ
      (apertureMomentFourierSynthesis 0 c (g : ComplexUnitIntervalL2))
      (apertureMomentFourierSynthesis 0 c (f : ComplexUnitIntervalL2)) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hfull := congrArg
    (fun A : ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2 =>
      inner ℂ (g : ComplexUnitIntervalL2) (A (f : ComplexUnitIntervalL2)))
    (adjoint_comp_apertureMomentFourierSynthesis_eq_bandOperator hc)
  simpa [complexEvenApertureMomentSynthesis,
    coe_complexUnitBandEvenBlock_apply, inner_smul_right] using hfull

end GaloisForLFunctions.RHTower
