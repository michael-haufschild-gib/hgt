import GaloisForLFunctions.RHTower.AnalyticHermitianClosedSpanRealization
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteUpperKernelInertia
import GaloisForLFunctions.HTGeometry.CauchyTransformOpenUniqueness
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Complex Set
open scoped InnerProductSpace ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem analyticOnNhd_upperToDiskCayley_upperHalfPlane :
    AnalyticOnNhd ℂ upperToDiskCayley upperHalfPlaneSet := by
  intro z hz
  change AnalyticAt ℂ (fun u : ℂ => (u - I) / (u + I)) z
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · intro hzero
    have him := congrArg Complex.im hzero
    change 0 < z.im at hz
    norm_num at him
    linarith

theorem analyticOnNhd_upperToDiskKernelWeight_upperHalfPlane :
    AnalyticOnNhd ℂ upperToDiskKernelWeight upperHalfPlaneSet := by
  intro z hz
  change AnalyticAt ℂ (fun u : ℂ => (Real.sqrt 2 : ℂ) / (u + I)) z
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · intro hzero
    have him := congrArg Complex.im hzero
    change 0 < z.im at hz
    norm_num at him
    linarith

/-- Weighted Hardy section whose Gram kernel is the upper-half-plane Szegő kernel. -/
def upperHalfPlaneHardySection (z : ℂ) : HardyDisk :=
  upperToDiskKernelWeight z •
    analyticHardyKernelSection ((starRingEnd ℂ) (upperToDiskCayley z))

theorem analyticOnNhd_inner_upperHalfPlaneHardySection (f : HardyDisk) :
    AnalyticOnNhd ℂ (fun z => inner ℂ f (upperHalfPlaneHardySection z))
      upperHalfPlaneSet := by
  have hcomp := (analyticOnNhd_inner_analyticHardyKernelSection f).comp
    analyticOnNhd_upperToDiskCayley_upperHalfPlane
    (fun z hz => by
      change dist (upperToDiskCayley z) 0 < 1
      rw [dist_zero_right]
      exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz)
  have hmul := analyticOnNhd_upperToDiskKernelWeight_upperHalfPlane.mul hcomp
  apply AnalyticOnNhd.congr isOpen_upperHalfPlaneSet hmul
  intro z hz
  simp only [upperHalfPlaneHardySection, inner_smul_right, Function.comp_apply]

theorem inner_upperHalfPlaneHardySection
    {z w : ℂ} (hz : z ∈ upperHalfPlaneSet) (hw : w ∈ upperHalfPlaneSet) :
    inner ℂ (upperHalfPlaneHardySection w) (upperHalfPlaneHardySection z) =
      I / (z - (starRingEnd ℂ) w) := by
  have hcz : ‖upperToDiskCayley z‖ < 1 :=
    GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz
  have hcw : ‖upperToDiskCayley w‖ < 1 :=
    GaloisForLFunctions.cayley_upperHalfPlane_to_disk w hw
  have hzden : z + I ≠ 0 := by
    change 0 < z.im at hz
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  have hwden : (starRingEnd ℂ) w - I ≠ 0 := by
    change 0 < w.im at hw
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  have hzw : z - (starRingEnd ℂ) w ≠ 0 :=
    upperHalfPlane_sub_conj_ne_zero hz hw
  have hcayley := upperHalfPlaneSchurKernel_eq_cayley_congruence
    (fun _ => 0) hzden hwden hzw
  rw [upperHalfPlaneHardySection, upperHalfPlaneHardySection,
    inner_smul_left, inner_smul_right,
    analyticHardyKernelSection_eq (by simpa using hcw),
    analyticHardyKernelSection_eq (by simpa using hcz),
    inner_hardyKernel_hardyKernel]
  simp only [← complex_star_eq_starRingEnd, star_star]
  simp only [upperHalfPlaneSchurKernel, diskSchurValueKernel, map_zero,
    mul_zero, sub_zero, one_div] at hcayley
  calc
    (starRingEnd ℂ) (upperToDiskKernelWeight w) *
        (upperToDiskKernelWeight z *
          (1 - upperToDiskCayley z *
            (starRingEnd ℂ) (upperToDiskCayley w))⁻¹) =
        upperToDiskKernelWeight z *
          (1 - upperToDiskCayley z *
            (starRingEnd ℂ) (upperToDiskCayley w))⁻¹ *
          (starRingEnd ℂ) (upperToDiskKernelWeight w) := by ring
    _ = I / (z - (starRingEnd ℂ) w) := by simpa using hcayley.symm

/-- Hilbert direct sum of two Hardy spaces. -/
abbrev HardyDouble := WithLp 2 (HardyDisk × HardyDisk)

/-- Difference form on two copies of the Hardy space. -/
def hardyDifferenceForm : HardyDouble →L[ℂ] HardyDouble :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ HardyDisk HardyDisk).symm ∘L
    ((ContinuousLinearMap.fst ℂ HardyDisk HardyDisk).prod
      (-(ContinuousLinearMap.snd ℂ HardyDisk HardyDisk))) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ HardyDisk HardyDisk)

@[simp] theorem hardyDifferenceForm_apply (x : HardyDouble) :
    hardyDifferenceForm x = WithLp.toLp 2 (x.fst, -x.snd) := by
  rfl

theorem hardyDifferenceForm_hermitian (x y : HardyDouble) :
    inner ℂ x (hardyDifferenceForm y) = inner ℂ (hardyDifferenceForm x) y := by
  change inner ℂ x.fst y.fst + inner ℂ x.snd (-y.snd) =
    inner ℂ x.fst y.fst + inner ℂ (-x.snd) y.snd
  simp

/-- Two-component shifted-Xi section whose difference Gram kernel is the cleared
Hermite--Biehler kernel. -/
def xiShiftClearedUpperSection (omega : ℝ) (z : ℂ) : HardyDouble :=
  WithLp.toLp 2
    (suzukiCanonicalE omega z • upperHalfPlaneHardySection z,
      suzukiCanonicalE omega (-z) • upperHalfPlaneHardySection z)

theorem analyticOnNhd_inner_xiShiftClearedUpperSection
    (omega : ℝ) (v : HardyDouble) :
    AnalyticOnNhd ℂ (fun z => inner ℂ v (xiShiftClearedUpperSection omega z))
      upperHalfPlaneSet := by
  have hE : AnalyticOnNhd ℂ (suzukiCanonicalE omega) upperHalfPlaneSet :=
    (differentiable_suzukiCanonicalE omega).differentiableOn.analyticOnNhd
      isOpen_upperHalfPlaneSet
  have hEneg : AnalyticOnNhd ℂ (fun z => suzukiCanonicalE omega (-z))
      upperHalfPlaneSet := by
    have hdneg : Differentiable ℂ (fun z : ℂ => suzukiCanonicalE omega (-z)) := by
      simpa [Function.comp_def] using
        (differentiable_suzukiCanonicalE omega).comp differentiable_id.neg
    exact hdneg.differentiableOn.analyticOnNhd isOpen_upperHalfPlaneSet
  have h1 := hE.mul (analyticOnNhd_inner_upperHalfPlaneHardySection v.fst)
  have h2 := hEneg.mul (analyticOnNhd_inner_upperHalfPlaneHardySection v.snd)
  apply AnalyticOnNhd.congr isOpen_upperHalfPlaneSet (h1.add h2)
  intro z hz
  simp only [Pi.add_apply]
  rw [WithLp.prod_inner_apply]
  simp only [xiShiftClearedUpperSection, inner_smul_right]
  rfl

theorem inner_xiShiftClearedUpperSection_hardyDifferenceForm
    (omega : ℝ) {z w : ℂ}
    (hz : z ∈ upperHalfPlaneSet) (hw : w ∈ upperHalfPlaneSet) :
    inner ℂ (xiShiftClearedUpperSection omega w)
        (hardyDifferenceForm (xiShiftClearedUpperSection omega z)) =
      xiShiftClearedUpperKernel omega z w := by
  rw [hardyDifferenceForm_apply, WithLp.prod_inner_apply]
  change inner ℂ
      (suzukiCanonicalE omega w • upperHalfPlaneHardySection w)
      (suzukiCanonicalE omega z • upperHalfPlaneHardySection z) +
    inner ℂ
      (suzukiCanonicalE omega (-w) • upperHalfPlaneHardySection w)
      (-(suzukiCanonicalE omega (-z) • upperHalfPlaneHardySection z)) = _
  rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_neg_right,
    inner_smul_right, inner_upperHalfPlaneHardySection hz hw]
  rw [xiShiftClearedUpperKernel]
  ring

/-- Actual shifted-Xi cleared kernel as an analytic Hermitian realization on its
canonical closed Hilbert span. -/
def xiShiftClearedUpperRealization (omega : ℝ) :=
  compressedClosedSpanRealization upperHalfPlaneSet
    (xiShiftClearedUpperSection omega) hardyDifferenceForm
    isPreconnected_upperHalfPlaneSet isOpen_upperHalfPlaneSet
    (analyticOnNhd_inner_xiShiftClearedUpperSection omega)
    hardyDifferenceForm_hermitian

theorem xiShiftClearedUpperRealization_kernel_eq
    (omega : ℝ) {z w : ℂ}
    (hz : z ∈ upperHalfPlaneSet) (hw : w ∈ upperHalfPlaneSet) :
    (xiShiftClearedUpperRealization omega).kernel z w =
      xiShiftClearedUpperKernel omega z w := by
  rw [xiShiftClearedUpperRealization,
    compressedClosedSpanRealization_kernel_eq _ _ _ _ _ _ _ hz hw]
  exact inner_xiShiftClearedUpperSection_hardyDifferenceForm omega hz hw

end
end RHTower
