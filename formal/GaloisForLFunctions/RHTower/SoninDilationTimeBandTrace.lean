/-
Exact trace current of the original Sonin dilation response. Finite-window
Schur kernels identify the actual normalized Fourier/dilation operators;
trace-class cyclicity keeps both source legs throughout the reduction.
-/
import GaloisForLFunctions.RHTower.SoninCompleteResponseTrace
import GaloisForLFunctions.HTGeometry.SchurKernelComposition
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import GaloisForLFunctions.HTGeometry.OperatorTraceAdjoint

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace RHTower
open GaloisForLFunctions.HTGeometry
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩


private def phaseKernel (a t x y : ℝ) : ℂ :=
  (Icc (-a) a).indicator (fun x =>
    (Icc (-a) a).indicator (fun y =>
      Complex.exp ((-(2 * Real.pi * t * x * y) : ℝ) * Complex.I)) y) x

private theorem phaseKernel_symm (a t x y : ℝ) :
    phaseKernel a t x y = phaseKernel a t y x := by
  by_cases hx : x ∈ Icc (-a) a <;> by_cases hy : y ∈ Icc (-a) a
  · simp only [phaseKernel, indicator_of_mem hx, indicator_of_mem hy]
    congr 1
    push_cast
    ring
  all_goals simp [phaseKernel, hx, hy]

private theorem phaseKernel_measurable (a t : ℝ) :
    Measurable (Function.uncurry (phaseKernel a t)) := by
  have hphase : Measurable (fun z : ℝ × ℝ =>
      Complex.exp ((-(2 * Real.pi * t * z.1 * z.2) : ℝ) * Complex.I)) := by
    fun_prop
  have h := hphase.indicator (measurableSet_Icc.prod measurableSet_Icc :
    MeasurableSet ((Icc (-a) a) ×ˢ (Icc (-a) a)))
  convert h using 1
  funext z
  by_cases hx : z.1 ∈ Icc (-a) a <;> by_cases hy : z.2 ∈ Icc (-a) a <;>
    simp only [Function.uncurry, phaseKernel, indicator, mem_prod, hx, hy,
      if_true, if_false, and_self, false_and, and_false]

private theorem phaseKernel_row (a t x : ℝ) :
    ∫⁻ y, ‖phaseKernel a t x y‖ₑ ≤ volume (Icc (-a) a) := by
  by_cases hx : x ∈ Icc (-a) a
  · have hpoint : (fun y => ‖phaseKernel a t x y‖ₑ) =
        (Icc (-a) a).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext y
      by_cases hy : y ∈ Icc (-a) a <;>
        simp only [phaseKernel, indicator, hx, hy, if_true, if_false,
          Complex.enorm_exp_ofReal_mul_I, enorm_zero]
    rw [hpoint, lintegral_indicator measurableSet_Icc, setLIntegral_const, one_mul]
  · simp [phaseKernel, hx]

private def phaseSchur (a t : ℝ) : SchurKernel (volume : Measure ℝ) where
  toFun := phaseKernel a t
  measurable := phaseKernel_measurable a t
  bound := (volume (Icc (-a) a)).toNNReal
  row x := by
    rw [ENNReal.coe_toNNReal (measure_Icc_lt_top.ne)]
    exact phaseKernel_row a t x
  col y := by
    rw [ENNReal.coe_toNNReal (measure_Icc_lt_top.ne)]
    simpa only [phaseKernel_symm a t] using phaseKernel_row a t y

private theorem phaseSchur_energy (a t : ℝ) :
    ∫⁻ x, ∫⁻ y, ‖(phaseSchur a t).toFun x y‖ₑ ^ 2 < ∞ := by
  have hpoint (x y : ℝ) : ‖(phaseSchur a t).toFun x y‖ₑ ^ 2 =
      (Icc (-a) a).indicator (fun _ =>
        (Icc (-a) a).indicator (fun _ => (1 : ℝ≥0∞)) y) x := by
    by_cases hx : x ∈ Icc (-a) a <;> by_cases hy : y ∈ Icc (-a) a <;>
      simp only [phaseSchur, phaseKernel, indicator, hx, hy, if_true, if_false,
        Complex.enorm_exp_ofReal_mul_I, enorm_zero, one_pow] <;> norm_num
  simp_rw [hpoint]
  have hinner (x : ℝ) :
      (∫⁻ y, (Icc (-a) a).indicator (fun _ =>
        (Icc (-a) a).indicator (fun _ => (1 : ℝ≥0∞)) y) x) =
      (Icc (-a) a).indicator (fun _ => volume (Icc (-a) a)) x := by
    by_cases hx : x ∈ Icc (-a) a
    · simp [hx, lintegral_indicator measurableSet_Icc]
    · simp [hx]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
  exact ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top

private theorem phaseSchur_op_coeFn (a t : ℝ) (f : SoninL2) :
    ((phaseSchur a t).op f : ℝ → ℂ) =ᵐ[volume]
      (Icc (-a) a).indicator (fun x => ∫ y in Icc (-a) a,
        Complex.exp ((-(2 * Real.pi * t * x * y) : ℝ) * Complex.I) * f y) := by
  filter_upwards [(phaseSchur a t).op_coeFn f] with x hx
  rw [hx, SchurKernel.apply]
  by_cases hxa : x ∈ Icc (-a) a
  · rw [indicator_of_mem hxa, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hya : y ∈ Icc (-a) a <;>
      simp only [phaseSchur, phaseKernel, indicator, hxa, hya, if_true, if_false, zero_mul]
  · simp [phaseSchur, phaseKernel, hxa]

private theorem phaseKernel_mul (a t s x y : ℝ) :
    phaseKernel a t y x * phaseKernel a s x y = phaseKernel a (t + s) x y := by
  rw [phaseKernel_symm a t y x]
  by_cases hx : x ∈ Icc (-a) a <;> by_cases hy : y ∈ Icc (-a) a
  · simp only [phaseKernel, indicator_of_mem hx, indicator_of_mem hy]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  all_goals simp [phaseKernel, hx, hy]

private theorem phaseSchur_trace_product (a t s : ℝ) :
    ContinuousLinearMap.opTrace ((phaseSchur a t).op ∘L (phaseSchur a s).op) =
      ∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
        Complex.exp ((-(2 * Real.pi * (t + s) * x * y) : ℝ) * Complex.I) := by
  rw [SchurKernel.opTrace_comp_op _ _ (phaseSchur_energy a t) (phaseSchur_energy a s)]
  change (∫ x, ∫ y, phaseKernel a t y x * phaseKernel a s x y) = _
  simp_rw [phaseKernel_mul]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-a) a
  · simp only [phaseKernel, indicator_of_mem hx]
    rw [integral_indicator measurableSet_Icc]
  · simp [phaseKernel, hx]

private theorem cutoff_fourier_ae (a : ℝ) (f : SoninL2) :
    (fourierUnitary (indicatorCutoff (Icc (-a) a) measurableSet_Icc f) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y in Icc (-a) a,
        Complex.exp ((-(2 * Real.pi * x * y) : ℝ) * Complex.I) * f y := by
  let g := indicatorCutoff (Icc (-a) a) measurableSet_Icc f
  have hg := integrable_indicatorCutoff_Icc (-a) a f
  have h := l2_fourier_coeFn_eq_l1_fourier_of_integrable g hg
  have h' : (fourierUnitary g : ℝ → ℂ) =ᵐ[volume]
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hg).toLp g) : ℝ → ℂ) := by
    simpa [fourierUnitary] using! h
  filter_upwards [h'] with x hx
  exact hx.trans (l1Fourier_indicatorCutoff_Icc_eq_setIntegral (-a) a f x)

private theorem phaseSchur_one (a : ℝ) :
    (phaseSchur a 1).op = cutoffFourierCutoff (-a) a (-a) a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [phaseSchur_op_coeFn a 1 f,
    indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc
      (fourierUnitary (indicatorCutoff (Icc (-a) a) measurableSet_Icc f)),
    cutoff_fourier_ae a f] with x hK hA hF
  change (phaseSchur a 1).op f x =
    indicatorCutoff (Icc (-a) a) measurableSet_Icc
      (fourierUnitary (indicatorCutoff (Icc (-a) a) measurableSet_Icc f)) x
  rw [hK, hA]
  by_cases hx : x ∈ Icc (-a) a
  · simp only [indicator_of_mem hx, mul_one]
    exact hF.symm
  · simp only [indicator_of_notMem hx]

private theorem phaseSchur_neg_one (a : ℝ) :
    (phaseSchur a (-1)).op = ContinuousLinearMap.adjoint (phaseSchur a 1).op := by
  rw [SchurKernel.adjoint_op]
  apply SchurKernel.op_eq_of_ae
  filter_upwards [] with x
  filter_upwards [] with y
  change phaseKernel a (-1) x y = (starRingEnd ℂ) (phaseKernel a 1 y x)
  rw [phaseKernel_symm a 1 y x]
  by_cases hx : x ∈ Icc (-a) a <;> by_cases hy : y ∈ Icc (-a) a
  · simp only [phaseKernel, indicator_of_mem hx, indicator_of_mem hy, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  all_goals simp [phaseKernel, hx, hy]

private theorem cutoff_dilation_fourier (a t : ℝ) (ht : 0 < t) :
    indicatorCutoff (Icc (-a) a) measurableSet_Icc * dilationCLM t ht *
        fourierUnitary.toLinearIsometry.toContinuousLinearMap *
        indicatorCutoff (Icc (-a) a) measurableSet_Icc =
      (Real.sqrt t : ℂ) • (phaseSchur a t).op := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  let g := indicatorCutoff (Icc (-a) a) measurableSet_Icc f
  have hF := (cutoff_fourier_ae a f).comp_tendsto
    (realMul_quasiMeasurePreserving t ht.ne').tendsto_ae
  filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc
      (dilation t ht (fourierUnitary g)),
    dilation_ae t ht (fourierUnitary g), hF,
    phaseSchur_op_coeFn a t f,
    Lp.coeFn_smul (Real.sqrt t : ℂ) ((phaseSchur a t).op f)] with x hA hD hF hK hsmul
  change indicatorCutoff (Icc (-a) a) measurableSet_Icc
    (dilation t ht (fourierUnitary g)) x =
    ((Real.sqrt t : ℂ) • (phaseSchur a t).op f : SoninL2) x
  rw [hA, hsmul, Pi.smul_apply, smul_eq_mul, hK]
  by_cases hx : x ∈ Icc (-a) a
  · rw [indicator_of_mem hx, indicator_of_mem hx, hD]
    congr 1
    calc
      _ = ∫ y in Icc (-a) a,
          Complex.exp ((-(2 * Real.pi * (t * x) * y) : ℝ) * Complex.I) * f y := hF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        congr 2
        push_cast
        ring
  · simp only [indicator_of_notMem hx, mul_zero]

open ContinuousLinearMap
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)

private theorem trace_conjugate (T F U : Op) (hT : MemSchattenClass 1 T)
    (hUF : U * F = 1) : opTrace (F * T * U) = opTrace T := by
  have hTU : MemSchattenClass 1 (T * U) := memSchattenClass_one_comp_right hT U
  calc
    opTrace (F * T * U) = opTrace (F * (T * U)) := by rw [mul_assoc]
    _ = opTrace ((T * U) * F) := hTU.one_opTrace_comp_comm F
    _ = opTrace T := by rw [mul_assoc, hUF, mul_one]

private theorem trace_dilation_reduce (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    opTrace (dilationCLM r hr *
      indicatorCutoff (Icc (-a) a) measurableSet_Icc *
      fourierCutoff (Icc (-a) a) measurableSet_Icc) =
    (Real.sqrt r⁻¹ : ℂ) *
      opTrace ((phaseSchur a r⁻¹).op * (phaseSchur a (-1)).op) := by
  let A : Op := indicatorCutoff (Icc (-a) a) measurableSet_Icc
  let B : Op := fourierCutoff (Icc (-a) a) measurableSet_Icc
  let F : Op := fourierUnitary.toLinearIsometry.toContinuousLinearMap
  let U : Op := fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
  let D := dilationCLM r hr
  let E := dilationCLM r⁻¹ (inv_pos.mpr hr)
  have hAA : A * A = A := indicatorCutoff_idempotent _ _
  have hBB : B * B = B := fourierCutoff_idempotent _ _
  have hFU : F * U = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    exact fourierUnitary.apply_symm_apply f
  have hUF : U * F = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    exact fourierUnitary.symm_apply_apply f
  have hB : B = U * A * F := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  have hFD : F * D = E * F := by
    apply ContinuousLinearMap.ext
    intro f
    exact fourierUnitary_dilation r hr f
  have hAB : MemSchattenClass 1 (A * B) :=
    memSchattenClass_one_indicatorCutoff_fourierCutoff_central a a ha
  have hS : MemSchattenClass 1 (D * A * B) := by
    rw [mul_assoc]
    exact memSchattenClass_one_comp_left hAB D
  have hBS : MemSchattenClass 1 (B * (D * A * B)) :=
    memSchattenClass_one_comp_left hS B
  have hcycle : opTrace (D * A * B) = opTrace (B * (D * A * B)) := by
    calc
      opTrace (D * A * B) = opTrace ((D * A * B) * B) := by
        rw [mul_assoc (D * A), hBB]
      _ = opTrace (B * (D * A * B)) := (hS.one_opTrace_comp_comm B).symm
  have hAFA : A * F * A = (phaseSchur a 1).op := (phaseSchur_one a).symm
  have hAUA : A * U * A = (phaseSchur a (-1)).op := by
    rw [phaseSchur_neg_one, ← hAFA, adjoint_mul_soninL2, adjoint_mul_soninL2]
    have hAdjA : adjoint A = A := adjoint_indicatorCutoff_central a
    have hAdjF : adjoint F = U := fourierUnitary.adjoint_eq_symm
    rw [hAdjA, hAdjF, ← mul_assoc]
  have hAEFA : A * E * F * A = (Real.sqrt r⁻¹ : ℂ) • (phaseSchur a r⁻¹).op :=
    cutoff_dilation_fourier a r⁻¹ (inv_pos.mpr hr)
  have hFB : F * B = A * F := by simp only [hB, ← mul_assoc, hFU, one_mul]
  have hBU : B * U = U * A := by rw [hB, mul_assoc, hFU, mul_one]
  have hfac : F * (B * (D * A * B)) * U = (A * E * F * A) * (A * U * A) := by
    calc
      _ = (F * B) * (D * A) * (B * U) := by simp only [mul_assoc]
      _ = A * (F * D) * A * (U * A) := by rw [hFB, hBU]; simp only [mul_assoc]
      _ = (A * E * F) * (A * A) * (U * A) := by rw [hFD, hAA]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  change opTrace (D * A * B) = _
  rw [hcycle, ← trace_conjugate _ F U hBS hUF, hfac, hAUA, hAEFA, smul_mul_assoc,
    opTrace_smul]

/-- Exact trace of the original normalized dilation against the actual central
physical/Fourier cutoff product. -/
theorem opTrace_dilation_timeBand (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    opTrace (dilationCLM r hr *
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) *
      fourierCutoff (centralInterval a) (measurableSet_centralInterval a)) =
    (Real.sqrt r⁻¹ : ℂ) *
      ∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
        Complex.exp (((2 * Real.pi * (1 - r⁻¹) * x * y) : ℝ) * Complex.I) := by
  change opTrace (dilationCLM r hr *
    indicatorCutoff (Icc (-a) a) measurableSet_Icc *
    fourierCutoff (Icc (-a) a) measurableSet_Icc) = _
  rw [trace_dilation_reduce a r ha hr]
  change (Real.sqrt r⁻¹ : ℂ) *
    opTrace ((phaseSchur a r⁻¹).op ∘L (phaseSchur a (-1)).op) = _
  rw [phaseSchur_trace_product]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  push_cast
  ring

private theorem re_trace_selfAdjoint_timeBand (a : ℝ) (ha : 0 < a)
    (D : Op) (hD : adjoint D = D) :
    (opTrace (D * (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) *
        fourierCutoff (centralInterval a) (measurableSet_centralInterval a) +
      fourierCutoff (centralInterval a) (measurableSet_centralInterval a) *
        indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)))).re =
    2 * (opTrace (D * indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) *
      fourierCutoff (centralInterval a) (measurableSet_centralInterval a))).re := by
  let A := indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
  let B := fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
  have hAB : MemSchattenClass 1 (A * B) :=
    memSchattenClass_one_indicatorCutoff_fourierCutoff_central a a ha
  have hBA : MemSchattenClass 1 (B * A) :=
    memSchattenClass_one_fourierCutoff_indicatorCutoff_central a a ha
  have hDAB : MemSchattenClass 1 (D * (A * B)) := memSchattenClass_one_comp_left hAB D
  have hDBA : MemSchattenClass 1 (D * (B * A)) := memSchattenClass_one_comp_left hBA D
  have hrev : opTrace (D * (B * A)) = star (opTrace (D * A * B)) := by
    calc
      _ = opTrace ((B * A) * D) := hBA.one_opTrace_comp_comm D
      _ = opTrace (adjoint (D * A * B)) := by
        rw [adjoint_mul_soninL2, adjoint_mul_soninL2, hD]
        rw [show adjoint A = A from adjoint_indicatorCutoff_central a,
          show adjoint B = B from adjoint_fourierCutoff_central a, mul_assoc]
      _ = _ := opTrace_adjoint _
  change (opTrace (D * (A * B + B * A))).re = 2 * (opTrace (D * A * B)).re
  rw [mul_add, opTrace_add_of_memSchattenClass_one hDAB hDBA, hrev, ← mul_assoc]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- Real trace of the complete original symmetric dilation response. Both
normalized dilation directions and both time-band legs are retained. -/
theorem re_opTrace_centralSoninCornerCorrectionResponse_dilationSum
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) :
    (opTrace (centralSoninCornerCorrectionResponse a (dilationSum r hr))).re =
      2 * (((Real.sqrt r⁻¹ : ℂ) *
        ∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
          Complex.exp (((2 * Real.pi * (1 - r⁻¹) * x * y) : ℝ) * Complex.I)) +
        (Real.sqrt r : ℂ) *
        ∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
          Complex.exp (((2 * Real.pi * (1 - r) * x * y) : ℝ) * Complex.I)).re := by
  let A := indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
  let B := fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
  have hAB : MemSchattenClass 1 (A * B) :=
    memSchattenClass_one_indicatorCutoff_fourierCutoff_central a a ha
  have hDAB : MemSchattenClass 1 (dilationCLM r (zero_lt_one.trans hr) * A * B) := by
    rw [mul_assoc]
    exact memSchattenClass_one_comp_left hAB _
  have hEAB : MemSchattenClass 1
      (dilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) * A * B) := by
    rw [mul_assoc]
    exact memSchattenClass_one_comp_left hAB _
  rw [opTrace_centralSoninCornerCorrectionResponse_eq_timeBand a ha]
  simp only [centralPhysicalForbidden, centralFourierForbidden,
    ← indicatorCutoff_eq_physicalForbidden_starProjection,
    ← fourierCutoff_eq_fourierForbidden_starProjection]
  change (opTrace (dilationSum r hr * (A * B + B * A))).re = _
  rw [re_trace_selfAdjoint_timeBand a ha _ (by
    rw [dilationSum, map_add, adjoint_adjoint]; exact add_comm _ _)]
  rw [dilationSum, adjoint_dilationCLM, add_mul, add_mul,
    opTrace_add_of_memSchattenClass_one hDAB hEAB,
    opTrace_dilation_timeBand a r ha (zero_lt_one.trans hr),
    opTrace_dilation_timeBand a r⁻¹ ha (inv_pos.mpr (zero_lt_one.trans hr)), inv_inv]

end RHTower
