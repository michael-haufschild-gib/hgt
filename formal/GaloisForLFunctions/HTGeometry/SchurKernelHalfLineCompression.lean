import GaloisForLFunctions.HTGeometry.WienerHopfPlaneWaveWeyl
import GaloisForLFunctions.HTGeometry.SchurKernelComposition
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Half-line compression of Schur kernels on the line

`P₊ = E R` is the orthogonal projection of `L²(ℝ)` onto functions supported in `[0, ∞)`, where
`R : L²(ℝ) → L²(0,∞)` is restriction and `E = R*` is extension by zero (`R E = 1`).  For a Schur
kernel `k` on `ℝ`, the compression `R K E` is the Schur operator on the half-line with the same
kernel.  A kernel that is a constant multiple of another gives the same multiple of the operator.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-- Restriction `R : L²(ℝ) → L²(0,∞)`. -/
def halfLineRestrict : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] L²₊ :=
  LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Ici 0)

theorem halfLineRestrict_coeFn (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (halfLineRestrict f : ℝ → ℂ) =ᵐ[halfLineMeasure] f :=
  LpToLpRestrictCLM_coeFn ℂ (Ici 0) f

theorem memLp_indicator_halfLine (u : L²₊) :
    MemLp ((Ici (0 : ℝ)).indicator (u : ℝ → ℂ)) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ici).mpr (Lp.memLp u)

theorem indicator_ae_eq_of_halfLine {f g : ℝ → ℂ} (h : f =ᵐ[halfLineMeasure] g) :
    (Ici (0 : ℝ)).indicator f =ᵐ[volume] (Ici (0 : ℝ)).indicator g :=
  (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ici).mp h

/-- Extension by zero, as a linear map. -/
def halfLineExtendLM : L²₊ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun u := (memLp_indicator_halfLine u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [indicator_ae_eq_of_halfLine (Lp.coeFn_add u v)] with x hx
    rw [hx]
    by_cases hmem : x ∈ Ici (0 : ℝ) <;> simp [hmem]
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [indicator_ae_eq_of_halfLine (Lp.coeFn_smul c u)] with x hx
    rw [hx]
    by_cases hmem : x ∈ Ici (0 : ℝ) <;> simp [hmem]

theorem norm_halfLineExtendLM (u : L²₊) : ‖halfLineExtendLM u‖ = ‖u‖ := by
  change ‖(memLp_indicator_halfLine u).toLp _‖ = _
  rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici]

/-- Extension by zero `E : L²(0,∞) → L²(ℝ)`. -/
def halfLineExtend : L²₊ →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous halfLineExtendLM 1 fun u => by rw [norm_halfLineExtendLM, one_mul]

theorem halfLineExtend_coeFn (u : L²₊) :
    (halfLineExtend u : ℝ → ℂ) =ᵐ[volume] (Ici (0 : ℝ)).indicator (u : ℝ → ℂ) :=
  MemLp.coeFn_toLp (memLp_indicator_halfLine u)

/-- `R E = 1`. -/
theorem halfLineRestrict_comp_halfLineExtend :
    halfLineRestrict ∘L halfLineExtend = ContinuousLinearMap.id ℂ L²₊ := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [halfLineRestrict_coeFn (halfLineExtend u),
    ae_restrict_of_ae (halfLineExtend_coeFn u),
    indicator_ae_eq_restrict (μ := volume) (f := (u : ℝ → ℂ)) measurableSet_Ici] with x h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2, h3]
  rfl

/-- `E = R*`. -/
theorem adjoint_halfLineExtend : ContinuousLinearMap.adjoint halfLineExtend = halfLineRestrict := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun f u => ?_).symm
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 : ∫ x, inner ℂ ((f : ℝ → ℂ) x) ((halfLineExtend u : ℝ → ℂ) x) ∂volume =
      ∫ x, (Ici (0 : ℝ)).indicator (fun x => inner ℂ ((f : ℝ → ℂ) x) ((u : ℝ → ℂ) x)) x := by
    refine integral_congr_ae ?_
    filter_upwards [halfLineExtend_coeFn u] with x hx
    rw [hx]
    by_cases hmem : x ∈ Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, inner_zero_right]
  rw [h1, integral_indicator measurableSet_Ici]
  refine integral_congr_ae ?_
  filter_upwards [halfLineRestrict_coeFn f] with x hx
  rw [hx]

/-- The half-line compression of a Schur kernel on `ℝ`: same kernel, half-line measure. -/
def SchurKernel.toHalfLine (k : SchurKernel (volume : Measure ℝ)) : SchurKernel halfLineMeasure where
  toFun := k.toFun
  measurable := k.measurable
  bound := k.bound
  row y := (setLIntegral_le_lintegral _ _).trans (k.row y)
  col z := (setLIntegral_le_lintegral _ _).trans (k.col z)

theorem SchurKernel.toHalfLine_toFun (k : SchurKernel (volume : Measure ℝ)) :
    k.toHalfLine.toFun = k.toFun := rfl

/-- **`R K E` is the half-line Schur operator with the same kernel.** -/
theorem SchurKernel.halfLineRestrict_comp_op_comp_halfLineExtend (k : SchurKernel (volume : Measure ℝ)) :
    halfLineRestrict ∘L k.op ∘L halfLineExtend = k.toHalfLine.op := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [halfLineRestrict_coeFn (k.op (halfLineExtend u)),
    ae_restrict_of_ae (k.op_coeFn (halfLineExtend u)), k.toHalfLine.op_coeFn u] with y h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3,
    SchurKernel.apply, SchurKernel.apply]
  have e : ∫ z, k.toFun y z * (halfLineExtend u : ℝ → ℂ) z =
      ∫ z, (Ici (0 : ℝ)).indicator (fun z => k.toFun y z * (u : ℝ → ℂ) z) z := by
    refine integral_congr_ae ?_
    filter_upwards [halfLineExtend_coeFn u] with z hz
    rw [hz, Set.indicator_mul_right]
  rw [e, integral_indicator measurableSet_Ici]
  rfl

/-- A kernel that is `c` times another gives `c` times the operator. -/
theorem SchurKernel.op_eq_smul_of_toFun {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {k₁ k₂ : SchurKernel μ} (c : ℂ) (h : ∀ y z, k₂.toFun y z = c * k₁.toFun y z) :
    k₂.op = c • k₁.op := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [k₂.op_coeFn f, Lp.coeFn_smul c (k₁.op f), k₁.op_coeFn f] with y h1 h2 h3
  rw [h1, _root_.smul_apply, h2, Pi.smul_apply, h3, SchurKernel.apply,
    SchurKernel.apply, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [h]
  ring

end GaloisForLFunctions.HTGeometry
