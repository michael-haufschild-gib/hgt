import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.SoninL2Model

/-!
# Archimedean quantized calculus of Connes--Consani

This file constructs the literal real-line Hardy involution used in the quantized differential
appendix of Connes--Consani, *Weil positivity and trace formula, the archimedean place*.  With the
source Fourier convention, `P` is multiplication by the indicator of `[0,∞)` and

`H = 2 F P F⁻¹ - 1`.

For an intrinsic Schwartz symbol `f`, multiplication on `L²(ℝ)` is bounded without an external
boundedness hypothesis.  The quantized differential is the source commutator `[H,M_f]`.  The
file proves the exact projection, involution, and cross-Hardy-block identities needed before the
Schatten estimate.  Trace class is a separate analytic theorem; it is not assumed here.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap

namespace RHTower

/-- Source half-line projection `P = 1_[0,∞)` on `L²(ℝ)`. -/
def ccmPositiveHalfLineProjection : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Set.Ici 0) measurableSet_Ici

theorem ccmPositiveHalfLineProjection_isStarProjection :
    IsStarProjection ccmPositiveHalfLineProjection :=
  indicatorCutoff_isStarProjection (Set.Ici 0) measurableSet_Ici

/-- Source Hardy projection on the spectral line: `F P F⁻¹`. -/
def ccmHardyProjection : SoninL2 →L[ℂ] SoninL2 :=
  fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    ccmPositiveHalfLineProjection ∘L
      fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem ccmHardyProjection_apply (x : SoninL2) :
    ccmHardyProjection x =
      fourierUnitary
        (ccmPositiveHalfLineProjection (fourierUnitary.symm x)) :=
  rfl

theorem ccmHardyProjection_idempotent :
    IsIdempotentElem ccmHardyProjection := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp, ccmHardyProjection_apply, ccmHardyProjection_apply,
    LinearIsometryEquiv.symm_apply_apply]
  have hP := ccmPositiveHalfLineProjection_isStarProjection.isIdempotentElem
  rw [isIdempotentElem_iff] at hP
  have hx := DFunLike.congr_fun hP (fourierUnitary.symm x)
  simpa only [mul_apply_eq_comp] using congrArg fourierUnitary hx

theorem ccmHardyProjection_symmetric :
    ccmHardyProjection.toLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℂ (ccmHardyProjection x) y =
        inner ℂ
          (fourierUnitary
            (ccmPositiveHalfLineProjection (fourierUnitary.symm x)))
          (fourierUnitary (fourierUnitary.symm y)) := by
            rw [ccmHardyProjection_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ
          (ccmPositiveHalfLineProjection (fourierUnitary.symm x))
          (fourierUnitary.symm y) :=
      fourierUnitary.inner_map_map _ _
    _ = inner ℂ (fourierUnitary.symm x)
          (ccmPositiveHalfLineProjection (fourierUnitary.symm y)) :=
      indicatorCutoff_symmetric (Set.Ici 0) measurableSet_Ici _ _
    _ = inner ℂ
          (fourierUnitary (fourierUnitary.symm x))
          (fourierUnitary
            (ccmPositiveHalfLineProjection (fourierUnitary.symm y))) :=
      (fourierUnitary.inner_map_map _ _).symm
    _ = inner ℂ x (ccmHardyProjection y) := by
      rw [LinearIsometryEquiv.apply_symm_apply, ccmHardyProjection_apply]

theorem ccmHardyProjection_isStarProjection :
    IsStarProjection ccmHardyProjection := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (show IsIdempotentElem ccmHardyProjection from ccmHardyProjection_idempotent),
    ccmHardyProjection_symmetric⟩

/-- Literal source Hardy involution `H = 2 F P F⁻¹ - 1`. -/
def ccmHardyInvolution : SoninL2 →L[ℂ] SoninL2 :=
  (2 : ℂ) • ccmHardyProjection - 1

@[simp]
theorem ccmHardyInvolution_apply (x : SoninL2) :
    ccmHardyInvolution x = (2 : ℂ) • ccmHardyProjection x - x :=
  rfl

theorem ccmHardyInvolution_apply_apply (x : SoninL2) :
    ccmHardyInvolution (ccmHardyInvolution x) = x := by
  have hQ := ccmHardyProjection_idempotent
  rw [isIdempotentElem_iff] at hQ
  have hQx := DFunLike.congr_fun hQ x
  simp only [mul_apply_eq_comp] at hQx
  rw [ccmHardyInvolution_apply, ccmHardyInvolution_apply, map_sub, map_smul, hQx]
  module

theorem ccmHardyInvolution_sq_eq_one :
    ccmHardyInvolution * ccmHardyInvolution = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change ccmHardyInvolution (ccmHardyInvolution x) = x
  exact ccmHardyInvolution_apply_apply x

theorem ccmHardyInvolution_isSelfAdjoint :
    IsSelfAdjoint ccmHardyInvolution := by
  rw [IsSelfAdjoint, ccmHardyInvolution, star_sub, star_smul,
    ccmHardyProjection_isStarProjection.isSelfAdjoint.star_eq, star_one]
  norm_num

theorem ccmHardyInvolution_inner_map_map (x y : SoninL2) :
    inner ℂ (ccmHardyInvolution x) (ccmHardyInvolution y) = inner ℂ x y := by
  have hstar := ccmHardyInvolution_isSelfAdjoint.star_eq
  change ContinuousLinearMap.adjoint ccmHardyInvolution = ccmHardyInvolution at hstar
  calc
    inner ℂ (ccmHardyInvolution x) (ccmHardyInvolution y) =
        inner ℂ x
          (ContinuousLinearMap.adjoint ccmHardyInvolution
            (ccmHardyInvolution y)) :=
      (ContinuousLinearMap.adjoint_inner_right ccmHardyInvolution x
        (ccmHardyInvolution y)).symm
    _ = inner ℂ x (ccmHardyInvolution (ccmHardyInvolution y)) := by
      rw [hstar]
    _ = inner ℂ x y := by rw [ccmHardyInvolution_apply_apply]

theorem norm_ccmHardyInvolution (x : SoninL2) :
    ‖ccmHardyInvolution x‖ = ‖x‖ := by
  have hsq : ‖ccmHardyInvolution x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
      ccmHardyInvolution_inner_map_map]
  nlinarith [norm_nonneg (ccmHardyInvolution x), norm_nonneg x]

/-- Pointwise multiplication by a Schwartz symbol on `L²(ℝ)`.  Schwartz membership supplies the
measurability and uniform bound internally. -/
def ccmSchwartzMultiplier (f : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    f.continuous.measurable
    (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f)
    (fun x => SchwartzMap.norm_le_seminorm ℂ f x)

theorem norm_ccmSchwartzMultiplier_le (f : 𝓢(ℝ, ℂ)) :
    ‖ccmSchwartzMultiplier f‖ ≤ SchwartzMap.seminorm ℂ 0 0 f :=
  norm_lpBoundedMulCLM_le f.continuous.measurable
    (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f)
    (fun x => SchwartzMap.norm_le_seminorm ℂ f x)

theorem ccmSchwartzMultiplier_coeFn (f : 𝓢(ℝ, ℂ)) (x : SoninL2) :
    (ccmSchwartzMultiplier f x : ℝ → ℂ) =ᵐ[volume]
      fun t => f t * x t :=
  lpBoundedMulCLM_coeFn f.continuous.measurable
    (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) f)
    (fun t => SchwartzMap.norm_le_seminorm ℂ f t) x

/-- Connes--Consani quantized differential `[H,M_f]`. -/
def ccmQuantizedDifferential (f : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  ccmHardyInvolution * ccmSchwartzMultiplier f -
    ccmSchwartzMultiplier f * ccmHardyInvolution

/-- Since `H = 2Q-1`, its commutator is twice the Hardy-projection commutator. -/
theorem ccmQuantizedDifferential_eq_two_smul_projectionCommutator
    (f : 𝓢(ℝ, ℂ)) :
    ccmQuantizedDifferential f =
      (2 : ℂ) •
        (ccmHardyProjection * ccmSchwartzMultiplier f -
          ccmSchwartzMultiplier f * ccmHardyProjection) := by
  apply ContinuousLinearMap.ext
  intro x
  change
    ccmHardyInvolution (ccmSchwartzMultiplier f x) -
        ccmSchwartzMultiplier f (ccmHardyInvolution x) =
      (2 : ℂ) •
        (ccmHardyProjection (ccmSchwartzMultiplier f x) -
          ccmSchwartzMultiplier f (ccmHardyProjection x))
  rw [ccmHardyInvolution_apply, ccmHardyInvolution_apply, map_sub, map_smul]
  module

/-- Projection commutator is exactly the difference of the two cross-Hardy blocks. -/
theorem ccmHardyProjection_commutator_eq_crossBlocks
    (f : 𝓢(ℝ, ℂ)) :
    ccmHardyProjection * ccmSchwartzMultiplier f -
        ccmSchwartzMultiplier f * ccmHardyProjection =
      ccmHardyProjection * ccmSchwartzMultiplier f * (1 - ccmHardyProjection) -
        (1 - ccmHardyProjection) * ccmSchwartzMultiplier f * ccmHardyProjection := by
  noncomm_ring

/-- Literal source block decomposition of the quantized differential. -/
theorem ccmQuantizedDifferential_eq_two_smul_crossBlocks
    (f : 𝓢(ℝ, ℂ)) :
    ccmQuantizedDifferential f =
      (2 : ℂ) •
        (ccmHardyProjection * ccmSchwartzMultiplier f * (1 - ccmHardyProjection) -
          (1 - ccmHardyProjection) * ccmSchwartzMultiplier f *
            ccmHardyProjection) := by
  rw [ccmQuantizedDifferential_eq_two_smul_projectionCommutator,
    ccmHardyProjection_commutator_eq_crossBlocks]

end RHTower
