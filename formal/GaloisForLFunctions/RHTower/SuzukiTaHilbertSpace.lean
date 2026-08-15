import GaloisForLFunctions.HTGeometry.CoerciveInnerProductRenorm
import GaloisForLFunctions.RHTower.SuzukiRayleighInfimum

/-!
# Suzuki's form Hilbert space

This file constructs the actual Hilbert space `H(T_a)` used in Suzuki's deficiency-index
argument.  We choose the canonical point below the form lower bound and prove, rather than assume,
that the resulting energy inner product is complete and equivalent to the closed-form norm.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Coercive metric operator for Suzuki's form at
`lambda = -boundedPerturbedFormShift`. -/
def suzukiTaMetricDatum (a : SuzukiPositiveAperture) :
    CoerciveInnerProductRenorm.Datum (CCMArchimedeanFormDomain a) where
  op := boundedPerturbedFormRiesz
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
  selfAdjoint := boundedPerturbedFormRiesz_isSelfAdjoint
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
  coercive u := by
    simpa only [RCLike.re_to_complex] using boundedPerturbedFormRiesz_coercive
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a) u

/-- Suzuki's canonical `H(T_a)` at `lambda = -boundedPerturbedFormShift`. -/
abbrev SuzukiTaHilbert (a : SuzukiPositiveAperture) :=
  CoerciveInnerProductRenorm.Carrier (suzukiTaMetricDatum a)

/-- Algebraic identity from the energy Hilbert space to the closed form domain. -/
def suzukiTaToFormLinearEquiv (a : SuzukiPositiveAperture) :
    SuzukiTaHilbert a ≃ₗ[ℂ] CCMArchimedeanFormDomain a :=
  CoerciveInnerProductRenorm.toOld (suzukiTaMetricDatum a)

/-- Bounded identity from the energy norm to the closed-form norm. -/
def suzukiTaToFormCLM (a : SuzukiPositiveAperture) :
    SuzukiTaHilbert a →L[ℂ] CCMArchimedeanFormDomain a :=
  LinearMap.mkContinuous (suzukiTaToFormLinearEquiv a).toLinearMap 1 (by
    intro x
    change
      ‖CoerciveInnerProductRenorm.toOld (suzukiTaMetricDatum a) x‖ ≤ 1 * ‖x‖
    simpa using CoerciveInnerProductRenorm.old_norm_le (suzukiTaMetricDatum a) x)

/-- Bounded identity from the closed-form norm to the energy norm. -/
def suzukiTaFromFormCLM (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] SuzukiTaHilbert a :=
  LinearMap.mkContinuous (suzukiTaToFormLinearEquiv a).symm.toLinearMap
    (‖(suzukiTaMetricDatum a).op‖ + 1) (by
      intro x
      change
        ‖(CoerciveInnerProductRenorm.toOld (suzukiTaMetricDatum a)).symm x‖ ≤
          (‖(suzukiTaMetricDatum a).op‖ + 1) * ‖x‖
      simpa using CoerciveInnerProductRenorm.norm_le (suzukiTaMetricDatum a)
        ((CoerciveInnerProductRenorm.toOld (suzukiTaMetricDatum a)).symm x))

/-- The energy Hilbert space and the closed form domain are topologically linearly equivalent. -/
def suzukiTaEquivForm (a : SuzukiPositiveAperture) :
    SuzukiTaHilbert a ≃L[ℂ] CCMArchimedeanFormDomain a where
  toLinearEquiv := suzukiTaToFormLinearEquiv a
  continuous_toFun := (suzukiTaToFormCLM a).continuous
  continuous_invFun := (suzukiTaFromFormCLM a).continuous

@[simp] theorem suzukiTaToFormCLM_fromForm
    (a : SuzukiPositiveAperture) (x : CCMArchimedeanFormDomain a) :
    suzukiTaToFormCLM a (suzukiTaFromFormCLM a x) = x := rfl

@[simp] theorem suzukiTaFromFormCLM_toForm
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) :
    suzukiTaFromFormCLM a (suzukiTaToFormCLM a x) = x := rfl

/-- Continuous injective physical embedding of `H(T_a)` into interval `L²`. -/
def suzukiTaPhysicalEmbedding (a : SuzukiPositiveAperture) :
    SuzukiTaHilbert a →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  (suzukiWeilIntervalFormEmbedding a).comp (suzukiTaToFormCLM a)

theorem suzukiTaPhysicalEmbedding_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiTaPhysicalEmbedding a) :=
  (suzukiWeilIntervalFormEmbedding_injective a).comp
    (suzukiTaToFormLinearEquiv a).injective

theorem denseRange_suzukiTaFromFormCLM (a : SuzukiPositiveAperture) :
    DenseRange (suzukiTaFromFormCLM a) :=
  (suzukiTaEquivForm a).symm.surjective.denseRange

/-- Suzuki's smooth compactly supported source core is dense in the actual energy Hilbert space. -/
theorem denseRange_ccmComplexSmoothInteriorSource_toSuzukiTa
    (a : SuzukiPositiveAperture) :
    DenseRange (fun u : CCMComplexSmoothInteriorSource a =>
      suzukiTaFromFormCLM a u.toCCMFormVector) := by
  exact (denseRange_suzukiTaFromFormCLM a).comp
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a)
    (suzukiTaFromFormCLM a).continuous

/-- Exact energy inner product: `T_a(x,y) - lambda (Jx,Jy)` at the canonical real
`lambda = -boundedPerturbedFormShift`. -/
theorem inner_suzukiTa_eq
    (a : SuzukiPositiveAperture) (x y : SuzukiTaHilbert a) :
    inner ℂ x y =
      suzukiWeilIntervalForm a (suzukiTaToFormCLM a x) (suzukiTaToFormCLM a y) +
        (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
          inner ℂ (suzukiTaPhysicalEmbedding a x) (suzukiTaPhysicalEmbedding a y) := by
  rw [CoerciveInnerProductRenorm.inner_def]
  change
    inner ℂ
        (boundedPerturbedFormRiesz
          (suzukiWeilIntervalFormEmbedding a)
          (suzukiWeilIntervalBoundedRemainder a)
          (suzukiTaToFormCLM a x))
        (suzukiTaToFormCLM a y) = _
  rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
    inner_smul_left, (suzukiWeilIntervalFormEmbedding a).adjoint_inner_left,
    (suzukiWeilIntervalFormEmbedding a).adjoint_inner_left]
  simp only [suzukiWeilIntervalForm, suzukiTaPhysicalEmbedding,
    ContinuousLinearMap.comp_apply, Complex.conj_ofReal]

end RHTower
