import GaloisForLFunctions.RHTower.ProlateEvenCrossSpectralContinuity
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant
import GaloisForLFunctions.RHTower.FiniteTimeBandFourierSchatten
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier
import GaloisForLFunctions.HTGeometry.SchattenOneBanach

noncomputable section

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

abbrev ComplexUnitIntervalL2 :=
  Lp ℂ 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1))

/-- Continuous complex kernels on the unit square act linearly on complex interval `L²`. -/
def complexContinuousKernelOperatorMap :
    C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ) →L[ℂ]
      (ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2) := by
  let toLpY : C(ClosedInterval (-1 : ℝ) 1, ℂ) →L[ℂ] ComplexUnitIntervalL2 :=
    ContinuousMap.toLp (α := ClosedInterval (-1 : ℝ) 1) (E := ℂ) 2
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℂ
  let pairing : ComplexUnitIntervalL2 →L[ℂ] (ComplexUnitIntervalL2 →L[ℂ] ℂ) :=
    complexMulBilinear.lpPairing (volume : Measure (ClosedInterval (-1 : ℝ) 1)) 2 2
  let fieldToLp : C(ClosedInterval (-1 : ℝ) 1, ComplexUnitIntervalL2 →L[ℂ] ℂ) →L[ℂ]
      Lp (ComplexUnitIntervalL2 →L[ℂ] ℂ) 2
        (volume : Measure (ClosedInterval (-1 : ℝ) 1)) :=
    ContinuousMap.toLp (α := ClosedInterval (-1 : ℝ) 1)
      (E := ComplexUnitIntervalL2 →L[ℂ] ℂ) 2
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℂ
  exact
    kernelOperatorMap (E := ComplexUnitIntervalL2)
        (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ∘L
      fieldToLp ∘L
      pairing.compLeftContinuous ℂ (ClosedInterval (-1 : ℝ) 1) ∘L
      toLpY.compLeftContinuous ℂ (ClosedInterval (-1 : ℝ) 1) ∘L
      continuousMapCurryCLM (ClosedInterval (-1 : ℝ) 1) (ClosedInterval (-1 : ℝ) 1)

def complexKernelSectionContinuous
    (K : C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ)) :
    C(ClosedInterval (-1 : ℝ) 1, ComplexUnitIntervalL2) where
  toFun x := ContinuousMap.toLp 2
    (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℂ (K.curry x)
  continuous_toFun := (ContinuousMap.toLp 2
    (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℂ).continuous.comp K.curry.continuous

def complexKernelFunctionalContinuous
    (K : C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ)) :
    C(ClosedInterval (-1 : ℝ) 1, ComplexUnitIntervalL2 →L[ℂ] ℂ) where
  toFun x := (complexMulBilinear.lpPairing
    (volume : Measure (ClosedInterval (-1 : ℝ) 1)) 2 2)
      (complexKernelSectionContinuous K x)
  continuous_toFun := (complexMulBilinear.lpPairing
    (volume : Measure (ClosedInterval (-1 : ℝ) 1)) 2 2).continuous.comp
      (complexKernelSectionContinuous K).continuous

def complexKernelFunctionalField
    (K : C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ)) :
    Lp (ComplexUnitIntervalL2 →L[ℂ] ℂ) 2
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) :=
  ContinuousMap.toLp 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℂ
    (complexKernelFunctionalContinuous K)

def complexContinuousKernelOperator
    (K : C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ)) :
    ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2 :=
  kernelOperator (volume : Measure (ClosedInterval (-1 : ℝ) 1))
    (complexKernelFunctionalField K)

theorem complexContinuousKernelOperator_eq_map
    (K : C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ)) :
    complexContinuousKernelOperator K = complexContinuousKernelOperatorMap K := rfl

/-- Pointwise complexification on continuous unit-square kernels. -/
def complexifyUnitKernelCLM :
    C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℝ) →L[ℝ]
      C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ) :=
  Complex.ofRealCLM.compLeftContinuous ℝ
    (ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1)

/-- Complexification of the real sinc kernel. -/
def complexSincKernelContinuous (c : ℝ) :
    C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℂ) :=
  complexifyUnitKernelCLM (sincKernelContinuous c)

/-- Complex unit-band Slepian operator. -/
def complexBandOperatorL2 (c : ℝ) :
    ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2 :=
  complexContinuousKernelOperator (complexSincKernelContinuous c)

theorem hasDerivAt_sincKernelContinuous (c : ℝ) :
    HasDerivAt sincKernelContinuous (cosKernelContinuous c) c := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ : (0 : ℝ) < ε * Real.pi / 2 := by positivity
  filter_upwards [Metric.ball_mem_nhds c hδ] with t ht
  have hdist : |t - c| ≤ ε * Real.pi / 2 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ht.le
  have hkey :
      ‖sincKernelContinuous t - sincKernelContinuous c -
          (t - c) • cosKernelContinuous c‖ ≤ 2 * (t - c) ^ 2 / Real.pi := by
    have h := norm_sincKernel_taylor_le c (t - c)
    rwa [show c + (t - c) = t by ring] at h
  refine hkey.trans ?_
  rw [Real.norm_eq_abs]
  have hsq : (t - c) ^ 2 = |t - c| * |t - c| := by
    rw [← sq_abs]
    ring
  rw [hsq, div_le_iff₀ hpi]
  nlinarith [abs_nonneg (t - c), hdist, hpi.le]

theorem continuous_complexSincKernelContinuous :
    Continuous complexSincKernelContinuous := by
  exact complexifyUnitKernelCLM.continuous.comp
    (continuous_iff_continuousAt.2 fun c => (hasDerivAt_sincKernelContinuous c).continuousAt)

theorem continuous_complexBandOperatorL2 : Continuous complexBandOperatorL2 := by
  change Continuous (fun c => complexContinuousKernelOperatorMap
    (complexSincKernelContinuous c))
  exact complexContinuousKernelOperatorMap.continuous.comp continuous_complexSincKernelContinuous

theorem isCompactOperator_complexBandOperatorL2 (c : ℝ) :
    IsCompactOperator (complexBandOperatorL2 c) := by
  unfold complexBandOperatorL2 complexContinuousKernelOperator
  exact isCompactOperator_kernelOperator
    (volume : Measure (ClosedInterval (-1 : ℝ) 1)) _

theorem complexBandOperatorL2_coeFn (c : ℝ) (f : ComplexUnitIntervalL2) :
    (complexBandOperatorL2 c f : ClosedInterval (-1 : ℝ) 1 → ℂ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval (-1 : ℝ) 1,
        (sincKernelSmooth c (x : ℝ) (y : ℝ) : ℂ) * f y := by
  filter_upwards [
    (evalBilinear (𝕜 := ℂ) (E := ComplexUnitIntervalL2)).coeFn_holder
      (r := (2 : ENNReal)) (complexKernelFunctionalField (complexSincKernelContinuous c))
      (Lp.const ∞ (volume : Measure (ClosedInterval (-1 : ℝ) 1)) f),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval (-1 : ℝ) 1)))
      (complexKernelFunctionalContinuous (complexSincKernelContinuous c)),
    Lp.coeFn_const (p := ∞) (volume : Measure (ClosedInterval (-1 : ℝ) 1)) f
  ] with x hholder hfield hconst
  rw [complexBandOperatorL2, complexContinuousKernelOperator, kernelOperator,
    kernelOperatorMap_apply, hholder, complexKernelFunctionalField, hfield, hconst]
  change (complexMulBilinear.lpPairing
    (volume : Measure (ClosedInterval (-1 : ℝ) 1)) 2 2
      ((ContinuousMap.toLp (α := ClosedInterval (-1 : ℝ) 1) (E := ℂ) 2
        (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℂ)
        ((complexSincKernelContinuous c).curry x))) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval (-1 : ℝ) 1)))
    ((complexSincKernelContinuous c).curry x)] with y hy
  change complexMulBilinear
      ((ContinuousMap.toLp 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1)) ℂ
        ((complexSincKernelContinuous c).curry x) :
          ClosedInterval (-1 : ℝ) 1 → ℂ) y)
      (f y) = _
  rw [hy]
  simp [complexMulBilinear, complexSincKernelContinuous, complexifyUnitKernelCLM,
    sincKernelContinuous, sincKernelSmooth]

def complexUnitBandReflectionIsometry :
    ComplexUnitIntervalL2 →ₗᵢ[ℂ] ComplexUnitIntervalL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ unitIntervalNeg measurePreserving_unitIntervalNeg

def complexUnitBandReflection :
    ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2 :=
  complexUnitBandReflectionIsometry.toContinuousLinearMap

theorem complexUnitBandReflection_ae (f : ComplexUnitIntervalL2) :
    (complexUnitBandReflection f : ClosedInterval (-1 : ℝ) 1 → ℂ) =ᵐ[volume]
      fun x => f (unitIntervalNeg x) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_unitIntervalNeg

@[simp] theorem complexUnitBandReflection_involutive (f : ComplexUnitIntervalL2) :
    complexUnitBandReflection (complexUnitBandReflection f) = f := by
  apply Lp.ext
  have hinner := (complexUnitBandReflection_ae f).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [complexUnitBandReflection_ae (complexUnitBandReflection f), hinner]
      with x hout hin
  rw [hout]
  simpa [Function.comp_apply, unitIntervalNeg_involutive] using hin

@[simp] theorem norm_complexUnitBandReflection (f : ComplexUnitIntervalL2) :
    ‖complexUnitBandReflection f‖ = ‖f‖ :=
  complexUnitBandReflectionIsometry.norm_map f

theorem complexBandOperatorL2_complexUnitBandReflection (c : ℝ)
    (f : ComplexUnitIntervalL2) :
    complexBandOperatorL2 c (complexUnitBandReflection f) =
      complexUnitBandReflection (complexBandOperatorL2 c f) := by
  apply Lp.ext
  have hBneg := (complexBandOperatorL2_coeFn c f).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [complexBandOperatorL2_coeFn c (complexUnitBandReflection f),
    complexUnitBandReflection_ae (complexBandOperatorL2 c f), hBneg]
      with x hleft hright hBnegx
  have hBnegx' : (complexBandOperatorL2 c f : ClosedInterval (-1 : ℝ) 1 → ℂ)
      (unitIntervalNeg x) = ∫ y : ClosedInterval (-1 : ℝ) 1,
        (sincKernelSmooth c (unitIntervalNeg x : ℝ) (y : ℝ) : ℂ) * f y := by
    simpa only [Function.comp_apply] using hBnegx
  rw [hleft, hright, hBnegx']
  calc
    (∫ y : ClosedInterval (-1 : ℝ) 1,
        (sincKernelSmooth c (x : ℝ) (y : ℝ) : ℂ) * (complexUnitBandReflection f) y) =
        ∫ y : ClosedInterval (-1 : ℝ) 1,
          (sincKernelSmooth c (x : ℝ) (y : ℝ) : ℂ) * f (unitIntervalNeg y) := by
            apply integral_congr_ae
            filter_upwards [complexUnitBandReflection_ae f] with y hy
            rw [hy]
    _ = ∫ y : ClosedInterval (-1 : ℝ) 1,
          (sincKernelSmooth c (x : ℝ) (unitIntervalNeg y : ℝ) : ℂ) * f y := by
            have hchange := measurePreserving_unitIntervalNegMeasurableEquiv.integral_comp'
              (fun y : ClosedInterval (-1 : ℝ) 1 =>
                (sincKernelSmooth c (x : ℝ) (unitIntervalNeg y : ℝ) : ℂ) * f y)
            simpa only [Function.comp_apply, unitIntervalNegMeasurableEquiv_apply,
              unitIntervalNeg_involutive] using hchange
    _ = ∫ y : ClosedInterval (-1 : ℝ) 1,
          (sincKernelSmooth c (unitIntervalNeg x : ℝ) (y : ℝ) : ℂ) * f y := by
            apply integral_congr_ae
            filter_upwards [] with y
            exact congrArg (fun z : ℝ => (z : ℂ) * f y)
              (sincKernelSmooth_neg_left_eq_neg_right c (x : ℝ) (y : ℝ)).symm

def complexUnitBandEvenProjection :
    ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2 :=
  (2 : ℂ)⁻¹ • ((1 : ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2) +
    complexUnitBandReflection)

@[simp] theorem complexUnitBandEvenProjection_apply (f : ComplexUnitIntervalL2) :
    complexUnitBandEvenProjection f = (2 : ℂ)⁻¹ • (f + complexUnitBandReflection f) := rfl

@[simp] theorem complexUnitBandReflection_evenProjection (f : ComplexUnitIntervalL2) :
    complexUnitBandReflection (complexUnitBandEvenProjection f) =
      complexUnitBandEvenProjection f := by
  simp [complexUnitBandEvenProjection_apply, map_add, map_smul, add_comm]

theorem complexUnitBandEvenProjection_idempotent :
    IsIdempotentElem complexUnitBandEvenProjection := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  change complexUnitBandEvenProjection (complexUnitBandEvenProjection f) =
    complexUnitBandEvenProjection f
  rw [complexUnitBandEvenProjection_apply, complexUnitBandReflection_evenProjection]
  module

def complexUnitBandEvenSubspace : Submodule ℂ ComplexUnitIntervalL2 :=
  LinearMap.range complexUnitBandEvenProjection.toLinearMap

instance complexUnitBandEvenSubspace_completeSpace :
    CompleteSpace complexUnitBandEvenSubspace :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    complexUnitBandEvenProjection_idempotent).completeSpace_coe

theorem mem_complexUnitBandEvenSubspace_iff (f : ComplexUnitIntervalL2) :
    f ∈ complexUnitBandEvenSubspace ↔ complexUnitBandReflection f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact complexUnitBandReflection_evenProjection g
  · intro hf
    refine ⟨f, ?_⟩
    change complexUnitBandEvenProjection f = f
    rw [complexUnitBandEvenProjection_apply, hf]
    module

theorem complexBandOperatorL2_mem_even (c : ℝ)
    {f : ComplexUnitIntervalL2} (hf : f ∈ complexUnitBandEvenSubspace) :
    complexBandOperatorL2 c f ∈ complexUnitBandEvenSubspace := by
  rw [mem_complexUnitBandEvenSubspace_iff,
    ← complexBandOperatorL2_complexUnitBandReflection,
    (mem_complexUnitBandEvenSubspace_iff f).mp hf]

theorem norm_complexUnitBandEvenProjection_le (f : ComplexUnitIntervalL2) :
    ‖complexUnitBandEvenProjection f‖ ≤ ‖f‖ := by
  have hadd := norm_add_le f (complexUnitBandReflection f)
  rw [norm_complexUnitBandReflection] at hadd
  calc
    ‖complexUnitBandEvenProjection f‖ = (1 / 2 : ℝ) *
        ‖f + complexUnitBandReflection f‖ := by
      rw [complexUnitBandEvenProjection_apply, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖f‖ + ‖f‖) :=
      mul_le_mul_of_nonneg_left hadd (by norm_num)
    _ = ‖f‖ := by ring

def complexUnitBandEvenProjectionCod :
    ComplexUnitIntervalL2 →L[ℂ] complexUnitBandEvenSubspace :=
  complexUnitBandEvenProjection.codRestrict complexUnitBandEvenSubspace
    (fun f => ⟨f, rfl⟩)

def complexUnitBandEvenCompressionCLM :
    (ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2) →L[ℂ]
      (complexUnitBandEvenSubspace →L[ℂ] complexUnitBandEvenSubspace) := by
  let pre : (ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2) →L[ℂ]
      (complexUnitBandEvenSubspace →L[ℂ] ComplexUnitIntervalL2) :=
    ContinuousLinearMap.flip (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
      (σ₁₃ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ)
      (E := ComplexUnitIntervalL2 →L[ℂ] ComplexUnitIntervalL2)
      (F := complexUnitBandEvenSubspace →L[ℂ] ComplexUnitIntervalL2)
      (G := complexUnitBandEvenSubspace →L[ℂ] ComplexUnitIntervalL2)
      (ContinuousLinearMap.compL ℂ complexUnitBandEvenSubspace
        ComplexUnitIntervalL2 ComplexUnitIntervalL2)
      complexUnitBandEvenSubspace.subtypeL
  let post : (complexUnitBandEvenSubspace →L[ℂ] ComplexUnitIntervalL2) →L[ℂ]
      (complexUnitBandEvenSubspace →L[ℂ] complexUnitBandEvenSubspace) :=
    (ContinuousLinearMap.compL ℂ complexUnitBandEvenSubspace
      ComplexUnitIntervalL2 complexUnitBandEvenSubspace)
      complexUnitBandEvenProjectionCod
  exact post ∘L pre

def complexUnitBandEvenBlock (c : ℝ) :
    complexUnitBandEvenSubspace →L[ℂ] complexUnitBandEvenSubspace :=
  complexUnitBandEvenCompressionCLM (complexBandOperatorL2 c)

@[simp] theorem coe_complexUnitBandEvenBlock_apply
    (c : ℝ) (f : complexUnitBandEvenSubspace) :
    ((complexUnitBandEvenBlock c f : complexUnitBandEvenSubspace) : ComplexUnitIntervalL2) =
      complexBandOperatorL2 c (f : ComplexUnitIntervalL2) := by
  change complexUnitBandEvenProjection
    (complexBandOperatorL2 c (f : ComplexUnitIntervalL2)) = _
  have hfix := (mem_complexUnitBandEvenSubspace_iff _).mp
    (complexBandOperatorL2_mem_even c f.2)
  rw [complexUnitBandEvenProjection_apply, hfix]
  module

theorem isCompactOperator_complexUnitBandEvenBlock (c : ℝ) :
    IsCompactOperator (complexUnitBandEvenBlock c) := by
  let R := (complexBandOperatorL2 c).restrict
    (fun _ hf => complexBandOperatorL2_mem_even c hf)
  have hrestrict : IsCompactOperator R :=
    (isCompactOperator_complexBandOperatorL2 c).restrict'
      (fun _ hf => complexBandOperatorL2_mem_even c hf)
  have heq : (fun f => complexUnitBandEvenBlock c f) = fun f => R f := by
    funext f
    apply Subtype.ext
    exact coe_complexUnitBandEvenBlock_apply c f
  change IsCompactOperator (fun f => complexUnitBandEvenBlock c f)
  rw [heq]
  exact hrestrict

theorem norm_complexUnitBandEvenBlock_sub_le (c d : ℝ) :
    ‖complexUnitBandEvenBlock c - complexUnitBandEvenBlock d‖ ≤
      ‖complexBandOperatorL2 c - complexBandOperatorL2 d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
  intro f
  have hc := coe_complexUnitBandEvenBlock_apply c f
  have hd := coe_complexUnitBandEvenBlock_apply d f
  change ‖((complexUnitBandEvenBlock c - complexUnitBandEvenBlock d) f :
    complexUnitBandEvenSubspace)‖ ≤ _
  rw [sub_apply]
  change ‖((complexUnitBandEvenBlock c f : complexUnitBandEvenSubspace) :
      ComplexUnitIntervalL2) -
    ((complexUnitBandEvenBlock d f : complexUnitBandEvenSubspace) :
      ComplexUnitIntervalL2)‖ ≤ _
  rw [hc, hd]
  change ‖(complexBandOperatorL2 c - complexBandOperatorL2 d)
      (f : ComplexUnitIntervalL2)‖ ≤
    ‖complexBandOperatorL2 c - complexBandOperatorL2 d‖ * ‖f‖
  exact (complexBandOperatorL2 c - complexBandOperatorL2 d).le_opNorm
    (f : ComplexUnitIntervalL2)

theorem continuous_complexUnitBandEvenBlock : Continuous complexUnitBandEvenBlock := by
  exact complexUnitBandEvenCompressionCLM.continuous.comp continuous_complexBandOperatorL2

/-! ## Exact real form and positivity -/

def complexUnitIntervalRealPart :
    ComplexUnitIntervalL2 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  Complex.reCLM.compLpL 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1))

def complexUnitIntervalImagPart :
    ComplexUnitIntervalL2 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  Complex.imCLM.compLpL 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1))

theorem complexUnitIntervalRealPart_coeFn (f : ComplexUnitIntervalL2) :
    (complexUnitIntervalRealPart f : ClosedInterval (-1 : ℝ) 1 → ℝ) =ᵐ[volume]
      fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f

theorem complexUnitIntervalImagPart_coeFn (f : ComplexUnitIntervalL2) :
    (complexUnitIntervalImagPart f : ClosedInterval (-1 : ℝ) 1 → ℝ) =ᵐ[volume]
      fun x => (f x).im :=
  Complex.imCLM.coeFn_compLpL f

theorem complexUnitIntervalL2_real_imag_decomposition (f : ComplexUnitIntervalL2) :
    f = GaloisForLFunctions.HTGeometry.ofRealLp (complexUnitIntervalRealPart f) +
      Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp (complexUnitIntervalImagPart f) := by
  apply Lp.ext
  filter_upwards [complexUnitIntervalRealPart_coeFn f,
    complexUnitIntervalImagPart_coeFn f,
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (complexUnitIntervalRealPart f),
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (complexUnitIntervalImagPart f),
    Lp.coeFn_add
      (GaloisForLFunctions.HTGeometry.ofRealLp (complexUnitIntervalRealPart f))
      (Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp
        (complexUnitIntervalImagPart f)),
    Lp.coeFn_smul Complex.I
      (GaloisForLFunctions.HTGeometry.ofRealLp (complexUnitIntervalImagPart f))]
      with x hre him hofRe hofIm hadd hsmul
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply]
  rw [hofRe, hofIm, hre, him]
  apply Complex.ext <;> simp

theorem complexBandOperatorL2_ofRealLp (c : ℝ)
    (u : RealIntervalL2 (-1 : ℝ) 1) :
    complexBandOperatorL2 c (GaloisForLFunctions.HTGeometry.ofRealLp u) =
      GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c u) := by
  apply Lp.ext
  filter_upwards [complexBandOperatorL2_coeFn c
      (GaloisForLFunctions.HTGeometry.ofRealLp u),
    bandOperatorL2_coeFn c u,
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u,
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (bandOperatorL2 c u)]
      with x hcomplex hreal hu hout
  rw [hcomplex, hout, hreal]
  calc
    (∫ y : ClosedInterval (-1 : ℝ) 1,
        (sincKernelSmooth c (x : ℝ) (y : ℝ) : ℂ) *
          GaloisForLFunctions.HTGeometry.ofRealLp u y) =
        ∫ y : ClosedInterval (-1 : ℝ) 1,
          ((sincKernelSmooth c (x : ℝ) (y : ℝ) * u y : ℝ) : ℂ) := by
            apply integral_congr_ae
            filter_upwards [GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u]
                with y huy
            rw [huy]
            norm_cast
    _ = ((∫ y : ClosedInterval (-1 : ℝ) 1,
          sincKernelSmooth c (x : ℝ) (y : ℝ) * u y : ℝ) : ℂ) :=
      integral_ofReal

theorem complexBandOperatorL2_real_imag_decomposition (c : ℝ)
    (f : ComplexUnitIntervalL2) :
    complexBandOperatorL2 c f =
      GaloisForLFunctions.HTGeometry.ofRealLp
          (bandOperatorL2 c (complexUnitIntervalRealPart f)) +
        Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp
          (bandOperatorL2 c (complexUnitIntervalImagPart f)) := by
  conv_lhs => rw [complexUnitIntervalL2_real_imag_decomposition f]
  rw [map_add, map_smul, complexBandOperatorL2_ofRealLp,
    complexBandOperatorL2_ofRealLp]

theorem inner_ofRealLp_eq_ofReal_inner
    (u v : RealIntervalL2 (-1 : ℝ) 1) :
    inner ℂ (GaloisForLFunctions.HTGeometry.ofRealLp u)
        (GaloisForLFunctions.HTGeometry.ofRealLp v) =
      ((inner ℝ u v : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    (∫ x : ClosedInterval (-1 : ℝ) 1,
        inner ℂ (GaloisForLFunctions.HTGeometry.ofRealLp u x)
          (GaloisForLFunctions.HTGeometry.ofRealLp v x)) =
        ∫ x : ClosedInterval (-1 : ℝ) 1,
          ((inner ℝ (u x) (v x) : ℝ) : ℂ) := by
            apply integral_congr_ae
            filter_upwards [GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u,
              GaloisForLFunctions.HTGeometry.coeFn_ofRealLp v] with x hu hv
            rw [hu, hv]
            simp [RCLike.inner_apply]
    _ = ((∫ x : ClosedInterval (-1 : ℝ) 1,
          inner ℝ (u x) (v x) : ℝ) : ℂ) := integral_ofReal

theorem inner_ofRealLp_add_I_smul
    (u v p q : RealIntervalL2 (-1 : ℝ) 1) :
    inner ℂ
        (GaloisForLFunctions.HTGeometry.ofRealLp u +
          Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp v)
        (GaloisForLFunctions.HTGeometry.ofRealLp p +
          Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp q) =
      (((inner ℝ u p : ℝ) + inner ℝ v q : ℝ) : ℂ) +
        Complex.I * (((inner ℝ u q : ℝ) - inner ℝ v p : ℝ) : ℂ) := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_ofRealLp_eq_ofReal_inner]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem complexBandOperatorL2_symmetric (c : ℝ) :
    (complexBandOperatorL2 c).IsSymmetric := by
  intro f g
  let u := complexUnitIntervalRealPart f
  let v := complexUnitIntervalImagPart f
  let p := complexUnitIntervalRealPart g
  let q := complexUnitIntervalImagPart g
  have hf : f = GaloisForLFunctions.HTGeometry.ofRealLp u +
      Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp v :=
    complexUnitIntervalL2_real_imag_decomposition f
  have hg : g = GaloisForLFunctions.HTGeometry.ofRealLp p +
      Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp q :=
    complexUnitIntervalL2_real_imag_decomposition g
  have hBf : complexBandOperatorL2 c f =
      GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c u) +
        Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c v) :=
    complexBandOperatorL2_real_imag_decomposition c f
  have hBg : complexBandOperatorL2 c g =
      GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c p) +
        Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c q) :=
    complexBandOperatorL2_real_imag_decomposition c g
  calc
    inner ℂ (complexBandOperatorL2 c f) g =
        (((inner ℝ (bandOperatorL2 c u) p : ℝ) +
            inner ℝ (bandOperatorL2 c v) q : ℝ) : ℂ) +
          Complex.I * (((inner ℝ (bandOperatorL2 c u) q : ℝ) -
            inner ℝ (bandOperatorL2 c v) p : ℝ) : ℂ) := by
              rw [hBf, hg, inner_ofRealLp_add_I_smul]
    _ = (((inner ℝ u (bandOperatorL2 c p) : ℝ) +
            inner ℝ v (bandOperatorL2 c q) : ℝ) : ℂ) +
          Complex.I * (((inner ℝ u (bandOperatorL2 c q) : ℝ) -
            inner ℝ v (bandOperatorL2 c p) : ℝ) : ℂ) := by
              rw [bandOperatorL2_symmetric c u p,
                bandOperatorL2_symmetric c v q,
                bandOperatorL2_symmetric c u q,
                bandOperatorL2_symmetric c v p]
    _ = inner ℂ f (complexBandOperatorL2 c g) := by
              rw [hf, hBg, inner_ofRealLp_add_I_smul]

theorem complexBandOperatorL2_reApplyInnerSelf
    (c : ℝ) (f : ComplexUnitIntervalL2) :
    (complexBandOperatorL2 c).reApplyInnerSelf f =
      (inner ℝ (bandOperatorL2 c (complexUnitIntervalRealPart f))
          (complexUnitIntervalRealPart f) : ℝ) +
        (inner ℝ (bandOperatorL2 c (complexUnitIntervalImagPart f))
          (complexUnitIntervalImagPart f) : ℝ) := by
  let u := complexUnitIntervalRealPart f
  let v := complexUnitIntervalImagPart f
  have hf : f = GaloisForLFunctions.HTGeometry.ofRealLp u +
      Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp v :=
    complexUnitIntervalL2_real_imag_decomposition f
  have hBf : complexBandOperatorL2 c f =
      GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c u) +
        Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c v) :=
    complexBandOperatorL2_real_imag_decomposition c f
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change (inner ℂ (complexBandOperatorL2 c f) f).re =
    (inner ℝ (bandOperatorL2 c u) u : ℝ) +
      (inner ℝ (bandOperatorL2 c v) v : ℝ)
  calc
    (inner ℂ (complexBandOperatorL2 c f) f).re =
        (inner ℂ
          (GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c u) +
            Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp (bandOperatorL2 c v))
          (GaloisForLFunctions.HTGeometry.ofRealLp u +
            Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp v)).re := by
              rw [hBf, hf]
    _ = (inner ℝ (bandOperatorL2 c u) u : ℝ) +
          (inner ℝ (bandOperatorL2 c v) v : ℝ) := by
            rw [inner_ofRealLp_add_I_smul]
            simp

theorem complexBandOperatorL2_isPositive {c : ℝ} (hc : 0 < c) :
    (complexBandOperatorL2 c).IsPositive := by
  refine ⟨complexBandOperatorL2_symmetric c, fun f => ?_⟩
  rw [complexBandOperatorL2_reApplyInnerSelf]
  exact add_nonneg
    (inner_bandOperatorL2_nonneg hc (complexUnitIntervalRealPart f))
    (inner_bandOperatorL2_nonneg hc (complexUnitIntervalImagPart f))

theorem complexUnitBandEvenBlock_isPositive {c : ℝ} (hc : 0 < c) :
    (complexUnitBandEvenBlock c).IsPositive := by
  refine ⟨?_, fun f => ?_⟩
  · intro f g
    change inner ℂ
        (((complexUnitBandEvenBlock c f : complexUnitBandEvenSubspace) :
          ComplexUnitIntervalL2)) (g : ComplexUnitIntervalL2) =
      inner ℂ (f : ComplexUnitIntervalL2)
        (((complexUnitBandEvenBlock c g : complexUnitBandEvenSubspace) :
          ComplexUnitIntervalL2))
    rw [coe_complexUnitBandEvenBlock_apply, coe_complexUnitBandEvenBlock_apply]
    exact complexBandOperatorL2_symmetric c f g
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change 0 ≤ (inner ℂ
      (((complexUnitBandEvenBlock c f : complexUnitBandEvenSubspace) :
        ComplexUnitIntervalL2)) (f : ComplexUnitIntervalL2)).re
    rw [coe_complexUnitBandEvenBlock_apply]
    exact (complexBandOperatorL2_isPositive hc).2 (f : ComplexUnitIntervalL2)

/-! ## Indexed compact spectrum -/

/-- Ordered approximation-number spectrum of the fixed-unit complex even Slepian block. -/
noncomputable def complexUnitBandEvenValue (c : ℝ) (n : ℕ) : ℝ :=
  approxNumber (complexUnitBandEvenBlock c) n

theorem continuous_complexUnitBandEvenValue (n : ℕ) :
    Continuous fun c => complexUnitBandEvenValue c n := by
  change Continuous ((fun T : complexUnitBandEvenSubspace →L[ℂ]
    complexUnitBandEvenSubspace => approxNumber T n) ∘ complexUnitBandEvenBlock)
  exact (approxNumber_lipschitz (H := complexUnitBandEvenSubspace) n).continuous.comp
    continuous_complexUnitBandEvenBlock

theorem complexUnitBandEvenValue_eq_sgVal
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    complexUnitBandEvenValue c n =
      ContinuousLinearMap.sgVal (complexUnitBandEvenBlock c) n := by
  rw [complexUnitBandEvenValue,
    approxNumber_eq_singVal
      (isCompactOperator_complexUnitBandEvenBlock c),
    ← abs_sgVal_eq_singVal
      (isCompactOperator_complexUnitBandEvenBlock c)
      (complexUnitBandEvenBlock_isPositive hc).isSymmetric,
    abs_of_nonneg (sgVal_nonneg_of_isPositive
      (complexUnitBandEvenBlock_isPositive hc) n)]

theorem complexUnitIntervalRealPart_ofRealLp
    (u : RealIntervalL2 (-1 : ℝ) 1) :
    complexUnitIntervalRealPart (GaloisForLFunctions.HTGeometry.ofRealLp u) = u := by
  apply Lp.ext
  filter_upwards [complexUnitIntervalRealPart_coeFn
      (GaloisForLFunctions.HTGeometry.ofRealLp u),
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u] with x hre hu
  rw [hre, hu]
  simp

theorem complexUnitIntervalImagPart_ofRealLp
    (u : RealIntervalL2 (-1 : ℝ) 1) :
    complexUnitIntervalImagPart (GaloisForLFunctions.HTGeometry.ofRealLp u) = 0 := by
  apply Lp.ext
  filter_upwards [complexUnitIntervalImagPart_coeFn
      (GaloisForLFunctions.HTGeometry.ofRealLp u),
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u,
    Lp.coeFn_zero ℝ 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1))]
      with x him hu hzero
  rw [him, hu, hzero]
  simp

theorem complexUnitIntervalRealPart_I_smul_ofRealLp
    (u : RealIntervalL2 (-1 : ℝ) 1) :
    complexUnitIntervalRealPart
      (Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp u) = 0 := by
  apply Lp.ext
  filter_upwards [complexUnitIntervalRealPart_coeFn
      (Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp u),
    Lp.coeFn_smul Complex.I (GaloisForLFunctions.HTGeometry.ofRealLp u),
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u,
    Lp.coeFn_zero ℝ 2 (volume : Measure (ClosedInterval (-1 : ℝ) 1))]
      with x hre hsmul hu hzero
  rw [hre, hsmul, Pi.smul_apply, hu, hzero]
  simp

theorem complexUnitIntervalImagPart_I_smul_ofRealLp
    (u : RealIntervalL2 (-1 : ℝ) 1) :
    complexUnitIntervalImagPart
      (Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp u) = u := by
  apply Lp.ext
  filter_upwards [complexUnitIntervalImagPart_coeFn
      (Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp u),
    Lp.coeFn_smul Complex.I (GaloisForLFunctions.HTGeometry.ofRealLp u),
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u] with x him hsmul hu
  rw [him, hsmul, Pi.smul_apply, hu]
  simp

theorem complexUnitIntervalRealPart_complexBandOperatorL2
    (c : ℝ) (f : ComplexUnitIntervalL2) :
    complexUnitIntervalRealPart (complexBandOperatorL2 c f) =
      bandOperatorL2 c (complexUnitIntervalRealPart f) := by
  rw [complexBandOperatorL2_real_imag_decomposition, map_add,
    complexUnitIntervalRealPart_ofRealLp,
    complexUnitIntervalRealPart_I_smul_ofRealLp, add_zero]

theorem complexUnitIntervalImagPart_complexBandOperatorL2
    (c : ℝ) (f : ComplexUnitIntervalL2) :
    complexUnitIntervalImagPart (complexBandOperatorL2 c f) =
      bandOperatorL2 c (complexUnitIntervalImagPart f) := by
  rw [complexBandOperatorL2_real_imag_decomposition, map_add,
    complexUnitIntervalImagPart_ofRealLp,
    complexUnitIntervalImagPart_I_smul_ofRealLp, zero_add]

theorem complexUnitIntervalRealPart_ofReal_smul
    (r : ℝ) (f : ComplexUnitIntervalL2) :
    complexUnitIntervalRealPart ((r : ℂ) • f) =
      r • complexUnitIntervalRealPart f := by
  apply Lp.ext
  filter_upwards [complexUnitIntervalRealPart_coeFn ((r : ℂ) • f),
    Lp.coeFn_smul (r : ℂ) f, complexUnitIntervalRealPart_coeFn f,
    Lp.coeFn_smul r (complexUnitIntervalRealPart f)] with x hre hsmul hrf hrsmul
  rw [hre, hsmul]
  simp only [Pi.smul_apply]
  rw [hrsmul]
  simp only [Pi.smul_apply]
  rw [hrf]
  simp

theorem complexUnitIntervalImagPart_ofReal_smul
    (r : ℝ) (f : ComplexUnitIntervalL2) :
    complexUnitIntervalImagPart ((r : ℂ) • f) =
      r • complexUnitIntervalImagPart f := by
  apply Lp.ext
  filter_upwards [complexUnitIntervalImagPart_coeFn ((r : ℂ) • f),
    Lp.coeFn_smul (r : ℂ) f, complexUnitIntervalImagPart_coeFn f,
    Lp.coeFn_smul r (complexUnitIntervalImagPart f)] with x him hsmul hif hismul
  rw [him, hsmul]
  simp only [Pi.smul_apply]
  rw [hismul]
  simp only [Pi.smul_apply]
  rw [hif]
  simp

theorem realPart_bandEigen_of_complexBandEigen
    {c lam : ℝ} {f : ComplexUnitIntervalL2}
    (hf : complexBandOperatorL2 c f = (lam : ℂ) • f) :
    bandOperatorL2 c (complexUnitIntervalRealPart f) =
      lam • complexUnitIntervalRealPart f := by
  have h := congrArg complexUnitIntervalRealPart hf
  rwa [complexUnitIntervalRealPart_complexBandOperatorL2,
    complexUnitIntervalRealPart_ofReal_smul] at h

theorem imagPart_bandEigen_of_complexBandEigen
    {c lam : ℝ} {f : ComplexUnitIntervalL2}
    (hf : complexBandOperatorL2 c f = (lam : ℂ) • f) :
    bandOperatorL2 c (complexUnitIntervalImagPart f) =
      lam • complexUnitIntervalImagPart f := by
  have h := congrArg complexUnitIntervalImagPart hf
  rwa [complexUnitIntervalImagPart_complexBandOperatorL2,
    complexUnitIntervalImagPart_ofReal_smul] at h

theorem ofRealLp_real_smul
    (r : ℝ) (u : RealIntervalL2 (-1 : ℝ) 1) :
    GaloisForLFunctions.HTGeometry.ofRealLp (r • u) =
      (r : ℂ) • GaloisForLFunctions.HTGeometry.ofRealLp u := by
  apply Lp.ext
  filter_upwards [GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (r • u),
    Lp.coeFn_smul r u,
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u,
    Lp.coeFn_smul (r : ℂ) (GaloisForLFunctions.HTGeometry.ofRealLp u)]
      with x hleft hrs hu hright
  rw [hleft, hrs, Pi.smul_apply, hright, Pi.smul_apply, hu]
  simp

@[simp] theorem ofRealLp_zero_unitInterval :
    GaloisForLFunctions.HTGeometry.ofRealLp
      (0 : RealIntervalL2 (-1 : ℝ) 1) = 0 :=
  map_zero (Complex.ofRealCLM.compLpL 2
    (volume : Measure (ClosedInterval (-1 : ℝ) 1)))

/-- Nonzero eigenspaces of the complexified Slepian operator remain one complex line. -/
theorem complexBandOperatorL2_eigenvectors_proportional
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {f g : ComplexUnitIntervalL2} (hfne : f ≠ 0)
    (hfEig : complexBandOperatorL2 c f = (lam : ℂ) • f)
    (hgEig : complexBandOperatorL2 c g = (lam : ℂ) • g) :
    ∃ z : ℂ, g = z • f := by
  let u := complexUnitIntervalRealPart f
  let v := complexUnitIntervalImagPart f
  let p := complexUnitIntervalRealPart g
  let q := complexUnitIntervalImagPart g
  have huEig : bandOperatorL2 c u = lam • u :=
    realPart_bandEigen_of_complexBandEigen hfEig
  have hvEig : bandOperatorL2 c v = lam • v :=
    imagPart_bandEigen_of_complexBandEigen hfEig
  have hpEig : bandOperatorL2 c p = lam • p :=
    realPart_bandEigen_of_complexBandEigen hgEig
  have hqEig : bandOperatorL2 c q = lam • q :=
    imagPart_bandEigen_of_complexBandEigen hgEig
  have hfdec : f = GaloisForLFunctions.HTGeometry.ofRealLp u +
      Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp v :=
    complexUnitIntervalL2_real_imag_decomposition f
  have hgdec : g = GaloisForLFunctions.HTGeometry.ofRealLp p +
      Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp q :=
    complexUnitIntervalL2_real_imag_decomposition g
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro hv
      apply hfne
      rw [hfdec, hu, hv]
      rw [ofRealLp_zero_unitInterval]
      module
    obtain ⟨s, hps⟩ := bandOperatorL2_eigenvectors_proportional
      hc hlam hvEig hv hpEig
    obtain ⟨t, hqt⟩ := bandOperatorL2_eigenvectors_proportional
      hc hlam hvEig hv hqEig
    let beta : ℂ := (s : ℂ) + Complex.I * (t : ℂ)
    have hgs : g = beta • GaloisForLFunctions.HTGeometry.ofRealLp v := by
      rw [hgdec, hps, hqt, ofRealLp_real_smul, ofRealLp_real_smul]
      simp only [beta]
      module
    have hfs : f = Complex.I • GaloisForLFunctions.HTGeometry.ofRealLp v := by
      rw [hfdec, hu]
      rw [ofRealLp_zero_unitInterval]
      module
    refine ⟨beta * Complex.I⁻¹, ?_⟩
    rw [hgs, hfs, smul_smul]
    congr 1
    field_simp
  · obtain ⟨s, hvs⟩ := bandOperatorL2_eigenvectors_proportional
      hc hlam huEig hu hvEig
    obtain ⟨t, hpt⟩ := bandOperatorL2_eigenvectors_proportional
      hc hlam huEig hu hpEig
    obtain ⟨w, hqw⟩ := bandOperatorL2_eigenvectors_proportional
      hc hlam huEig hu hqEig
    let alpha : ℂ := 1 + Complex.I * (s : ℂ)
    let beta : ℂ := (t : ℂ) + Complex.I * (w : ℂ)
    have halpha : alpha ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp [alpha] at hre
    have hfs : f = alpha • GaloisForLFunctions.HTGeometry.ofRealLp u := by
      rw [hfdec, hvs, ofRealLp_real_smul]
      simp only [alpha]
      module
    have hgs : g = beta • GaloisForLFunctions.HTGeometry.ofRealLp u := by
      rw [hgdec, hpt, hqw, ofRealLp_real_smul, ofRealLp_real_smul]
      simp only [beta]
      module
    refine ⟨beta * alpha⁻¹, ?_⟩
    rw [hgs, hfs, smul_smul]
    congr 1
    field_simp

theorem complexUnitBandReflection_ofRealLp
    (u : RealIntervalL2 (-1 : ℝ) 1) :
    complexUnitBandReflection (GaloisForLFunctions.HTGeometry.ofRealLp u) =
      GaloisForLFunctions.HTGeometry.ofRealLp (unitBandReflection u) := by
  apply Lp.ext
  have hofComp := (GaloisForLFunctions.HTGeometry.coeFn_ofRealLp u).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [complexUnitBandReflection_ae
      (GaloisForLFunctions.HTGeometry.ofRealLp u),
    unitBandReflection_ae u, hofComp,
    GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (unitBandReflection u)]
      with x hleft href hsource hright
  rw [hleft, hright, href]
  simpa only [Function.comp_apply] using hsource

theorem ofRealLp_mem_complexUnitBandEvenSubspace
    {u : RealIntervalL2 (-1 : ℝ) 1} (hu : u ∈ unitBandEvenSubspace) :
    GaloisForLFunctions.HTGeometry.ofRealLp u ∈ complexUnitBandEvenSubspace := by
  rw [mem_complexUnitBandEvenSubspace_iff, complexUnitBandReflection_ofRealLp,
    (mem_unitBandEvenSubspace_iff u).mp hu]

def complexifyUnitBandEven
    (u : unitBandEvenSubspace) : complexUnitBandEvenSubspace :=
  ⟨GaloisForLFunctions.HTGeometry.ofRealLp (u : RealIntervalL2 (-1 : ℝ) 1),
    ofRealLp_mem_complexUnitBandEvenSubspace u.2⟩

theorem complexifyUnitBandEven_ne_zero
    {u : unitBandEvenSubspace} (hu : u ≠ 0) :
    complexifyUnitBandEven u ≠ 0 := by
  intro hzero
  apply hu
  apply Subtype.ext
  have hcoe := congrArg (fun z : complexUnitBandEvenSubspace =>
    (z : ComplexUnitIntervalL2)) hzero
  have hnorm := GaloisForLFunctions.HTGeometry.norm_ofRealLp
    (u : RealIntervalL2 (-1 : ℝ) 1)
  have : ‖(u : RealIntervalL2 (-1 : ℝ) 1)‖ = 0 := by
    rw [← hnorm, show GaloisForLFunctions.HTGeometry.ofRealLp
      (u : RealIntervalL2 (-1 : ℝ) 1) = 0 by exact hcoe, norm_zero]
  exact norm_eq_zero.mp this

theorem complexUnitBandEvenBlock_complexifyUnitBandEven
  (c : ℝ) (u : unitBandEvenSubspace) :
    complexUnitBandEvenBlock c (complexifyUnitBandEven u) =
      complexifyUnitBandEven (unitBandEvenBlock c u) := by
  apply Subtype.ext
  rw [coe_complexUnitBandEvenBlock_apply]
  change complexBandOperatorL2 c
      (GaloisForLFunctions.HTGeometry.ofRealLp
        (u : RealIntervalL2 (-1 : ℝ) 1)) =
    GaloisForLFunctions.HTGeometry.ofRealLp
      (((unitBandEvenBlock c u : unitBandEvenSubspace) :
        RealIntervalL2 (-1 : ℝ) 1))
  rw [coe_unitBandEvenBlock_apply]
  exact complexBandOperatorL2_ofRealLp c u

theorem exists_complexUnitBandEvenValue_eq_signedValue_sq
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ k : ℕ, complexUnitBandEvenValue (2 * Real.pi * a ^ 2) k =
      evenProlateSignedValue a n ^ 2 := by
  let nu : ℝ := evenProlateSignedValue a n
  let lam : ℝ := nu ^ 2
  have hnu : nu ≠ 0 := evenProlateSignedValue_ne_zero ha n
  have hlam : lam ≠ 0 := pow_ne_zero 2 hnu
  obtain ⟨psi, hpsiNe, hpsiEig, hpsiExtEven⟩ :=
    exists_realIntervalL2_bandEigen_of_signedMode ha n hnu
  have hpsiEven : psi ∈ unitBandEvenSubspace := by
    rw [← bandClass_eigenExtension hlam hpsiEig]
    exact bandClass_mem_unitBandEvenSubspace_of_even
      (continuous_eigenExtension _ _ _) hpsiExtEven
  let u : unitBandEvenSubspace := ⟨psi, hpsiEven⟩
  have huNe : u ≠ 0 := by
    intro hzero
    apply hpsiNe
    exact congrArg Subtype.val hzero
  let z : complexUnitBandEvenSubspace := complexifyUnitBandEven u
  have hzNe : z ≠ 0 := complexifyUnitBandEven_ne_zero huNe
  have hzEig : complexUnitBandEvenBlock (2 * Real.pi * a ^ 2) z =
      (lam : ℂ) • z := by
    rw [show z = complexifyUnitBandEven u from rfl,
      complexUnitBandEvenBlock_complexifyUnitBandEven]
    apply Subtype.ext
    change GaloisForLFunctions.HTGeometry.ofRealLp
        (bandOperatorL2 (2 * Real.pi * a ^ 2) psi) =
      (lam : ℂ) • GaloisForLFunctions.HTGeometry.ofRealLp psi
    rw [hpsiEig, ofRealLp_real_smul]
  obtain ⟨k, hk⟩ := ContinuousLinearMap.exists_sgVal_eq_of_eigenvalue
    (isCompactOperator_complexUnitBandEvenBlock (2 * Real.pi * a ^ 2))
    (complexUnitBandEvenBlock_isPositive (by positivity :
      0 < 2 * Real.pi * a ^ 2)).isSymmetric hzNe hzEig
    (Complex.ofReal_ne_zero.mpr hlam)
  refine ⟨k, ?_⟩
  rw [complexUnitBandEvenValue_eq_sgVal (by positivity :
    0 < 2 * Real.pi * a ^ 2)]
  exact Complex.ofReal_injective hk

theorem unitBandReflection_complexUnitIntervalRealPart
    (f : ComplexUnitIntervalL2) :
    unitBandReflection (complexUnitIntervalRealPart f) =
      complexUnitIntervalRealPart (complexUnitBandReflection f) := by
  apply Lp.ext
  have hreComp := (complexUnitIntervalRealPart_coeFn f).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [unitBandReflection_ae (complexUnitIntervalRealPart f),
    hreComp, complexUnitBandReflection_ae f,
    complexUnitIntervalRealPart_coeFn (complexUnitBandReflection f)]
      with x hleft hre href hright
  rw [hleft, hright, href]
  simpa only [Function.comp_apply] using hre

theorem unitBandReflection_complexUnitIntervalImagPart
    (f : ComplexUnitIntervalL2) :
    unitBandReflection (complexUnitIntervalImagPart f) =
      complexUnitIntervalImagPart (complexUnitBandReflection f) := by
  apply Lp.ext
  have himComp := (complexUnitIntervalImagPart_coeFn f).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [unitBandReflection_ae (complexUnitIntervalImagPart f),
    himComp, complexUnitBandReflection_ae f,
    complexUnitIntervalImagPart_coeFn (complexUnitBandReflection f)]
      with x hleft him href hright
  rw [hleft, hright, href]
  simpa only [Function.comp_apply] using him

theorem complexUnitIntervalRealPart_mem_unitBandEvenSubspace
    {f : ComplexUnitIntervalL2} (hf : f ∈ complexUnitBandEvenSubspace) :
    complexUnitIntervalRealPart f ∈ unitBandEvenSubspace := by
  rw [mem_unitBandEvenSubspace_iff,
    unitBandReflection_complexUnitIntervalRealPart,
    (mem_complexUnitBandEvenSubspace_iff f).mp hf]

theorem complexUnitIntervalImagPart_mem_unitBandEvenSubspace
    {f : ComplexUnitIntervalL2} (hf : f ∈ complexUnitBandEvenSubspace) :
    complexUnitIntervalImagPart f ∈ unitBandEvenSubspace := by
  rw [mem_unitBandEvenSubspace_iff,
    unitBandReflection_complexUnitIntervalImagPart,
    (mem_complexUnitBandEvenSubspace_iff f).mp hf]

/-- Every nonzero eigenvalue of the fixed-unit complex even Slepian block comes from an actual
physical signed finite-Fourier mode, with the exact square normalization. -/
theorem exists_evenProlateSignedValue_sq_eq_of_complexUnitBandEvenBlock_eigen
    {a lam : ℝ} (ha : 0 < a) (hlam : lam ≠ 0)
    {z : complexUnitBandEvenSubspace} (hzNe : z ≠ 0)
    (hzEig : complexUnitBandEvenBlock (2 * Real.pi * a ^ 2) z =
      (lam : ℂ) • z) :
    ∃ n : ℕ, evenProlateSignedValue a n ^ 2 = lam := by
  let f : ComplexUnitIntervalL2 := (z : ComplexUnitIntervalL2)
  have hfNe : f ≠ 0 := by
    intro hzero
    apply hzNe
    exact Subtype.ext hzero
  have hfEig : complexBandOperatorL2 (2 * Real.pi * a ^ 2) f =
      (lam : ℂ) • f := by
    dsimp only [f]
    have h := congrArg (fun w : complexUnitBandEvenSubspace =>
      (w : ComplexUnitIntervalL2)) hzEig
    rw [coe_complexUnitBandEvenBlock_apply] at h
    change complexBandOperatorL2 (2 * Real.pi * a ^ 2)
        (z : ComplexUnitIntervalL2) =
      (lam : ℂ) • (z : ComplexUnitIntervalL2) at h
    exact h
  obtain ⟨u, huNe, huEig, huEven⟩ :
      ∃ u : RealIntervalL2 (-1 : ℝ) 1,
        u ≠ 0 ∧
          bandOperatorL2 (2 * Real.pi * a ^ 2) u = lam • u ∧
          u ∈ unitBandEvenSubspace := by
    let u := complexUnitIntervalRealPart f
    let v := complexUnitIntervalImagPart f
    have huEig : bandOperatorL2 (2 * Real.pi * a ^ 2) u = lam • u :=
      realPart_bandEigen_of_complexBandEigen hfEig
    have hvEig : bandOperatorL2 (2 * Real.pi * a ^ 2) v = lam • v :=
      imagPart_bandEigen_of_complexBandEigen hfEig
    have huEven : u ∈ unitBandEvenSubspace :=
      complexUnitIntervalRealPart_mem_unitBandEvenSubspace z.2
    have hvEven : v ∈ unitBandEvenSubspace :=
      complexUnitIntervalImagPart_mem_unitBandEvenSubspace z.2
    by_cases huNe : u ≠ 0
    · exact ⟨u, huNe, huEig, huEven⟩
    · have hvNe : v ≠ 0 := by
        intro hvzero
        apply hfNe
        rw [complexUnitIntervalL2_real_imag_decomposition f,
          show complexUnitIntervalRealPart f = 0 from not_ne_iff.mp huNe,
          show complexUnitIntervalImagPart f = 0 from hvzero,
          ofRealLp_zero_unitInterval]
        module
      exact ⟨v, hvNe, hvEig, hvEven⟩
  have hc : 0 < 2 * Real.pi * a ^ 2 := by positivity
  have hExtEven : Function.Even
      (eigenExtension (2 * Real.pi * a ^ 2) lam u) :=
    eigenExtension_even_of_mem_unitBandEvenSubspace _ _ huEven
  obtain ⟨Phi, eta, hPhiSmooth, hPhiNe, hPhiEven, hPhiBand, hPhiProlate⟩ :=
    exists_joint_even_prolate_band_eigen hc hlam huEig huNe hExtEven
  obtain ⟨mu, hmuNe, hmuSq, hmuEig⟩ :=
    exists_realFourierBandTransform_eigen (Φ := Phi) (eta := eta)
      (lam := lam) (κ := a ^ 2) (by positivity)
      hPhiSmooth hPhiNe hPhiEven hlam hPhiBand hPhiProlate
  let trial : evenSubspace :=
    continuousEvenPhysicalTrial a ha Phi hPhiSmooth.continuous hPhiEven
  have hPhi0 : Phi 0 ≠ 0 :=
    value_zero_ne_of_even_joint_prolate_band_eigen
      hPhiSmooth hPhiNe hPhiEven hlam hPhiBand hPhiProlate
  have htrialNe : trial ≠ 0 :=
    continuousEvenPhysicalTrial_ne_zero_of_value_zero_ne
      ha hPhiSmooth.continuous hPhiEven hPhi0
  have htrialEig : evenTimeBandFourier a trial =
      (((a * mu : ℝ) : ℂ)) • trial :=
    evenTimeBandFourier_continuousEvenPhysicalTrial_eigen
      ha hPhiSmooth.continuous hPhiEven hmuEig
  have haMuNe : ((a * mu : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero ha.ne' hmuNe)
  obtain ⟨n, hn⟩ := ContinuousLinearMap.exists_sgVal_eq_of_eigenvalue
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a)) htrialNe htrialEig haMuNe
  refine ⟨n, ?_⟩
  have hnReal : evenProlateSignedValue a n = a * mu := by
    exact Complex.ofReal_injective hn
  rw [hnReal]
  calc
    (a * mu) ^ 2 = a ^ 2 * mu ^ 2 := by ring
    _ = lam := hmuSq

theorem complexUnitBandEvenValue_pos
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < complexUnitBandEvenValue (2 * Real.pi * a ^ 2) n := by
  let S := complexUnitBandEvenBlock (2 * Real.pi * a ^ 2)
  let g := complexUnitBandEvenValue (2 * Real.pi * a ^ 2)
  have hnonneg : 0 ≤ g n := approxNumber_nonneg S n
  by_contra hnpos
  have hzero : g n = 0 := le_antisymm (not_lt.mp hnpos) hnonneg
  have hex : ∀ j : Fin (n + 1), ∃ k : ℕ,
      g k = evenProlateSignedValue a j ^ 2 := by
    intro j
    exact exists_complexUnitBandEvenValue_eq_signedValue_sq ha j
  choose k hk using hex
  have hklt : ∀ j : Fin (n + 1), k j < n := by
    intro j
    by_contra hnot
    have hle : g (k j) ≤ g n :=
      (approxNumber_antitone S) (Nat.le_of_not_gt hnot)
    have hpos : 0 < evenProlateSignedValue a j ^ 2 :=
      sq_pos_of_ne_zero (evenProlateSignedValue_ne_zero ha j)
    rw [hk j, hzero] at hle
    linarith
  let phi : Fin (n + 1) → Fin n := fun j => ⟨k j, hklt j⟩
  have hphi : Function.Injective phi := by
    intro i j hij
    apply Fin.ext
    apply evenProlateSignedValue_sq_injective ha
    change evenProlateSignedValue a (i : ℕ) ^ 2 =
      evenProlateSignedValue a (j : ℕ) ^ 2
    rw [← hk i, ← hk j]
    exact congrArg g (congrArg Fin.val hij)
  have hcard := Fintype.card_le_of_injective phi hphi
  simp only [Fintype.card_fin] at hcard
  omega

theorem complexUnitBandEvenValue_injective
    {a : ℝ} (ha : 0 < a) :
    Function.Injective (complexUnitBandEvenValue (2 * Real.pi * a ^ 2)) := by
  let c : ℝ := 2 * Real.pi * a ^ 2
  let S := complexUnitBandEvenBlock c
  let g := complexUnitBandEvenValue c
  have hc : 0 < c := by dsimp only [c]; positivity
  intro m n hmnVal
  by_contra hmn
  have hgmPos : 0 < g m := complexUnitBandEvenValue_pos ha m
  have hgmNe : g m ≠ 0 := ne_of_gt hgmPos
  let em : complexUnitBandEvenSubspace := ContinuousLinearMap.sgVec S m
  let en : complexUnitBandEvenSubspace := ContinuousLinearMap.sgVec S n
  have hemNe : em ≠ 0 := by
    intro hzero
    have hdead := ContinuousLinearMap.sgVal_zero_of_dead
      (S := S) (n := m) hzero
    have hEq := complexUnitBandEvenValue_eq_sgVal hc m
    exact hgmNe (hEq.trans hdead)
  have henNe : en ≠ 0 := by
    intro hzero
    have hdead := ContinuousLinearMap.sgVal_zero_of_dead
      (S := S) (n := n) hzero
    have hEq := complexUnitBandEvenValue_eq_sgVal hc n
    exact hgmNe (hmnVal.trans (hEq.trans hdead))
  have hemEigBlock : S em = ((g m : ℝ) : ℂ) • em := by
    have h := ContinuousLinearMap.apply_sgVec S m
    rw [← complexUnitBandEvenValue_eq_sgVal hc m] at h
    exact h
  have henEigBlock : S en = ((g m : ℝ) : ℂ) • en := by
    have h := ContinuousLinearMap.apply_sgVec S n
    rw [← complexUnitBandEvenValue_eq_sgVal hc n, ← hmnVal] at h
    exact h
  have hemEig : complexBandOperatorL2 c
      (em : ComplexUnitIntervalL2) =
      ((g m : ℝ) : ℂ) • (em : ComplexUnitIntervalL2) := by
    have h := congrArg (fun w : complexUnitBandEvenSubspace =>
      (w : ComplexUnitIntervalL2)) hemEigBlock
    rw [coe_complexUnitBandEvenBlock_apply] at h
    exact h
  have henEig : complexBandOperatorL2 c
      (en : ComplexUnitIntervalL2) =
      ((g m : ℝ) : ℂ) • (en : ComplexUnitIntervalL2) := by
    have h := congrArg (fun w : complexUnitBandEvenSubspace =>
      (w : ComplexUnitIntervalL2)) henEigBlock
    rw [coe_complexUnitBandEvenBlock_apply] at h
    exact h
  obtain ⟨z, hprop⟩ := complexBandOperatorL2_eigenvectors_proportional
    hc hgmNe (show (em : ComplexUnitIntervalL2) ≠ 0 by
      intro hzero; exact hemNe (Subtype.ext hzero)) hemEig henEig
  have hpropSub : en = z • em := by
    apply Subtype.ext
    exact hprop
  have horth := ContinuousLinearMap.inner_sgVec_sgVec_of_ne S hmn
  change inner ℂ em en = 0 at horth
  rw [hpropSub] at horth
  rw [inner_smul_right em em z, inner_self_eq_norm_sq_to_K] at horth
  have hz : z = 0 := by
    rcases mul_eq_zero.mp horth with hz | hnorm
    · exact hz
    · have hnormC : ((‖em‖ : ℝ) : ℂ) = 0 :=
        (pow_eq_zero_iff (n := 2) (by norm_num)).mp hnorm
      have hnormReal : ‖em‖ = 0 := Complex.ofReal_injective hnormC
      exact False.elim (hemNe (norm_eq_zero.mp hnormReal))
  apply henNe
  rw [hpropSub, hz, zero_smul]

theorem complexUnitBandEvenValue_strictAnti
    {a : ℝ} (ha : 0 < a) :
    StrictAnti (complexUnitBandEvenValue (2 * Real.pi * a ^ 2)) := by
  exact (approxNumber_antitone
    (complexUnitBandEvenBlock (2 * Real.pi * a ^ 2))).strictAnti_of_injective
      (complexUnitBandEvenValue_injective ha)

theorem exists_signedValue_sq_eq_complexUnitBandEvenValue
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ n : ℕ, evenProlateSignedValue a n ^ 2 =
      complexUnitBandEvenValue (2 * Real.pi * a ^ 2) k := by
  let c : ℝ := 2 * Real.pi * a ^ 2
  let S := complexUnitBandEvenBlock c
  let z : complexUnitBandEvenSubspace := ContinuousLinearMap.sgVec S k
  have hc : 0 < c := by dsimp only [c]; positivity
  have hvalPos : 0 < complexUnitBandEvenValue c k :=
    complexUnitBandEvenValue_pos ha k
  have hvalNe : complexUnitBandEvenValue c k ≠ 0 := ne_of_gt hvalPos
  have hzNe : z ≠ 0 := by
    intro hzero
    have hdead := ContinuousLinearMap.sgVal_zero_of_dead
      (S := S) (n := k) hzero
    exact hvalNe ((complexUnitBandEvenValue_eq_sgVal hc k).trans hdead)
  have hzEig : S z =
      ((complexUnitBandEvenValue c k : ℝ) : ℂ) • z := by
    have h := ContinuousLinearMap.apply_sgVec S k
    rw [← complexUnitBandEvenValue_eq_sgVal hc k] at h
    exact h
  exact exists_evenProlateSignedValue_sq_eq_of_complexUnitBandEvenBlock_eigen
    ha hvalNe hzNe hzEig

/-- Exact indexed spectral identification: fixed-unit Slepian approximation numbers are the
squares of the actual signed physical Fourier modes, with no branch permutation. -/
theorem complexUnitBandEvenValue_eq_evenProlateSignedValue_sq
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    complexUnitBandEvenValue (2 * Real.pi * a ^ 2) n =
      evenProlateSignedValue a n ^ 2 := by
  let f : ℕ → ℝ := fun n => evenProlateSignedValue a n ^ 2
  let g : ℕ → ℝ := complexUnitBandEvenValue (2 * Real.pi * a ^ 2)
  have hf : StrictAnti f := evenProlateSignedValue_sq_strictAnti ha
  have hg : StrictAnti g := complexUnitBandEvenValue_strictAnti ha
  have hrange : Set.range f = Set.range g := by
    apply Set.Subset.antisymm
    · rintro x ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := exists_complexUnitBandEvenValue_eq_signedValue_sq ha j
      exact ⟨k, hk⟩
    · rintro x ⟨k, rfl⟩
      obtain ⟨j, hj⟩ := exists_signedValue_sq_eq_complexUnitBandEvenValue ha k
      exact ⟨j, hj⟩
  have hrangeNeg : Set.range (fun n => -f n) = Set.range (fun n => -g n) := by
    apply Set.Subset.antisymm
    · rintro x ⟨j, rfl⟩
      have hj : f j ∈ Set.range g := hrange ▸ Set.mem_range_self j
      obtain ⟨k, hk⟩ := hj
      exact ⟨k, congrArg Neg.neg hk⟩
    · rintro x ⟨k, rfl⟩
      have hk : g k ∈ Set.range f := hrange.symm ▸ Set.mem_range_self k
      obtain ⟨j, hj⟩ := hk
      exact ⟨j, congrArg Neg.neg hj⟩
  have hneg : (fun n => -f n) = (fun n => -g n) :=
    (hf.neg.range_inj hg.neg).mp hrangeNeg
  have hfg : f = g := by
    funext n
    exact neg_inj.mp (congrFun hneg n)
  exact (congrFun hfg n).symm

/-- Global positive-aperture continuity of every actual squared signed prolate mode. -/
theorem continuousOn_evenProlateSignedValue_sq (n : ℕ) :
    ContinuousOn (fun a : ℝ => evenProlateSignedValue a n ^ 2) (Set.Ioi 0) := by
  have hc : Continuous fun a : ℝ => 2 * Real.pi * a ^ 2 := by fun_prop
  have hcont : Continuous fun a : ℝ =>
      complexUnitBandEvenValue (2 * Real.pi * a ^ 2) n :=
    (continuous_complexUnitBandEvenValue n).comp hc
  refine hcont.continuousOn.congr ?_
  intro a ha
  exact (complexUnitBandEvenValue_eq_evenProlateSignedValue_sq ha n).symm

end GaloisForLFunctions.RHTower
