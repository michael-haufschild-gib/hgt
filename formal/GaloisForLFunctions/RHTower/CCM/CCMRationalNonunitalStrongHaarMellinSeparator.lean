import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicClosedNonunitalStrongLefschetz
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongClassSpaceHaarMellin
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongTraceMultiplicationFracture
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerLogGaussianUniversalOrbitCriterion

/-!
# Haar--Mellin separation in the literal closed CCM quotient

The literal nonunital strong target has a canonical strong class-space
coordinate: embed it faithfully into the pointwise model and read its unique
diagonal trace representative.  Haar averaging in the profinite-unit
direction followed by radial Mellin evaluation is therefore a continuous
linear functional on every target degree.

In degree zero an explicit trace-one ideal field carrying the log-Gaussian
profile gives a chain whose Haar--Mellin value never vanishes.  Consequently,
any spectral parameter at which the exact adelic restriction is annihilated
separates a nonzero class in the literal closed relative quotient.  The final
hypothesis is deliberately stated on the exact source image; proving it at
zeta zeros is the arithmetic Tate-factorization gate, not a formal surrogate.
-/

noncomputable section

open CategoryTheory Set Topology

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev U := CCMRationalProfiniteUnit
private abbrev Ideal := CCMRationalMoritaTraceNormOperator
private abbrev IdealField := CCMRationalContinuousTraceNormIdealField
private abbrev FieldUnit :=
  CCMRationalContinuousTraceNormIdealFieldUnitization
private abbrev Strong := _root_.RHTower.DeningerMeyerStrongLogTarget
private abbrev StrongClass := CCMRationalStrongClassSpace
private abbrev TargetDegree (n : ℕ) :=
  CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n
private abbrev SourceDegree (n : ℕ) :=
  CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial.degree n

/-! ## Exact continuous spectral coordinate -/

/-- Logarithmic radius is continuous on the positive-unit factor. -/
theorem ccmRationalPositiveUnitLog_continuous :
    Continuous ccmRationalPositiveUnitLog := by
  rw [continuous_iff_continuousAt]
  intro r
  unfold ccmRationalPositiveUnitLog
  have hlog : ContinuousAt Real.log (((r.val : NNReal) : ℝ)) :=
    Real.continuousAt_log
      (ne_of_gt (ccmRationalPositiveUnit_coe_pos r))
  have hin : ContinuousAt
      (fun q : Units NNReal => (((q.val : NNReal) : ℝ))) r := by
    fun_prop
  simpa [Function.comp_def] using
    (ContinuousAt.comp
      (f := fun q : Units NNReal => (((q.val : NNReal) : ℝ)))
      (g := Real.log) hlog hin)

/-- Unique exact strong class-space representative of the literal target's
diagonal trace. -/
def ccmRationalNonunitalStrongDiagonalCoordinate (n : ℕ) :
    TargetDegree n →ₗ[ℂ] StrongClass :=
  (ccmRationalStrongDiagonalCoordinate n).comp
    (ccmRationalNonunitalStrongCyclicEmbeddingDegree n)

@[simp]
theorem ccmRationalNonunitalStrongDiagonalCoordinate_eval
    (n : ℕ) (x : TargetDegree n) :
    ccmRationalStrongClassSpaceEvalLinear
        (ccmRationalNonunitalStrongDiagonalCoordinate n x) =
      ccmRationalNonunitalStrongDiagonalTrace n x.1 := by
  rw [ccmRationalNonunitalStrongDiagonalCoordinate,
    LinearMap.comp_apply, ccmRationalStrongDiagonalCoordinate_eval,
    ccmRationalNonunitalStrongCyclicEmbeddingDegree_coe,
    ccmRationalNonunitalStrongDiagonalTrace_embedding]

/-- Exact diagonal coordinate is continuous for the literal induced cyclic
topology and the profinite-LF/all-weight radial topology. -/
theorem continuous_ccmRationalNonunitalStrongDiagonalCoordinate (n : ℕ) :
    @Continuous (TargetDegree n) StrongClass
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      ccmRationalStrongClassSpaceLFTopology
      (ccmRationalNonunitalStrongDiagonalCoordinate n) := by
  letI : TopologicalSpace (TargetDegree n) :=
    ccmRationalNonunitalStrongCyclicDegreeTopology n
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  exact (continuous_ccmRationalStrongDiagonalCoordinate n).comp
    (continuous_ccmRationalNonunitalStrongCyclicEmbeddingDegree n)

/-- Trivial compact-character Haar--Mellin functional on one literal strong
cyclic degree. -/
def ccmRationalNonunitalStrongHaarMellinLM (n : ℕ) (s : ℂ) :
    TargetDegree n →ₗ[ℂ] ℂ :=
  (ccmRationalStrongClassSpaceTrivialMellinLM s).comp
    (ccmRationalNonunitalStrongDiagonalCoordinate n)

/-- Haar--Mellin functional is continuous on the literal target. -/
theorem continuous_ccmRationalNonunitalStrongHaarMellinLM
    (n : ℕ) (s : ℂ) :
    @Continuous (TargetDegree n) ℂ
      (ccmRationalNonunitalStrongCyclicDegreeTopology n) inferInstance
      (ccmRationalNonunitalStrongHaarMellinLM n s) := by
  letI : TopologicalSpace (TargetDegree n) :=
    ccmRationalNonunitalStrongCyclicDegreeTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  exact (continuous_ccmRationalStrongClassSpaceTrivialMellinLM s).comp
    (continuous_ccmRationalNonunitalStrongDiagonalCoordinate n)

/-! ## Explicit Gaussian trace-one chain -/

/-- Trace-one ideal coefficient used to carry an arbitrary scalar radial
profile without introducing a scalar unitization component. -/
def ccmRationalMoritaGaussianCarrier : Ideal :=
  ccmRationalMoritaMatrixUnitOneNeg *
    ccmRationalMoritaMatrixUnitNegOne

@[simp]
theorem ccmRationalMoritaGaussianCarrier_trace :
    ccmRationalMoritaTraceNormOperatorTrace
        ccmRationalMoritaGaussianCarrier = 1 := by
  exact ccmRationalMoritaMatrixUnit_mul_trace

/-- Continuous ideal field equal to the log-Gaussian scalar profile times a
fixed trace-one ideal element. -/
def ccmRationalNonunitalLogGaussianIdealField : IdealField where
  toFun b :=
    _root_.RHTower.deningerMeyerLogGaussianProfile
        (ccmRationalPositiveUnitLog b.2) •
      ccmRationalMoritaGaussianCarrier
  continuous_toFun := by
    have hlog : Continuous
        (fun b : Section => ccmRationalPositiveUnitLog b.2) :=
      ccmRationalPositiveUnitLog_continuous.comp continuous_snd
    have hscalar : Continuous
        (fun b : Section =>
          _root_.RHTower.deningerMeyerLogGaussianProfile
            (ccmRationalPositiveUnitLog b.2)) :=
      _root_.RHTower.deningerMeyerLogGaussianProfile_smooth.continuous.comp
        hlog
    exact hscalar.smul continuous_const

@[simp]
theorem ccmRationalNonunitalLogGaussianIdealField_trace
    (b : Section) :
    ccmRationalMoritaTraceNormOperatorTrace
        (ccmRationalNonunitalLogGaussianIdealField b) =
      _root_.RHTower.deningerMeyerLogGaussianProfile
        (ccmRationalPositiveUnitLog b.2) := by
  change ccmRationalMoritaTraceNormOperatorTrace
      (_root_.RHTower.deningerMeyerLogGaussianProfile
          (ccmRationalPositiveUnitLog b.2) •
        ccmRationalMoritaGaussianCarrier) = _
  rw [map_smul, ccmRationalMoritaGaussianCarrier_trace]
  simp

/-- Canonical degree-zero one-tensor in the global unitization carrying the
Gaussian ideal field. -/
def ccmRationalNonunitalLogGaussianAmbientChain :
    CyclicBarTensor ℂ FieldUnit 0 :=
  PiTensorProduct.tprod ℂ (fun _ : Fin 1 =>
    (ccmRationalNonunitalLogGaussianIdealField : FieldUnit))

@[simp]
theorem ccmRationalNonunitalLogGaussianAmbientChain_augmentation :
    cyclicBarTraceAugmentation
        ccmRationalNonunitalFieldAugmentation 0
        ccmRationalNonunitalLogGaussianAmbientChain = 0 := by
  simp [ccmRationalNonunitalLogGaussianAmbientChain,
    ccmRationalNonunitalFieldAugmentation]

/-- Diagonal trace of the Gaussian ideal-field chain is exactly the scalar
realization of the constant-profinite strong log-Gaussian. -/
theorem ccmRationalNonunitalLogGaussianAmbientChain_trace :
    ccmRationalNonunitalStrongDiagonalTrace 0
        ccmRationalNonunitalLogGaussianAmbientChain =
      ccmRationalStrongClassSpaceEvalLinear
        (LocallyConstant.const U
          _root_.RHTower.deningerMeyerLogGaussianSource) := by
  funext b
  change (cyclicBarModuleTraceAugmentation
      ccmRationalNonunitalFieldTrace 0
        ccmRationalNonunitalLogGaussianAmbientChain) b = _
  rw [ccmRationalNonunitalLogGaussianAmbientChain,
    cyclicBarModuleTraceAugmentation_zero_tprod]
  change ccmRationalNonunitalFieldPointTrace b
      (ccmRationalNonunitalLogGaussianIdealField : FieldUnit) = _
  rw [ccmRationalNonunitalFieldPointTrace_apply,
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_inr,
    ccmRationalMoritaTraceNormL1InrHom_apply]
  simpa [ccmRationalMoritaTraceNormL1Trace_apply,
    ccmRationalStrongClassSpaceEvalLinear_apply,
    ccmRationalNonunitalStrongDiagonalTrace,
    cyclicBarModuleTraceAugmentation, cyclicBarTotalProduct,
    ccmRationalNonunitalLogGaussianAmbientChain,
    ccmRationalNonunitalFieldTrace,
    ccmRationalNonunitalFieldPointTrace,
    _root_.RHTower.deningerMeyerLogGaussianSource,
    _root_.RHTower.deningerMeyerLogGaussianProfile] using
      ccmRationalNonunitalLogGaussianIdealField_trace b

/-- Explicit literal Definition 4.9 chain with Gaussian diagonal trace and
zero global augmentation. -/
def ccmRationalNonunitalLogGaussianStrongChain : TargetDegree 0 :=
  ⟨ccmRationalNonunitalLogGaussianAmbientChain,
    (mem_ccmRationalNonunitalStrongCyclicTarget_iff 0 _).mpr
      ⟨ccmRationalNonunitalLogGaussianAmbientChain_augmentation, by
        rw [ccmRationalNonunitalLogGaussianAmbientChain_trace]
        exact ⟨LocallyConstant.const U
          _root_.RHTower.deningerMeyerLogGaussianSource, rfl⟩⟩⟩

@[simp]
theorem ccmRationalNonunitalStrongDiagonalCoordinate_logGaussian :
    ccmRationalNonunitalStrongDiagonalCoordinate 0
        ccmRationalNonunitalLogGaussianStrongChain =
      LocallyConstant.const U
        _root_.RHTower.deningerMeyerLogGaussianSource := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  rw [ccmRationalNonunitalStrongDiagonalCoordinate_eval]
  exact ccmRationalNonunitalLogGaussianAmbientChain_trace

@[simp]
theorem ccmRationalNonunitalStrongHaarMellinLM_logGaussian (s : ℂ) :
    ccmRationalNonunitalStrongHaarMellinLM 0 s
        ccmRationalNonunitalLogGaussianStrongChain =
      _root_.RHTower.deningerMeyerStrongLogMellin
        _root_.RHTower.deningerMeyerLogGaussianSource s := by
  rw [ccmRationalNonunitalStrongHaarMellinLM, LinearMap.comp_apply,
    ccmRationalNonunitalStrongDiagonalCoordinate_logGaussian,
    ccmRationalStrongClassSpaceTrivialMellinLM_const]
  rfl

theorem ccmRationalNonunitalStrongHaarMellinLM_logGaussian_ne_zero
    (s : ℂ) :
    ccmRationalNonunitalStrongHaarMellinLM 0 s
        ccmRationalNonunitalLogGaussianStrongChain ≠ 0 := by
  rw [ccmRationalNonunitalStrongHaarMellinLM_logGaussian]
  exact _root_.RHTower.deningerMeyerLogGaussianSource_mellin_ne_zero s

/-! ## Closed-range separation -/

/-- A continuous spectral functional annihilating the exact restriction
also annihilates its topological closure. -/
theorem ccmRationalAdelicClosedNonunitalStrongRestrictionRange_le_mellinKer
    (s : ℂ)
    (hsource : ∀ x : SourceDegree 0,
      ccmRationalNonunitalStrongHaarMellinLM 0 s
        (ccmRationalAdelicReducedNonunitalStrongCyclicDegree 0 x) = 0) :
    CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0 ≤
      (ccmRationalNonunitalStrongHaarMellinLM 0 s).ker := by
  letI : TopologicalSpace (TargetDegree 0) :=
    ccmRationalNonunitalStrongCyclicDegreeTopology 0
  letI : ContinuousAdd (TargetDegree 0) :=
    ccmRationalNonunitalStrongCyclicDegreeContinuousAdd 0
  letI : ContinuousSMul ℂ (TargetDegree 0) :=
    ccmRationalNonunitalStrongCyclicDegreeContinuousSMul 0
  change
    (LinearMap.range
      (ccmRationalAdelicReducedNonunitalStrongCyclicDegree 0)).topologicalClosure ≤
      (ccmRationalNonunitalStrongHaarMellinLM 0 s).ker
  apply Submodule.topologicalClosure_minimal
  · rintro y ⟨x, rfl⟩
    exact hsource x
  · change IsClosed
      {x : TargetDegree 0 |
        ccmRationalNonunitalStrongHaarMellinLM 0 s x = 0}
    exact isClosed_singleton.preimage
      (continuous_ccmRationalNonunitalStrongHaarMellinLM 0 s)

/-- Exact source annihilation at one spectral parameter forces the explicit
Gaussian chain to survive in the literal CCM Definition 4.10 closed quotient. -/
theorem ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero_of_source_vanishes
    (s : ℂ)
    (hsource : ∀ x : SourceDegree 0,
      ccmRationalNonunitalStrongHaarMellinLM 0 s
        (ccmRationalAdelicReducedNonunitalStrongCyclicDegree 0 x) = 0) :
    (CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0).mkQ
        ccmRationalNonunitalLogGaussianStrongChain ≠ 0 := by
  intro hzero
  have hmem : ccmRationalNonunitalLogGaussianStrongChain ∈
      CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0 := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hzero
  have hker :=
    ccmRationalAdelicClosedNonunitalStrongRestrictionRange_le_mellinKer
      s hsource hmem
  exact ccmRationalNonunitalStrongHaarMellinLM_logGaussian_ne_zero s hker

end GaloisForLFunctions.RHTower
