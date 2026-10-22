import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicTensorHaarMobiusCompression
import GaloisForLFunctions.RHTower.CCM.CCMRationalNonunitalStrongHaarMellinSeparator
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPoissonMellinFactorization
import GaloisForLFunctions.RHTower.MobiusOrderLowerBound

/-!
# Adelic Haar--Mellin boundary law

Finite-fibre LF descent commutes with normalized profinite Haar averaging.
Combined with full-tensor Möbius compression, this gives one universal law:
every degree-zero reduced adelic Haar--Mellin value is the Mellin transform of
a literal Meyer Poisson boundary.  Zeta-zero annihilation is then exact on the
source and, by continuity, on its closed range in CCM Definition 4.10.
-/

noncomputable section

open CategoryTheory Complex MeasureTheory Set Topology
open scoped Classical BigOperators RestrictedProduct algebraMap FourierTransform SchwartzMap

namespace GaloisForLFunctions.RHTower

private abbrev U := CCMRationalProfiniteUnit
private abbrev Strong := _root_.RHTower.DeningerMeyerStrongLogTarget
private abbrev Class := CCMRationalStrongClassSpace
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev TwistedSource := CCMRationalAdelicTwistedCyclicSourceAlgebra
private abbrev LegacySource := CCMRationalAdelicCyclicSourceAlgebra
private abbrev SourceDegree :=
  CCMRationalAdelicTwistedReducedSourceCyclicModule.simplicial.degree 0

local instance cCMRationalAdelicHaarMellinBoundaryLawLocalInst1 : MeasurableSpace U := borel U
local instance cCMRationalAdelicHaarMellinBoundaryLawLocalInst2 : BorelSpace U := ⟨rfl⟩
local instance cCMRationalAdelicHaarMellinBoundaryLawLocalInst3 : IsProbabilityMeasure ccmRationalProfiniteUnitHaar :=
  ⟨ccmRationalProfiniteUnitHaar_univ⟩

/-! ## Finite-fibre Haar descent -/

/-- Strong radial profile obtained by Haar averaging one finite LF stage. -/
def ccmRationalStrongClassSpaceLFStageHaarAverage
    (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) : Strong :=
  ∑ j, (∫ u : U, i.coefficient j u
    ∂ccmRationalProfiniteUnitHaar) • g j

theorem ccmRationalStrongClassSpaceLFStageHaarAverage_apply
    (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) (t : ℝ) :
    (((ccmRationalStrongClassSpaceLFStageHaarAverage i g : Strong) :
        ℝ → ℂ) t) =
      ∫ u : U,
        ((((ccmRationalStrongClassSpaceLFStage i g) u : Strong) :
          ℝ → ℂ) t) ∂ccmRationalProfiniteUnitHaar := by
  let E : Strong →ₗ[ℂ] ℂ :=
    { toFun := fun h => ((h : ℝ → ℂ) t)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  change E (ccmRationalStrongClassSpaceLFStageHaarAverage i g) =
    ∫ u : U, E (ccmRationalStrongClassSpaceLFStage i g u)
      ∂ccmRationalProfiniteUnitHaar
  rw [ccmRationalStrongClassSpaceLFStageHaarAverage, map_sum]
  simp_rw [ccmRationalStrongClassSpaceLFStage_apply,
    map_sum, map_smul, smul_eq_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const]
  · intro j hj
    let a : LocallyConstant U ℂ := i.coefficient j
    have ha : Integrable a ccmRationalProfiniteUnitHaar :=
      a.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace a)
    exact ha.mul_const _

theorem ccmRationalStrongClassSpaceTrivialMellinLM_stageHaarAverage
    (s : ℂ) (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) :
    ccmRationalStrongClassSpaceTrivialMellinLM s
        (ccmRationalStrongClassSpaceLFStage i g) =
      _root_.RHTower.deningerMeyerStrongLogMellinLM s
        (ccmRationalStrongClassSpaceLFStageHaarAverage i g) := by
  rw [ccmRationalStrongClassSpaceTrivialMellinLM_stage]
  rw [ccmRationalStrongClassSpaceLFStageHaarAverage, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Every exact strong class-space function has one Haar-averaged strong
radial profile, simultaneously for all spectral parameters. -/
theorem ccmRationalStrongClassSpace_exists_haarAverage
    (C : Class) :
    ∃ A : Strong,
      (∀ t : ℝ, ((A : ℝ → ℂ) t) =
        ∫ u : U, ((((C u : Strong) : ℝ → ℂ) t))
          ∂ccmRationalProfiniteUnitHaar) ∧
      ∀ s : ℂ,
        ccmRationalStrongClassSpaceTrivialMellinLM s C =
          _root_.RHTower.deningerMeyerStrongLogMellinLM s A := by
  obtain ⟨i, g, hstage⟩ :=
    ccmRationalStrongClassSpaceLFStage_surjective C
  refine ⟨ccmRationalStrongClassSpaceLFStageHaarAverage i g, ?_, ?_⟩
  · intro t
    rw [← hstage]
    exact ccmRationalStrongClassSpaceLFStageHaarAverage_apply i g t
  · intro s
    rw [← hstage]
    exact ccmRationalStrongClassSpaceTrivialMellinLM_stageHaarAverage s i g

/-! ## Tensor boundary factorization -/

/-- Haar--Mellin transform of an endpoint-zero tensor class is exactly the
Mellin transform of its Haar--Möbius Meyer boundary. -/
theorem ccmRationalStrongClassSpaceTrivialMellinLM_tensor_eq_boundary
    (x : Core)
    (hzero : ccmRationalAdelicBruhatZeroEval x = 0)
    (hone : ccmRationalAdelicBruhatIntegral x = 0)
    (P : CCMRationalAdelicTensorHaarMobiusPacket x) (s : ℂ) :
    ccmRationalStrongClassSpaceTrivialMellinLM s
        (ccmRationalAdelicTensorStrongClassSpace x hzero hone) =
      _root_.RHTower.deningerMeyerStrongLogMellinLM s
        (_root_.RHTower.deningerMeyerStrongLogSumLM
          (P.toMeyerCap hzero hone)) := by
  obtain ⟨A, hA, hMellin⟩ :=
    ccmRationalStrongClassSpace_exists_haarAverage
      (ccmRationalAdelicTensorStrongClassSpace x hzero hone)
  rw [hMellin]
  congr 1
  apply Subtype.ext
  funext t
  rw [hA t]
  change (∫ u : U, ccmRationalAdelicTensorUnitLogTrace x u t
      ∂ccmRationalProfiniteUnitHaar) =
    ((_root_.RHTower.deningerMeyerStrongLogSumLM
      (P.toMeyerCap hzero hone) : Strong) : ℝ → ℂ) t
  rw [_root_.RHTower.deningerMeyerStrongLogSumLM_apply]
  calc
    (∫ u : U, ccmRationalAdelicTensorUnitLogTrace x u t
        ∂ccmRationalProfiniteUnitHaar) =
        ∫ u : U, (∑' q : ℚ,
          ccmRationalAdelicBruhatTensorOrbit
            x (Real.exp t) u.1 q)
          ∂ccmRationalProfiniteUnitHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u =>
        (ccmRationalAdelicBruhatTensorOrbitSum_eq_unitOrbitSum
          x (Real.exp t) u.1 hzero).symm
    _ = ccmRationalAdelicTensorProfiniteHaarRationalLogTrace x t := rfl
    _ = _root_.RHTower.deningerMeyerSum P.source (Real.exp t) := by
      have ht := congrFun P.haarTrace_eq t
      simpa [hzero] using ht

/-! ## Exact reduced source -/

/-- Legacy total product underlying one degree-zero chain of the sealed
reduced adelic source. -/
def ccmRationalAdelicTwistedReducedDegreeZeroProduct
    (x : SourceDegree) : LegacySource :=
  ccmRationalAdelicTwistedSourceToLegacy
    (cyclicBarTotalProduct 0 x.1.1)

/-- Identity-scaling Bruhat coefficient controlling both degree-zero Tate
endpoints and the diagonal class-space trace. -/
def ccmRationalAdelicTwistedReducedDegreeZeroCore
    (x : SourceDegree) : Core :=
  (ccmRationalAdelicTwistedReducedDegreeZeroProduct x).snd 1

@[simp]
theorem ccmRationalAdelicTwistedReducedDegreeZeroProduct_fst
    (x : SourceDegree) :
    (ccmRationalAdelicTwistedReducedDegreeZeroProduct x).fst = 0 := by
  have haug := x.1.2.1
  change cyclicBarTraceAugmentation
    ccmRationalAdelicTwistedUnitizationAugmentation 0 x.1.1 = 0 at haug
  change (cyclicBarTotalProduct 0 x.1.1).fst = 0 at haug
  simpa [ccmRationalAdelicTwistedReducedDegreeZeroProduct] using haug

theorem ccmRationalAdelicTwistedReducedDegreeZeroProduct_epsilonZero
    (x : SourceDegree) :
    ccmRationalAdelicEpsilonZero
        (ccmRationalAdelicTwistedReducedDegreeZeroProduct x) = 0 := by
  have hx0 := x.2.1
  change cyclicBarTraceAugmentation
    ccmRationalAdelicTwistedEpsilonZero 0 x.1.1 = 0 at hx0
  change ccmRationalAdelicTwistedEpsilonZero
    (cyclicBarTotalProduct 0 x.1.1) = 0 at hx0
  simpa [ccmRationalAdelicTwistedReducedDegreeZeroProduct] using hx0

theorem ccmRationalAdelicTwistedReducedDegreeZeroProduct_epsilonOne
    (x : SourceDegree) :
    ccmRationalAdelicEpsilonOne
        (ccmRationalAdelicTwistedReducedDegreeZeroProduct x) = 0 := by
  have hx1 := x.2.2
  change cyclicBarTraceAugmentation
    ccmRationalAdelicTwistedEpsilonOne 0 x.1.1 = 0 at hx1
  change ccmRationalAdelicTwistedEpsilonOne
    (cyclicBarTotalProduct 0 x.1.1) = 0 at hx1
  simpa [ccmRationalAdelicTwistedReducedDegreeZeroProduct] using hx1

@[simp]
theorem ccmRationalAdelicTwistedReducedDegreeZeroCore_zeroEval
    (x : SourceDegree) :
    ccmRationalAdelicBruhatZeroEval
        (ccmRationalAdelicTwistedReducedDegreeZeroCore x) = 0 := by
  have h :=
    ccmRationalAdelicTwistedReducedDegreeZeroProduct_epsilonZero x
  change (ccmRationalAdelicTwistedReducedDegreeZeroProduct x).fst +
      ccmRationalAdelicBruhatZeroEval
        (ccmRationalAdelicTwistedReducedDegreeZeroCore x) = 0 at h
  simpa using h

@[simp]
theorem ccmRationalAdelicTwistedReducedDegreeZeroCore_integral
    (x : SourceDegree) :
    ccmRationalAdelicBruhatIntegral
        (ccmRationalAdelicTwistedReducedDegreeZeroCore x) = 0 := by
  have h :=
    ccmRationalAdelicTwistedReducedDegreeZeroProduct_epsilonOne x
  change (ccmRationalAdelicTwistedReducedDegreeZeroProduct x).fst +
      ccmRationalAdelicBruhatIntegral
        (ccmRationalAdelicTwistedReducedDegreeZeroCore x) = 0 at h
  simpa using h

/-- Exact diagonal coordinate of the literal nonunital restriction is the
explicit strong class-space trace of its identity-scaling Bruhat core. -/
theorem ccmRationalAdelicReducedNonunitalStrongDiagonalCoordinate_zero
    (x : SourceDegree) :
    ccmRationalNonunitalStrongDiagonalCoordinate 0
        (ccmRationalAdelicReducedNonunitalStrongCyclicDegree 0 x) =
      ccmRationalAdelicTensorStrongClassSpace
        (ccmRationalAdelicTwistedReducedDegreeZeroCore x)
        (ccmRationalAdelicTwistedReducedDegreeZeroCore_zeroEval x)
        (ccmRationalAdelicTwistedReducedDegreeZeroCore_integral x) := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  rw [ccmRationalNonunitalStrongDiagonalCoordinate_eval,
    ccmRationalAdelicReducedNonunitalStrongCyclicDegree_coe,
    ccmRationalNonunitalStrongDiagonalTrace_restriction]
  funext b
  symm
  change ccmRationalAdelicTensorUnitLogTrace
      (ccmRationalAdelicTwistedReducedDegreeZeroCore x) b.1
        (ccmRationalPositiveUnitLog b.2) =
    ccmRationalAdelicSourceClassSpaceTrace
      (ccmRationalAdelicTwistedReducedDegreeZeroProduct x) b
  rw [ccmRationalAdelicSourceClassSpaceTrace_eq_orbitSum]
  rw [ccmRationalAdelicTensorUnitLogTrace,
    ccmRationalAdelicTwistedReducedDegreeZeroProduct_fst, zero_add]
  apply tsum_congr
  intro q
  simp only [ccmRationalPositiveUnitLog]
  rw [Real.exp_log (ccmRationalPositiveUnit_coe_pos b.2)]
  rfl

/-- **Universal reduced-source boundary law.** Every degree-zero exact
restriction Haar--Mellin value factors through one literal Meyer boundary,
uniformly in the spectral parameter. -/
theorem ccmRationalAdelicReducedNonunitalStrongHaarMellin_exists_boundary
    (x : SourceDegree) :
    ∃ f : _root_.RHTower.DeningerMeyerCap, ∀ s : ℂ,
      ccmRationalNonunitalStrongHaarMellinLM 0 s
          (ccmRationalAdelicReducedNonunitalStrongCyclicDegree 0 x) =
        _root_.RHTower.deningerMeyerStrongLogMellinLM s
          (_root_.RHTower.deningerMeyerStrongLogSumLM f) := by
  obtain ⟨P⟩ := ccmRationalAdelicTensor_exists_haarMobiusPacket
    (ccmRationalAdelicTwistedReducedDegreeZeroCore x)
  let hzero := ccmRationalAdelicTwistedReducedDegreeZeroCore_zeroEval x
  let hone := ccmRationalAdelicTwistedReducedDegreeZeroCore_integral x
  refine ⟨P.toMeyerCap hzero hone, ?_⟩
  intro s
  rw [ccmRationalNonunitalStrongHaarMellinLM, LinearMap.comp_apply,
    ccmRationalAdelicReducedNonunitalStrongDiagonalCoordinate_zero]
  exact ccmRationalStrongClassSpaceTrivialMellinLM_tensor_eq_boundary
    (ccmRationalAdelicTwistedReducedDegreeZeroCore x) hzero hone P s

/-- Exact reduced restriction is annihilated at every non-pole zeta zero in
the positive half-plane. -/
theorem ccmRationalAdelicReducedNonunitalStrongHaarMellin_zero_at_zeta_zero
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (hζ : riemannZeta ρ = 0) (x : SourceDegree) :
    ccmRationalNonunitalStrongHaarMellinLM 0 ρ
        (ccmRationalAdelicReducedNonunitalStrongCyclicDegree 0 x) = 0 := by
  obtain ⟨f, hf⟩ :=
    ccmRationalAdelicReducedNonunitalStrongHaarMellin_exists_boundary x
  rw [hf ρ]
  exact _root_.RHTower.deningerMeyerStrongLogMellin_boundary_zero_at_zeta_zero
    f hρ0 hρ1 hζ

/-- Every positive-half-plane zeta zero separates the explicit Gaussian
class in the literal closed CCM quotient. -/
theorem ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero_at_zeta_zero
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (hζ : riemannZeta ρ = 0) :
    (CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0).mkQ
        ccmRationalNonunitalLogGaussianStrongChain ≠ 0 :=
  ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero_of_source_vanishes
    ρ (fun x =>
      ccmRationalAdelicReducedNonunitalStrongHaarMellin_zero_at_zeta_zero
        hρ0 hρ1 hζ x)

/-- Unconditional nontriviality of literal CCM Definition 4.10. -/
theorem ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero :
    (CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0).mkQ
        ccmRationalNonunitalLogGaussianStrongChain ≠ 0 := by
  obtain ⟨ρ, hζ, hρ1, hρ0⟩ :=
    _root_.RHTower.exists_riemannZeta_eq_zero_lt_re
      (b := 0) (by norm_num)
  exact
    ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero_at_zeta_zero
      hρ0 hρ1 hζ

/-- Literal identity Lefschetz correspondence fixes a nonzero degree-zero
class; hence its recipient and correspondence are not vacuous. -/
theorem ccmRationalAdelicClosedNonunitalStrongLefschetz_exists_nonzero_fixed :
    ∃ q :
        CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule.simplicial.degree 0,
      q ≠ 0 ∧
      (ccmRationalAdelicClosedNonunitalStrongLefschetz 1).simplicial.app
          (.op (.mk 0)) q = q := by
  let q := (CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0).mkQ
    ccmRationalNonunitalLogGaussianStrongChain
  exact ⟨q,
    ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero,
    ccmRationalAdelicClosedNonunitalStrongLefschetz_one_degree 0 q⟩

end GaloisForLFunctions.RHTower
