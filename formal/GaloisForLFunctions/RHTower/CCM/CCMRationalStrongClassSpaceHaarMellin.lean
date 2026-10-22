import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongClassSpaceLFTopology
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogMellinContinuity
import Mathlib.MeasureTheory.Measure.Haar.Basic

open Complex MeasureTheory Set Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

private abbrev U := CCMRationalProfiniteUnit
private abbrev Strong := _root_.RHTower.DeningerMeyerStrongLogTarget
private abbrev Class := CCMRationalStrongClassSpace

local instance cCMRationalStrongClassSpaceHaarMellinLocalInst1 : MeasurableSpace U := borel U
local instance cCMRationalStrongClassSpaceHaarMellinLocalInst2 : BorelSpace U := ⟨rfl⟩

/-- Whole profinite-unit group as Haar normalizing compact. -/
def ccmRationalProfiniteUnitPositiveCompact :
    TopologicalSpace.PositiveCompacts U :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Probability Haar measure on the compact profinite-unit factor. -/
def ccmRationalProfiniteUnitHaar : Measure U :=
  Measure.haarMeasure ccmRationalProfiniteUnitPositiveCompact

@[simp]
theorem ccmRationalProfiniteUnitHaar_univ :
    ccmRationalProfiniteUnitHaar Set.univ = 1 := by
  exact Measure.haarMeasure_self

local instance ccmRationalProfiniteUnitHaarProbability :
    IsProbabilityMeasure ccmRationalProfiniteUnitHaar :=
  ⟨ccmRationalProfiniteUnitHaar_univ⟩

private theorem ccmRationalStrongClassSpaceMellin_integrable
    (s : ℂ) (f : Class) :
    Integrable (fun u : U =>
      _root_.RHTower.deningerMeyerStrongLogMellinLM s (f u))
      ccmRationalProfiniteUnitHaar := by
  let h : LocallyConstant U ℂ :=
    LocallyConstant.map
      (_root_.RHTower.deningerMeyerStrongLogMellinLM s) f
  change Integrable h ccmRationalProfiniteUnitHaar
  exact h.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace h)

/-- Trivial compact-character Mellin transform on the exact strong class
space. -/
def ccmRationalStrongClassSpaceTrivialMellinLM (s : ℂ) :
    Class →ₗ[ℂ] ℂ where
  toFun f := ∫ u : U,
    _root_.RHTower.deningerMeyerStrongLogMellinLM s (f u)
      ∂ccmRationalProfiniteUnitHaar
  map_add' f g := by
    change (∫ u : U,
      _root_.RHTower.deningerMeyerStrongLogMellinLM s ((f + g) u)
        ∂ccmRationalProfiniteUnitHaar) = _
    rw [show (fun u : U =>
        _root_.RHTower.deningerMeyerStrongLogMellinLM s ((f + g) u)) =
      (fun u : U =>
        _root_.RHTower.deningerMeyerStrongLogMellinLM s (f u)) +
      fun u : U =>
        _root_.RHTower.deningerMeyerStrongLogMellinLM s (g u) by
      funext u
      exact map_add
        (_root_.RHTower.deningerMeyerStrongLogMellinLM s) (f u) (g u)]
    exact integral_add
      (ccmRationalStrongClassSpaceMellin_integrable s f)
      (ccmRationalStrongClassSpaceMellin_integrable s g)
  map_smul' c f := by
    change (∫ u : U,
      _root_.RHTower.deningerMeyerStrongLogMellinLM s ((c • f) u)
        ∂ccmRationalProfiniteUnitHaar) = _
    rw [show (fun u : U =>
        _root_.RHTower.deningerMeyerStrongLogMellinLM s ((c • f) u)) =
      fun u : U => c *
        _root_.RHTower.deningerMeyerStrongLogMellinLM s (f u) by
      funext u
      exact map_smul
        (_root_.RHTower.deningerMeyerStrongLogMellinLM s) c (f u)]
    exact integral_const_mul c _

@[simp]
theorem ccmRationalStrongClassSpaceTrivialMellinLM_apply
    (s : ℂ) (f : Class) :
    ccmRationalStrongClassSpaceTrivialMellinLM s f =
      ∫ u : U, _root_.RHTower.deningerMeyerStrongLogMellinLM s (f u)
        ∂ccmRationalProfiniteUnitHaar :=
  rfl

theorem ccmRationalStrongClassSpaceTrivialMellinLM_stage
    (s : ℂ) (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) :
    ccmRationalStrongClassSpaceTrivialMellinLM s
        (ccmRationalStrongClassSpaceLFStage i g) =
      ∑ j, (∫ u : U, i.coefficient j u ∂ccmRationalProfiniteUnitHaar) *
        _root_.RHTower.deningerMeyerStrongLogMellinLM s (g j) := by
  rw [ccmRationalStrongClassSpaceTrivialMellinLM_apply]
  simp_rw [ccmRationalStrongClassSpaceLFStage_apply, map_sum, map_smul,
    smul_eq_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact integral_mul_const _ _
  · intro j hj
    let a : LocallyConstant U ℂ := i.coefficient j
    have ha : Integrable a ccmRationalProfiniteUnitHaar :=
      a.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace a)
    exact ha.mul_const _

/-- Haar--Mellin evaluation is continuous for the literal profinite LF and
radial all-weight topology. -/
theorem continuous_ccmRationalStrongClassSpaceTrivialMellinLM (s : ℂ) :
    @Continuous Class ℂ ccmRationalStrongClassSpaceLFTopology inferInstance
      (ccmRationalStrongClassSpaceTrivialMellinLM s) := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  letI : ContinuousAdd Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousAdd
  letI : ContinuousSMul ℂ Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousSMul
  apply (linearFinalTopology_continuous_iff ℂ
    ccmRationalStrongClassSpaceLFStageSpace Class
    ccmRationalStrongClassSpaceLFStage
    (tW := inferInstance) inferInstance inferInstance
    (ccmRationalStrongClassSpaceTrivialMellinLM s)).2
  intro i
  have heq :
      (fun g : ccmRationalStrongClassSpaceLFStageSpace i =>
        ccmRationalStrongClassSpaceTrivialMellinLM s
          (ccmRationalStrongClassSpaceLFStage i g)) =
      fun g => ∑ j,
        (∫ u : U, i.coefficient j u ∂ccmRationalProfiniteUnitHaar) *
          _root_.RHTower.deningerMeyerStrongLogMellinLM s (g j) := by
    funext g
    exact ccmRationalStrongClassSpaceTrivialMellinLM_stage s i g
  rw [show (ccmRationalStrongClassSpaceTrivialMellinLM s).comp
      (ccmRationalStrongClassSpaceLFStage i) =
        fun g => ccmRationalStrongClassSpaceTrivialMellinLM s
          (ccmRationalStrongClassSpaceLFStage i g) from rfl,
    heq]
  apply continuous_finset_sum
  intro j hj
  exact continuous_const.mul
    (_root_.RHTower.continuous_deningerMeyerStrongLogMellinLM s |>.comp
      (continuous_apply j))

/-- Constant profinite profiles have Haar--Mellin transform equal to their
ordinary radial Mellin transform. -/
@[simp]
theorem ccmRationalStrongClassSpaceTrivialMellinLM_const
    (s : ℂ) (g : Strong) :
    ccmRationalStrongClassSpaceTrivialMellinLM s
        (LocallyConstant.const U g) =
      _root_.RHTower.deningerMeyerStrongLogMellinLM s g := by
  rw [ccmRationalStrongClassSpaceTrivialMellinLM_apply]
  simp

end

end GaloisForLFunctions.RHTower
