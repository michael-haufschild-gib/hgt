import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongClassSpaceLFTopology
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogRealContinuity
import GaloisForLFunctions.RHTower.SemilinearFinalTopology

/-!
# Continuity of Real conjugation on the exact rational strong class space

On every finite profinite coefficient packet, Real conjugation conjugates the
locally constant scalar coefficients and the radial Meyer profiles.  The
semilinear final-topology criterion therefore proves continuity on the full
literal LF space `S(C_ℚ)`.
-/

noncomputable section

open Topology

namespace GaloisForLFunctions.RHTower

private abbrev Strong := _root_.RHTower.DeningerMeyerStrongLogTarget
private abbrev Class := CCMRationalStrongClassSpace

/-- Conjugate-linear bundle of the exact strong class-space Real involution. -/
def ccmRationalStrongClassSpaceRealₛₗ : Class →ₗ⋆[ℂ] Class where
  toFun := ccmRationalStrongClassSpaceReal
  map_add' := ccmRationalStrongClassSpaceReal_add
  map_smul' := ccmRationalStrongClassSpaceReal_smul

/-- Finite LF packet obtained by conjugating all profinite scalar
coefficients. -/
@[reducible]
def ccmRationalStrongClassSpaceRealIndex
    (i : CCMRationalStrongClassSpaceLFIndex) :
    CCMRationalStrongClassSpaceLFIndex where
  carrier := i.carrier
  coefficient j := LocallyConstant.map (starRingEnd ℂ) (i.coefficient j)

/-- Coordinatewise radial conjugation between a packet and its conjugate
packet. -/
def ccmRationalStrongClassSpaceRealStage
    (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) :
    ccmRationalStrongClassSpaceLFStageSpace
      (ccmRationalStrongClassSpaceRealIndex i) :=
  fun j => _root_.RHTower.deningerMeyerStrongLogConj (g j)

/-- Exact factorization of class-space Real conjugation through a conjugate
finite LF packet. -/
theorem ccmRationalStrongClassSpaceReal_stage
    (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) :
    ccmRationalStrongClassSpaceReal
        (ccmRationalStrongClassSpaceLFStage i g) =
      ccmRationalStrongClassSpaceLFStage
        (ccmRationalStrongClassSpaceRealIndex i)
        (ccmRationalStrongClassSpaceRealStage i g) := by
  apply LocallyConstant.ext
  intro u
  change _root_.RHTower.deningerMeyerStrongLogConj
      (ccmRationalStrongClassSpaceLFStage i g u) =
    ccmRationalStrongClassSpaceLFStage
      (ccmRationalStrongClassSpaceRealIndex i)
      (ccmRationalStrongClassSpaceRealStage i g) u
  rw [ccmRationalStrongClassSpaceLFStage_apply,
    ccmRationalStrongClassSpaceLFStage_apply]
  change _root_.RHTower.deningerMeyerStrongLogConjₛₗ
      (∑ j, i.coefficient j u • g j) =
    ∑ j, star (i.coefficient j u) •
      _root_.RHTower.deningerMeyerStrongLogConj (g j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact _root_.RHTower.deningerMeyerStrongLogConj_smul
    (i.coefficient j u) (g j)

/-- Coordinatewise radial conjugation is continuous between the corresponding
finite packet spaces. -/
theorem ccmRationalStrongClassSpaceRealStage_continuous
    (i : CCMRationalStrongClassSpaceLFIndex) :
    @Continuous
      (ccmRationalStrongClassSpaceLFStageSpace i)
      (ccmRationalStrongClassSpaceLFStageSpace
        (ccmRationalStrongClassSpaceRealIndex i))
      (by
        letI : TopologicalSpace Strong :=
          _root_.RHTower.deningerMeyerStrongLogTopology
        exact inferInstance)
      (by
        letI : TopologicalSpace Strong :=
          _root_.RHTower.deningerMeyerStrongLogTopology
        exact inferInstance)
      (ccmRationalStrongClassSpaceRealStage i) := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  exact continuous_pi fun j =>
    _root_.RHTower.deningerMeyerStrongLogConj_continuous.comp
      (continuous_apply j)

/-- Pointwise Real conjugation is continuous for the exact profinite-LF /
radial-strong topology. -/
theorem ccmRationalStrongClassSpaceReal_continuous :
    @Continuous Class Class ccmRationalStrongClassSpaceLFTopology
      ccmRationalStrongClassSpaceLFTopology
      ccmRationalStrongClassSpaceReal := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  letI : ContinuousAdd Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousAdd
  letI : ContinuousSMul ℂ Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousSMul
  letI : TopologicalSpace Class :=
    ccmRationalStrongClassSpaceLFTopology
  letI : ContinuousAdd Class :=
    ccmRationalStrongClassSpaceLFTopology_continuousAdd
  letI : ContinuousSMul ℂ Class :=
    ccmRationalStrongClassSpaceLFTopology_continuousSMul
  apply linearFinalTopology_semilinear_continuous ℂ
    ccmRationalStrongClassSpaceLFStageSpace Class
    ccmRationalStrongClassSpaceLFStage
    ccmRationalStrongClassSpaceLFTopology
    ccmRationalStrongClassSpaceLFTopology_continuousAdd
    ccmRationalStrongClassSpaceLFTopology_continuousSMul
    continuous_star ccmRationalStrongClassSpaceRealₛₗ
  intro i
  rw [show (fun g => ccmRationalStrongClassSpaceRealₛₗ
        (ccmRationalStrongClassSpaceLFStage i g)) =
      fun g => ccmRationalStrongClassSpaceLFStage
        (ccmRationalStrongClassSpaceRealIndex i)
        (ccmRationalStrongClassSpaceRealStage i g) by
    funext g
    exact ccmRationalStrongClassSpaceReal_stage i g]
  exact (ccmRationalStrongClassSpaceLFStage_continuous _).comp
    (ccmRationalStrongClassSpaceRealStage_continuous i)

end GaloisForLFunctions.RHTower
