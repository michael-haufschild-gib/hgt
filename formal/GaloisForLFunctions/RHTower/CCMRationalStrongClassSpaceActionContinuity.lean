import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpaceLFTopology
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogFlowContinuity

/-!
# Continuity of class-space translation on `S(C_ℚ)`

Right translation transports a finite locally constant coefficient packet by
precomposition on `Ẑˣ` and applies one fixed continuous logarithmic flow to
each radial coefficient.  Hence it maps every LF stage continuously to
another LF stage.  The linear final-topology universal property then proves
continuity on the full exact strong class space.
-/

noncomputable section

open Topology

namespace GaloisForLFunctions.RHTower

private abbrev Strong := _root_.RHTower.DeningerMeyerStrongLogTarget
private abbrev Class := CCMRationalStrongClassSpace

/-- Coefficient packet transported in the profinite direction. -/
@[reducible]
def ccmRationalStrongClassSpaceRightActionIndex
    (c : CCMRationalClassSpaceSection)
    (i : CCMRationalStrongClassSpaceLFIndex) :
    CCMRationalStrongClassSpaceLFIndex where
  carrier := i.carrier
  coefficient j := LocallyConstant.comap
    (ccmRationalProfiniteRightMul c.1) (i.coefficient j)

/-- Radial coefficient transport between the corresponding finite stages. -/
def ccmRationalStrongClassSpaceRightActionStageFlow
    (c : CCMRationalClassSpaceSection)
    (i : CCMRationalStrongClassSpaceLFIndex) :
    ccmRationalStrongClassSpaceLFStageSpace i →ₗ[ℂ]
      ccmRationalStrongClassSpaceLFStageSpace
        (ccmRationalStrongClassSpaceRightActionIndex c i) where
  toFun g j := _root_.RHTower.deningerMeyerStrongLogFlow
    (-ccmRationalPositiveUnitLog c.2) (g j)
  map_add' g h := by
    funext j
    exact map_add
      (_root_.RHTower.deningerMeyerStrongLogFlow
        (-ccmRationalPositiveUnitLog c.2)) (g j) (h j)
  map_smul' z g := by
    funext j
    exact map_smul
      (_root_.RHTower.deningerMeyerStrongLogFlow
        (-ccmRationalPositiveUnitLog c.2)) z (g j)

/-- Exact factorization of class-space translation through a transported
finite LF stage. -/
theorem ccmRationalStrongClassSpaceRightAction_stage
    (c : CCMRationalClassSpaceSection)
    (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) :
    ccmRationalStrongClassSpaceRightActionLinear c
        (ccmRationalStrongClassSpaceLFStage i g) =
      ccmRationalStrongClassSpaceLFStage
        (ccmRationalStrongClassSpaceRightActionIndex c i)
        (ccmRationalStrongClassSpaceRightActionStageFlow c i g) := by
  apply LocallyConstant.ext
  intro u
  apply Subtype.ext
  funext t
  change ((((ccmRationalStrongClassSpaceRightAction c
      (ccmRationalStrongClassSpaceLFStage i g)) u : Strong) : ℝ → ℂ) t) = _
  rw [ccmRationalStrongClassSpaceRightAction_apply,
    ccmRationalStrongClassSpaceLFStage_apply,
    ccmRationalStrongClassSpaceLFStage_apply]
  let evPlus : Strong →ₗ[ℂ] ℂ :=
    { toFun := fun h => ((h : Strong) : ℝ → ℂ)
        (t + ccmRationalPositiveUnitLog c.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ev : Strong →ₗ[ℂ] ℂ :=
    { toFun := fun h => ((h : Strong) : ℝ → ℂ) t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change evPlus (∑ j : i.carrier, (i.coefficient j) (u * c.1) • g j) =
    ev (∑ j : i.carrier,
      ((ccmRationalStrongClassSpaceRightActionIndex c i).coefficient j) u •
        ccmRationalStrongClassSpaceRightActionStageFlow c i g j)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, map_smul]
  change (i.coefficient j) (u * c.1) *
      (((g j : Strong) : ℝ → ℂ)
        (t + ccmRationalPositiveUnitLog c.2)) =
    (i.coefficient j) (u * c.1) *
      (((_root_.RHTower.deningerMeyerStrongLogFlow
        (-ccmRationalPositiveUnitLog c.2) (g j) : Strong) : ℝ → ℂ) t)
  rw [_root_.RHTower.deningerMeyerStrongLogFlow_apply]
  congr 2
  ring

theorem ccmRationalStrongClassSpaceRightActionStageFlow_continuous
    (c : CCMRationalClassSpaceSection)
    (i : CCMRationalStrongClassSpaceLFIndex) :
    @Continuous
      (ccmRationalStrongClassSpaceLFStageSpace i)
      (ccmRationalStrongClassSpaceLFStageSpace
        (ccmRationalStrongClassSpaceRightActionIndex c i))
      (by
        letI : TopologicalSpace Strong :=
          _root_.RHTower.deningerMeyerStrongLogTopology
        exact inferInstance)
      (by
        letI : TopologicalSpace Strong :=
          _root_.RHTower.deningerMeyerStrongLogTopology
        exact inferInstance)
      (ccmRationalStrongClassSpaceRightActionStageFlow c i) := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  exact continuous_pi fun j =>
    (_root_.RHTower.deningerMeyerStrongLogFlow_continuous
      (-ccmRationalPositiveUnitLog c.2)).comp (continuous_apply j)

/-- Right translation by every fixed class-space element is continuous for
the exact profinite-LF/radial-strong topology. -/
theorem ccmRationalStrongClassSpaceRightAction_continuous
    (c : CCMRationalClassSpaceSection) :
    @Continuous Class Class ccmRationalStrongClassSpaceLFTopology
      ccmRationalStrongClassSpaceLFTopology
      (ccmRationalStrongClassSpaceRightActionLinear c) := by
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
  apply (linearFinalTopology_continuous_iff ℂ
    ccmRationalStrongClassSpaceLFStageSpace Class
    ccmRationalStrongClassSpaceLFStage
    ccmRationalStrongClassSpaceLFTopology
    ccmRationalStrongClassSpaceLFTopology_continuousAdd
    ccmRationalStrongClassSpaceLFTopology_continuousSMul
    (ccmRationalStrongClassSpaceRightActionLinear c)).2
  intro i
  rw [show (ccmRationalStrongClassSpaceRightActionLinear c).comp
        (ccmRationalStrongClassSpaceLFStage i) =
      (ccmRationalStrongClassSpaceLFStage
        (ccmRationalStrongClassSpaceRightActionIndex c i)).comp
          (ccmRationalStrongClassSpaceRightActionStageFlow c i) by
    apply LinearMap.ext
    intro g
    exact ccmRationalStrongClassSpaceRightAction_stage c i g]
  exact (ccmRationalStrongClassSpaceLFStage_continuous _).comp
    (ccmRationalStrongClassSpaceRightActionStageFlow_continuous c i)

end GaloisForLFunctions.RHTower
