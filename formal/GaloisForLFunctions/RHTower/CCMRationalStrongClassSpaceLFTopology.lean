import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpace
import GaloisForLFunctions.RHTower.CCMRationalProfiniteUnitCompact
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogTopology
import GaloisForLFunctions.RHTower.LinearFinalTopology

/-!
# LF topology of the exact rational strong class space

The profinite Bruhat direction is an algebraic inductive limit of finite
locally constant coefficient packets.  A stage is a finite family of scalar
locally constant functions on `Ẑˣ`, with coefficients in Meyer's radial strong
space.  The class-space topology is their final topological-module topology.

Every locally constant strong function has finite range because `Ẑˣ` is
compact.  Its fibre indicators give an explicit stage presentation, proved
below; thus the stages exhaust the literal strong target rather than a proper
finite-level surrogate.
-/

noncomputable section

open Set Topology

namespace GaloisForLFunctions.RHTower

private abbrev U := CCMRationalProfiniteUnit
private abbrev Strong := _root_.RHTower.DeningerMeyerStrongLogTarget
private abbrev Class := CCMRationalStrongClassSpace

local instance : DecidableEq Strong := Classical.decEq Strong

/-- One finite locally constant coefficient packet. -/
structure CCMRationalStrongClassSpaceLFIndex where
  carrier : Finset Strong
  coefficient : carrier → LocallyConstant U ℂ

/-- Domain of one finite packet stage. -/
abbrev ccmRationalStrongClassSpaceLFStageSpace
    (i : CCMRationalStrongClassSpaceLFIndex) := i.carrier → Strong

/-- Pointwise multiplication of a scalar locally constant coefficient by one
constant radial strong profile. -/
def ccmRationalStrongClassSpaceCoefficientTerm
    (a : LocallyConstant U ℂ) (g : Strong) : Class where
  toFun := fun u => a u • g
  isLocallyConstant := a.isLocallyConstant.comp (fun z : ℂ => z • g)

@[simp]
theorem ccmRationalStrongClassSpaceCoefficientTerm_apply
    (a : LocallyConstant U ℂ) (g : Strong) (u : U) :
    ccmRationalStrongClassSpaceCoefficientTerm a g u = a u • g :=
  rfl

@[simp]
theorem ccmRationalStrongClassSpaceCoefficientTerm_eval
    (a : LocallyConstant U ℂ) (g : Strong) (u : U) :
    (LocallyConstant.evalₗ ℂ u)
        (ccmRationalStrongClassSpaceCoefficientTerm a g) = a u • g :=
  rfl

/-- Linear map from one finite coefficient packet into the exact strong class
space. -/
def ccmRationalStrongClassSpaceLFStage
    (i : CCMRationalStrongClassSpaceLFIndex) :
    ccmRationalStrongClassSpaceLFStageSpace i →ₗ[ℂ] Class where
  toFun g := ∑ j, ccmRationalStrongClassSpaceCoefficientTerm
    (i.coefficient j) (g j)
  map_add' g h := by
    apply LocallyConstant.ext
    intro u
    change
      (LocallyConstant.evalₗ ℂ u)
          (∑ j, ccmRationalStrongClassSpaceCoefficientTerm
            (i.coefficient j) (g j + h j)) =
        (LocallyConstant.evalₗ ℂ u)
            (∑ j, ccmRationalStrongClassSpaceCoefficientTerm
              (i.coefficient j) (g j)) +
          (LocallyConstant.evalₗ ℂ u)
            (∑ j, ccmRationalStrongClassSpaceCoefficientTerm
              (i.coefficient j) (h j))
    simp only [map_sum, ccmRationalStrongClassSpaceCoefficientTerm_eval,
      smul_add, Finset.sum_add_distrib]
  map_smul' z g := by
    apply LocallyConstant.ext
    intro u
    change
      (LocallyConstant.evalₗ ℂ u)
          (∑ j, ccmRationalStrongClassSpaceCoefficientTerm
            (i.coefficient j) (z • g j)) =
        z • (LocallyConstant.evalₗ ℂ u)
          (∑ j, ccmRationalStrongClassSpaceCoefficientTerm
            (i.coefficient j) (g j))
    simp only [map_sum, ccmRationalStrongClassSpaceCoefficientTerm_eval,
      smul_smul, Finset.smul_sum, mul_comm]

@[simp]
theorem ccmRationalStrongClassSpaceLFStage_apply
    (i : CCMRationalStrongClassSpaceLFIndex)
    (g : ccmRationalStrongClassSpaceLFStageSpace i) (u : U) :
    ccmRationalStrongClassSpaceLFStage i g u =
      ∑ j, i.coefficient j u • g j := by
  change (LocallyConstant.evalₗ ℂ u)
      (∑ j, ccmRationalStrongClassSpaceCoefficientTerm
        (i.coefficient j) (g j)) = _
  simp only [map_sum, ccmRationalStrongClassSpaceCoefficientTerm_eval]

/-- Final topological-module topology of all finite locally constant
coefficient packets. -/
@[reducible]
def ccmRationalStrongClassSpaceLFTopology : TopologicalSpace Class := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  letI : ContinuousAdd Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousAdd
  letI : ContinuousSMul ℂ Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousSMul
  exact linearFinalTopology ℂ ccmRationalStrongClassSpaceLFStageSpace
    Class ccmRationalStrongClassSpaceLFStage

theorem ccmRationalStrongClassSpaceLFTopology_continuousAdd :
    @ContinuousAdd Class ccmRationalStrongClassSpaceLFTopology
      inferInstance := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  letI : ContinuousAdd Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousAdd
  letI : ContinuousSMul ℂ Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousSMul
  exact linearFinalTopology_continuousAdd ℂ
    ccmRationalStrongClassSpaceLFStageSpace Class
    ccmRationalStrongClassSpaceLFStage

theorem ccmRationalStrongClassSpaceLFTopology_continuousSMul :
    @ContinuousSMul ℂ Class inferInstance inferInstance
      ccmRationalStrongClassSpaceLFTopology := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  letI : ContinuousAdd Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousAdd
  letI : ContinuousSMul ℂ Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousSMul
  exact linearFinalTopology_continuousSMul ℂ
    ccmRationalStrongClassSpaceLFStageSpace Class
    ccmRationalStrongClassSpaceLFStage

theorem ccmRationalStrongClassSpaceLFStage_continuous
    (i : CCMRationalStrongClassSpaceLFIndex) :
    @Continuous (ccmRationalStrongClassSpaceLFStageSpace i) Class
      (by
        letI : TopologicalSpace Strong :=
          _root_.RHTower.deningerMeyerStrongLogTopology
        exact inferInstance)
      ccmRationalStrongClassSpaceLFTopology
      (ccmRationalStrongClassSpaceLFStage i) := by
  letI : TopologicalSpace Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology
  letI : ContinuousAdd Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousAdd
  letI : ContinuousSMul ℂ Strong :=
    _root_.RHTower.deningerMeyerStrongLogTopology_continuousSMul
  exact linearFinalTopology_stage_continuous ℂ
    ccmRationalStrongClassSpaceLFStageSpace Class
    ccmRationalStrongClassSpaceLFStage i

/-- Fibre indicator of a value of a locally constant strong function. -/
def ccmRationalStrongClassSpaceFibreCoefficient
    (f : Class) (g : Strong) : LocallyConstant U ℂ :=
  by
    classical
    exact LocallyConstant.map (fun h : Strong => if g = h then 1 else 0) f

@[simp]
theorem ccmRationalStrongClassSpaceFibreCoefficient_apply
    (f : Class) (g : Strong) (u : U) :
    ccmRationalStrongClassSpaceFibreCoefficient f g u =
      if g = f u then 1 else 0 :=
  by
    classical
    rfl

/-- **Algebraic exhaustiveness of the LF stages.** Every literal strong
class-space function belongs to an explicit finite fibre-indicator stage. -/
theorem ccmRationalStrongClassSpaceLFStage_surjective :
    ∀ f : Class, ∃ (i : CCMRationalStrongClassSpaceLFIndex)
      (g : ccmRationalStrongClassSpaceLFStageSpace i),
        ccmRationalStrongClassSpaceLFStage i g = f := by
  intro f
  classical
  let S : Finset Strong := f.range_finite.toFinset
  let i : CCMRationalStrongClassSpaceLFIndex :=
    ⟨S, fun g => ccmRationalStrongClassSpaceFibreCoefficient f g.1⟩
  let g : ccmRationalStrongClassSpaceLFStageSpace i := fun h => h.1
  refine ⟨i, g, ?_⟩
  apply LocallyConstant.ext
  intro u
  rw [ccmRationalStrongClassSpaceLFStage_apply]
  let y : i.carrier := ⟨f u, by
    change f u ∈ S
    exact f.range_finite.mem_toFinset.mpr (Set.mem_range_self u)⟩
  rw [Fintype.sum_eq_single y]
  · change (if (y : Strong) = f u then 1 else 0) • (y : Strong) = f u
    simp [y]
  · intro b hb
    have hbne : (b : Strong) ≠ f u := by
      intro heq
      apply hb
      apply Subtype.ext
      simpa [y] using heq
    change (if (b : Strong) = f u then 1 else 0) • (b : Strong) = 0
    simp [hbne]

end GaloisForLFunctions.RHTower
