import GaloisForLFunctions.RHTower.CCMRationalAdelicCyclicRestrictionFormula
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleHaar

/-!
# Canonical positive-real section of the rational idele class space

For `ℚ`, the standard idele-class section is

`Δ_ℚ = Ẑˣ × ℝ₊ˣ`.

Here `Ẑˣ` is represented inside the actual finite ideles by requiring both a unit and its
inverse to be integral at every finite place.  The second factor is the unit group of the
nonnegative reals; being a unit makes its real value strictly positive.  No abstract label type
or arbitrary base parameter replaces the rational class-space section.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Integral finite ideles with integral inverse, the actual embedded copy of `Ẑˣ`. -/
def ccmRationalProfiniteUnitSubgroup :
    Subgroup CCMRationalFiniteAdeleˣ where
  carrier := {u |
    (u : CCMRationalFiniteAdele) ∈ ccmRationalIntegralFiniteAdeles ∧
    ((u⁻¹ : CCMRationalFiniteAdeleˣ) : CCMRationalFiniteAdele) ∈
      ccmRationalIntegralFiniteAdeles}
  one_mem' := by
    constructor <;> intro v <;> exact one_mem _
  mul_mem' := by
    intro u v hu hv
    constructor
    · intro w
      exact mul_mem (hu.1 w) (hv.1 w)
    · intro w
      rw [mul_inv_rev]
      exact mul_mem (hv.2 w) (hu.2 w)
  inv_mem' := by
    intro u hu
    constructor
    · exact hu.2
    · simpa using hu.1

/-- Actual profinite-unit factor `Ẑˣ` in the rational class-space section. -/
abbrev CCMRationalProfiniteUnit := ccmRationalProfiniteUnitSubgroup

/-- Canonical rational idele-class section `Ẑˣ × ℝ₊ˣ`. -/
abbrev CCMRationalClassSpaceSection :=
  CCMRationalProfiniteUnit × Units NNReal

/-- Its canonical point in the genuine adelic Morita-base parameter space. -/
def ccmRationalClassSpaceSectionMoritaBase
    (b : CCMRationalClassSpaceSection) :
    CCMRationalAdelicMoritaBase where
  bInf := (b.2.val : NNReal)
  bInf_ne_zero := by
    exact_mod_cast b.2.ne_zero
  bFin := b.1.val

/-- Topology on genuine Morita bases induced by real and finite-idele coordinates. -/
noncomputable instance ccmRationalAdelicMoritaBaseTopologicalSpace :
    TopologicalSpace CCMRationalAdelicMoritaBase :=
  TopologicalSpace.induced (fun b => (b.bInf, b.bFin)) inferInstance

/-- The canonical rational section is continuous in the genuine Morita-base topology. -/
theorem ccmRationalClassSpaceSectionMoritaBase_continuous :
    Continuous ccmRationalClassSpaceSectionMoritaBase := by
  rw [continuous_induced_rng]
  change Continuous (fun b : CCMRationalClassSpaceSection =>
    (((b.2.val : NNReal) : ℝ), b.1.val))
  fun_prop

/-- Module character on the rational class-space section: its positive real coordinate. -/
def ccmRationalClassSpaceModule
    (b : CCMRationalClassSpaceSection) : ℝ :=
  (b.2.val : NNReal)

theorem ccmRationalClassSpaceModule_pos
    (b : CCMRationalClassSpaceSection) :
    0 < ccmRationalClassSpaceModule b := by
  change 0 < ((b.2.val : NNReal) : ℝ)
  exact_mod_cast (pos_iff_ne_zero.mpr b.2.ne_zero : 0 < b.2.val)

@[simp]
theorem ccmRationalClassSpaceModule_one :
    ccmRationalClassSpaceModule 1 = 1 :=
  rfl

@[simp]
theorem ccmRationalClassSpaceModule_mul
    (b c : CCMRationalClassSpaceSection) :
    ccmRationalClassSpaceModule (b * c) =
      ccmRationalClassSpaceModule b * ccmRationalClassSpaceModule c := by
  rfl

theorem ccmRationalClassSpaceModule_continuous :
    Continuous ccmRationalClassSpaceModule := by
  unfold ccmRationalClassSpaceModule
  fun_prop

end RHTower
end GaloisForLFunctions
