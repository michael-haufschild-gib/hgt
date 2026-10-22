import GaloisForLFunctions.RHTower.CCM.CCMRationalClassSpaceSection
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Compactness of the rational profinite-unit factor

The integral finite adeles form a compact multiplicative submonoid.  Its unit
submonoid consists exactly of finite ideles whose value and inverse are both
integral, i.e. the literal `Ẑˣ` used in the rational class-space section.
Closed embedding of units into the product with their inverses then gives the
missing compactness instance.
-/

noncomputable section

open Set Topology

namespace GaloisForLFunctions.RHTower

/-- Compact multiplicative submonoid of integral rational finite adeles. -/
def ccmRationalIntegralFiniteAdelesSubmonoid :
    Submonoid CCMRationalFiniteAdele where
  carrier := ccmRationalIntegralFiniteAdeles
  one_mem' := by
    intro v
    exact one_mem _
  mul_mem' := by
    intro x y hx hy v
    exact mul_mem (hx v) (hy v)

theorem ccmRationalProfiniteUnitSubgroup_eq_integralUnits :
    (ccmRationalProfiniteUnitSubgroup : Set CCMRationalFiniteAdeleˣ) =
      (ccmRationalIntegralFiniteAdelesSubmonoid.units :
        Set CCMRationalFiniteAdeleˣ) := by
  ext u
  rfl

/-- The literal rational profinite-unit factor `Ẑˣ` is compact. -/
noncomputable instance ccmRationalProfiniteUnitCompactSpace :
    CompactSpace CCMRationalProfiniteUnit where
  isCompact_univ := by
    have hUnits : IsCompact
        (ccmRationalIntegralFiniteAdelesSubmonoid.units :
          Set CCMRationalFiniteAdeleˣ) :=
      Submonoid.units_isCompact ccmRationalIntegralFiniteAdeles_isCompact
    have hCarrier : IsCompact
        (ccmRationalProfiniteUnitSubgroup : Set CCMRationalFiniteAdeleˣ) := by
      rw [ccmRationalProfiniteUnitSubgroup_eq_integralUnits]
      exact hUnits
    exact isCompact_iff_isCompact_univ.mp hCarrier

end GaloisForLFunctions.RHTower
