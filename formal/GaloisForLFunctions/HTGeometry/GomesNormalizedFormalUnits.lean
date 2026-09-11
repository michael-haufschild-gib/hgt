import GaloisForLFunctions.HTGeometry.GomesFormalSeriesExpLogInverses
import Mathlib.Algebra.Group.Units.Equiv

/-!
# The full group of normalized formal units

Constant coefficient defines a character of formal units. Its kernel consists
of all series based at one. Every based formal coordinate exponentiates to an
actual member of this group, including the zero coordinate.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The scalar coefficient character of the existing formal power-series unit group. -/
def gomesFormalAugmentationCharacter : (PowerSeries ℂ)ˣ →* ℂˣ :=
  Units.map (PowerSeries.constantCoeff : PowerSeries ℂ →+* ℂ).toMonoidHom

/-- All formal units with scalar coefficient one, as an actual subgroup. -/
def gomesNormalizedFormalUnitGroup : Subgroup (PowerSeries ℂ)ˣ :=
  gomesFormalAugmentationCharacter.ker

/-- The character kernel is exactly the group of normalized formal units. -/
theorem gomesNormalizedFormalUnitGroup_mem_iff (u : (PowerSeries ℂ)ˣ) :
    u ∈ gomesNormalizedFormalUnitGroup ↔ PowerSeries.constantCoeff u.val = 1 := by
  change gomesFormalAugmentationCharacter u = 1 ↔ PowerSeries.constantCoeff u.val = 1
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

/-- Every member of the normalized group has literal constant coefficient one. -/
theorem gomesNormalizedFormalUnitGroup_constantCoeff (u : gomesNormalizedFormalUnitGroup) :
    PowerSeries.constantCoeff u.val.val = 1 :=
  (gomesNormalizedFormalUnitGroup_mem_iff u.val).mp u.property

/-- Exponentiation of an arbitrary based formal coordinate. -/
def gomesBasedFormalExponential (G : GomesBasedFormalSeries) : PowerSeries ℂ :=
  PowerSeries.subst G.val (PowerSeries.exp ℂ)

/-- Every based formal exponential is normalized, with no convergence assumptions. -/
theorem gomesBasedFormalExponential_constantCoeff (G : GomesBasedFormalSeries) :
    PowerSeries.constantCoeff (gomesBasedFormalExponential G) = 1 := by
  have hg := gomesBasedFormalSeries_hasSubst G
  have h1 : PowerSeries.subst G.val (1 : PowerSeries ℂ) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
    simp
  have hzero : PowerSeries.constantCoeff (PowerSeries.subst G.val (PowerSeries.exp ℂ - 1)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (gomesBasedFormalSeries_constantCoeff G)
      (PowerSeries.exp ℂ - 1) (by simp [PowerSeries.constantCoeff_exp])
  rw [PowerSeries.subst_sub hg, h1, map_sub, map_one] at hzero
  exact sub_eq_zero.mp hzero

/-- The formal exponential is always an actual unit. -/
theorem gomesBasedFormalExponential_isUnit (G : GomesBasedFormalSeries) :
    IsUnit (gomesBasedFormalExponential G) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, gomesBasedFormalExponential_constantCoeff]
  exact isUnit_one

/-- The exponential as an actual normalized formal unit. -/
def gomesBasedFormalExponentialUnit (G : GomesBasedFormalSeries) : gomesNormalizedFormalUnitGroup :=
  ⟨(gomesBasedFormalExponential_isUnit G).unit, by
    rw [gomesNormalizedFormalUnitGroup_mem_iff, IsUnit.unit_spec]
    exact gomesBasedFormalExponential_constantCoeff G⟩

/-- The packaged exponential unit retains the literal substituted formal exponential. -/
theorem gomesBasedFormalExponentialUnit_val (G : GomesBasedFormalSeries) :
    (gomesBasedFormalExponentialUnit G).val.val = gomesBasedFormalExponential G :=
  (gomesBasedFormalExponential_isUnit G).unit_spec

/-- Every normalized formal unit has a canonical based increment. -/
def gomesNormalizedFormalUnitIncrement (u : gomesNormalizedFormalUnitGroup) : GomesBasedFormalSeries :=
  ⟨u.val.val - 1, by
    change PowerSeries.constantCoeff (u.val.val - 1) = 0
    rw [map_sub, map_one, gomesNormalizedFormalUnitGroup_constantCoeff, sub_self]⟩

/-- Adding back one recovers the whole normalized formal unit. -/
theorem gomesNormalizedFormalUnit_one_add_increment (u : gomesNormalizedFormalUnitGroup) :
    1 + (gomesNormalizedFormalUnitIncrement u).val = u.val.val := by
  change 1 + (u.val.val - 1) = u.val.val
  ring

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
