import GaloisForLFunctions.HTGeometry.SteinbergElementaryGroup

/-!
# The central part of finite-rank `K₂`

The degree-two Milnor presentation is abelian, whereas finite-rank `K₂` need not be globally
central without a stable-range argument.  The subgroup of elements that are both in `K₂` and in the
centre of the Steinberg group is therefore the honest abelian target for a fixed finite-rank symbol
construction.

This small interface records that target.  It avoids silently treating all finite-rank `K₂` as
abelian, while retaining the exact `K₂` membership needed by the Matsumoto comparison.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The centre of any group is a commutative group. -/
instance subgroupCenterCommGroup (G : Type*) [Group G] : CommGroup (Subgroup.center G) :=
  { Subgroup.toGroup (Subgroup.center G) with
    mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 a.property b).symm) }

/-- The central finite-rank part of `K₂`, viewed as a subgroup of the centre. -/
def steinbergKTwoCenter (R : Type*) [CommRing R] (n : Type*) [DecidableEq n] [Fintype n] :
    Subgroup (Subgroup.center (SteinbergGroup R n)) :=
  (KTwo R n).comap (Subgroup.subtype (Subgroup.center (SteinbergGroup R n)))

/-- An element of the central `K₂` target is, by construction, in `K₂`. -/
theorem steinbergKTwoCenter_mem_KTwo {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]
    [Fintype n] (z : steinbergKTwoCenter R n) : ((z.1 : Subgroup.center (SteinbergGroup R n)) :
      SteinbergGroup R n) ∈ KTwo R n :=
  z.property

/-- An element of the central `K₂` target is, by construction, central. -/
theorem steinbergKTwoCenter_mem_center {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]
    [Fintype n] (z : steinbergKTwoCenter R n) :
    ((z.1 : Subgroup.center (SteinbergGroup R n)) : SteinbergGroup R n)
      ∈ Subgroup.center (SteinbergGroup R n) :=
  z.1.property

end GaloisForLFunctions.HTGeometry

end
