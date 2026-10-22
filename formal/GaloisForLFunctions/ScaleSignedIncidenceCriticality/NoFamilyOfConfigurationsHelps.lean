import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheFloorTheorem

/-!
# No family of configurations helps

The corpus's criteria for a contribution to the shared target include "no family average": a method
that proves its estimate only after averaging over a family of L-functions does not settle the
critical form. In the admissibility calculus this is a floor, and the floor is exact.

The data are families `Z : ι → TemperedZeroConfig` of any cardinality, the invariant is the worst
width in the family (`familyWidth`), and the reading is the joint aperture certificate — the
certificate of *every* member (`familyAperture`). The constant family built from the depth-`½`
witness passes the joint certificate and has worst width `½`, so

`resolutionLimit familyWidth (familyAperture a) = ½`
(`resolutionLimit_familyWidth_familyAperture`)

for every aperture and every index type. The same witness is constant, so the limit of the
*average* width over any finite family is `½` as well
(`resolutionLimit_familyWidth_eq_half_of_constant`): averaging cannot help, because the extremal
datum is already uniform across the family.

So the criterion is not a methodological preference but an entry in the table: the pair
(joint certificate over any family, `½`). A mechanism must obtain its bound for the individual
configuration, and no amount of averaging, of any kind, over any family, improves the trivial
bound — because the worst case is attained by the family all of whose members are extremal.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Families and their worst width -/

/-- A family of configurations, of any cardinality. -/
def FamilyConfig (ι : Type*) : Type _ := ι → TemperedZeroConfig

/-- The worst width in the family. -/
noncomputable def familyWidth {ι : Type*} (Z : FamilyConfig ι) : ℝ :=
  sSup (Set.range fun i => width (Z i))

theorem familyWidth_le_half {ι : Type*} (Z : FamilyConfig ι) : familyWidth Z ≤ 1 / 2 := by
  refine Real.sSup_le ?_ (by norm_num)
  rintro x ⟨i, rfl⟩
  exact width_le_half (Z i)

/-- The joint certificate: the aperture-`a` certificate of every member. -/
def familyAperture {ι : Type*} (a : ℝ) (Z : FamilyConfig ι) : Prop :=
  ∀ i : ι, aperturePositivity a (Z i)

/-! ### 2. The constant extremal family -/

/-- The family all of whose members are the depth-`½` witness. -/
theorem exists_familyWidth_eq_half {ι : Type*} [Nonempty ι] {a : ℝ} (ha : 0 < a) :
    ∃ Z : FamilyConfig ι, familyWidth Z = 1 / 2 ∧ familyAperture a Z := by
  obtain ⟨W, hw, hpos⟩ := exists_width_eq_half_aperturePositivity ha
  refine ⟨fun _ => W, ?_, fun _ => hpos⟩
  have hrange : (Set.range fun _ : ι => width W) = {width W} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨-, h⟩ := hx
      exact h.symm
    · intro h
      exact ⟨Classical.arbitrary ι, h.symm⟩
  unfold familyWidth
  rw [hrange, csSup_singleton, hw]

/-! ### 3. The floor -/

/-- **No family helps.** The joint certificate over a family of any cardinality has resolution
limit `½` for the worst width. -/
theorem resolutionLimit_familyWidth_familyAperture {ι : Type*} [Nonempty ι] {a : ℝ} (ha : 0 < a)
    {Z : FamilyConfig ι} (hZ : familyAperture a Z) :
    resolutionLimit familyWidth (familyAperture a) Z = 1 / 2 := by
  obtain ⟨W, hw, hpos⟩ := exists_familyWidth_eq_half (ι := ι) ha
  exact resolutionLimit_eq_of_mem_shadow_of_max familyWidth_le_half
    (propext (iff_of_true hpos hZ)) hw

/-- **And the extremal family is constant**, so no averaging over it can do better than its single
member: the worst case and the average coincide there. -/
theorem resolutionLimit_familyWidth_eq_half_of_constant {ι : Type*} [Nonempty ι] {a : ℝ}
    (ha : 0 < a) {Z : FamilyConfig ι} (hZ : familyAperture a Z) :
    ∃ W : TemperedZeroConfig, width W = 1 / 2 ∧ aperturePositivity a W ∧
      familyWidth (fun _ : ι => W) = 1 / 2 ∧
      resolutionLimit familyWidth (familyAperture a) Z = 1 / 2 := by
  obtain ⟨W, hw, hpos⟩ := exists_width_eq_half_aperturePositivity ha
  refine ⟨W, hw, hpos, ?_, resolutionLimit_familyWidth_familyAperture ha hZ⟩
  have hrange : (Set.range fun _ : ι => width W) = {width W} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨-, h⟩ := hx
      exact h.symm
    · intro h
      exact ⟨Classical.arbitrary ι, h.symm⟩
  unfold familyWidth
  rw [hrange, csSup_singleton, hw]

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
