import GaloisForLFunctions.HTGeometry.MilnorTotalResidueSurjective
import GaloisForLFunctions.HTGeometry.MilnorResidueInfinity

/-!
# Milnor's norm map

Bass and Tate's norm `N_{F[X]/π ／ F}` is defined by reciprocity: lift a class of `K_n^M(F[X]/π)` to
a class of `K_{n+1}^M(F(t))` seen by no other finite place, and read minus its residue at infinity.
The lift exists by the right exactness of Milnor's sequence, and the value does not depend on it,
because two lifts differ by a class with no finite residues at all — hence by a class of constants,
which the residue at infinity kills.

* `milnorResidueInfty_eq_of_residues_eq` : the residue at infinity depends only on the finite ones.
* `milnorNormAt` : **the norm.**
* `milnorNormAt_spec` : it is computed by any admissible lift.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- **Two classes with the same finite residues have the same residue at infinity.** -/
theorem milnorResidueInfty_eq_of_residues_eq {n : ℕ} {y y' : MilnorKDeg (RatFunc F) (n + 1)}
    (h : ∀ q : MonicIrred F, milnorResidue (polyResidueData q.2.1) (n + 1) y
       = milnorResidue (polyResidueData q.2.1) (n + 1) y') :
    milnorResidueInfty n y = milnorResidueInfty n y' := by
  have hz : ∀ (π : Polynomial F) (hπ : Irreducible π), π.Monic →
      milnorResidue (polyResidueData hπ) (n + 1) (y - y') = 0 := by
    intro π hπ hm
    rw [map_sub, h ⟨π, hπ, hm⟩, sub_self]
  obtain ⟨z, hz'⟩ := mem_range_of_residues_zero (F := F) n (y - y') hz
  have hzero : milnorResidueInfty n (y - y') = 0 := by
    rw [← hz']
    exact milnorResidueInfty_const n z
  rw [map_sub] at hzero
  exact sub_eq_zero.1 hzero

/-- An admissible lift of a class of `K_n^M(F[X]/π)`. -/
theorem exists_lift_single (q : MonicIrred F) (n : ℕ)
    (x : MilnorKDeg (polyResidueField q.2.1) n) :
    ∃ y : MilnorKDeg (RatFunc F) (n + 1),
      milnorResidue (polyResidueData q.2.1) (n + 1) y = x ∧
      ∀ q' : MonicIrred F, q' ≠ q → milnorResidue (polyResidueData q'.2.1) (n + 1) y = 0 :=
  exists_residue_single n q.1.natDegree q rfl x

/-- **Milnor's norm** at a monic irreducible place. -/
noncomputable def milnorNormAt (q : MonicIrred F) (n : ℕ) :
    MilnorKDeg (polyResidueField q.2.1) n →+ MilnorKDeg F n :=
  AddMonoidHom.mk'
    (fun x => - milnorResidueInfty n (Classical.choose (exists_lift_single q n x)))
    (by
      intro a b
      have ha := Classical.choose_spec (exists_lift_single q n a)
      have hb := Classical.choose_spec (exists_lift_single q n b)
      have hab := Classical.choose_spec (exists_lift_single q n (a + b))
      have hsame : milnorResidueInfty n (Classical.choose (exists_lift_single q n (a + b)))
          = milnorResidueInfty n (Classical.choose (exists_lift_single q n a)
              + Classical.choose (exists_lift_single q n b)) := by
        refine milnorResidueInfty_eq_of_residues_eq fun q' => ?_
        by_cases hq' : q' = q
        · subst hq'
          rw [hab.1, map_add, ha.1, hb.1]
          rfl
        · rw [map_add, ha.2 q' hq', hb.2 q' hq', hab.2 q' hq', add_zero]
      rw [hsame, map_add, neg_add])

/-- **The norm is computed by any admissible lift.** -/
theorem milnorNormAt_spec (q : MonicIrred F) (n : ℕ)
    {x : MilnorKDeg (polyResidueField q.2.1) n} {y : MilnorKDeg (RatFunc F) (n + 1)}
    (h1 : milnorResidue (polyResidueData q.2.1) (n + 1) y = x)
    (h2 : ∀ q' : MonicIrred F, q' ≠ q → milnorResidue (polyResidueData q'.2.1) (n + 1) y = 0) :
    milnorNormAt q n x = - milnorResidueInfty n y := by
  have hc := Classical.choose_spec (exists_lift_single q n x)
  show - milnorResidueInfty n (Classical.choose (exists_lift_single q n x)) = _
  refine congrArg Neg.neg (milnorResidueInfty_eq_of_residues_eq fun q' => ?_)
  by_cases hq' : q' = q
  · subst hq'
    rw [hc.1, h1]
  · rw [hc.2 q' hq', h2 q' hq']

end GaloisForLFunctions.HTGeometry
