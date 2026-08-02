import GaloisForLFunctions.RHTower.DeningerTowerTransition

/-!
# Every level of the tower embeds in the next

The local degree of a place over its restriction is positive, and every place of the base is the
restriction of a place of the extension — otherwise the fibre sum of the local degrees would be
zero instead of `[L : K]`.  Hence the transition map of the tower is injective: no test function
is lost when the field of definition grows, so every level of the tower embeds into the direct
limit.

* `deningerPlaceDegreeOver_pos` : the local degrees are positive.
* `deningerPlaceRestrict_surjective` : **every place of the base comes from the extension.**
* `deningerTowerPull_injective` : **the transition maps are injective.**
-/

namespace RHTower

open NumberField NumberField.InfinitePlace Module

section Positivity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem deningerArchDegreeOver_pos (w : InfinitePlace L) :
    0 < deningerArchDegreeOver (K := K) w :=
  Nat.div_pos (mult_comap_le _ _) mult_pos

theorem deningerFiniteDegreeOver_pos (w : FinitePlace L) :
    0 < deningerFiniteDegreeOver (K := K) w :=
  Nat.pos_of_ne_zero (deningerLocalDegree_ne_zero (K := K) w)

end Positivity

section Surjective

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem deningerPlaceDegreeOver_pos (w : DeningerPlace L) :
    0 < deningerPlaceDegreeOver K L w := by
  cases w with
  | inl w => exact deningerArchDegreeOver_pos w
  | inr w => exact deningerFiniteDegreeOver_pos w

theorem deningerRelativeFinrank_pos : 0 < finrank K L := by
  have htower : finrank ℚ K * finrank K L = finrank ℚ L := finrank_mul_finrank ℚ K L
  have hLpos : 0 < finrank ℚ L := Module.finrank_pos
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [h, Nat.mul_zero] at htower
  omega

/-- **Every place of the base is the restriction of a place of the extension.**  If the fibre over
a place were empty, the fibre sum of the local degrees would be zero, but it is `[L : K]`. -/
theorem deningerPlaceRestrict_surjective :
    Function.Surjective (deningerPlaceRestrict K L) := by
  classical
  intro v
  by_contra hcon
  push Not at hcon
  have hempty : deningerPlaceRestrict K L ⁻¹' {v} = (∅ : Set (DeningerPlace L)) := by
    ext w
    constructor
    · intro hw
      exact absurd hw (hcon w)
    · intro hw
      exact absurd hw (Set.notMem_empty w)
  have hsum := deningerPlaceDegree_fibre_sum K L v
  rw [hempty, finsum_mem_empty] at hsum
  have hpos : 0 < finrank K L := deningerRelativeFinrank_pos K L
  have hne : (0 : ℝ) ≠ (finrank K L : ℝ) :=
    ne_of_lt ((Nat.cast_pos (α := ℝ)).mpr hpos)
  exact hne hsum

/-- **The transition map of the tower is injective**: every level embeds into the next. -/
theorem deningerTowerPull_injective :
    Function.Injective (deningerTowerPull K L) := by
  intro f g hfg
  refine Subtype.ext (funext fun v => ?_)
  obtain ⟨w, rfl⟩ := deningerPlaceRestrict_surjective K L v
  have hval := congrArg (fun h : DeningerTestSpace (DeningerPlace L) =>
    (h : DeningerPlace L → ℝ) w) hfg
  have hdeg : (deningerPlaceDegreeOver K L w : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (deningerPlaceDegreeOver_pos K L w).ne'
  have hval' : (deningerPlaceDegreeOver K L w : ℝ)
      * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w)
    = (deningerPlaceDegreeOver K L w : ℝ)
      * (g : DeningerPlace K → ℝ) (deningerPlaceRestrict K L w) := hval
  exact mul_left_cancel₀ hdeg hval'

end Surjective

end RHTower
