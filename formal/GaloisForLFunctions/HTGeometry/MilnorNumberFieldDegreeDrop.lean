import GaloisForLFunctions.HTGeometry.MilnorSimpleExtensionTorsion
import GaloisForLFunctions.HTGeometry.MilnorKTateEuclid

/-!
# The Milnor `K`-theory of a number field is torsion above its degree

Tate's computation makes `K_j^M(ℚ)` torsion for every `j ≥ 2`, and Bass and Tate's degree drop
carries that to a finite extension at the cost of its degree minus one.

* `milnorKDeg_rat_torsion` : **`K_j^M(ℚ)` is torsion for `j ≥ 2`.**
* `milnorKDeg_numberField_torsion` : **`K_m^M(F)` is torsion for `m ≥ [F : ℚ] + 1`.**
-/

namespace GaloisForLFunctions.HTGeometry

/-- **`K_j^M(ℚ)` is torsion in every degree at least two.** -/
theorem milnorKDeg_rat_torsion (j : ℕ) (hj : 2 ≤ j) (x : MilnorKDeg ℚ j) :
    x ∈ torsionAddSubgroup (MilnorKDeg ℚ j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = 2 + k := ⟨j - 2, by omega⟩
  exact milnorKDeg_mem_torsion_of_two ℚ milnorKDegTwo_rat_torsion k x

/-- **The Milnor `K`-theory of a number field is torsion above its degree.**  For a finite
extension `F/ℚ` of degree `d`, every class of `K_m^M(F)` with `m ≥ d + 1` is torsion.

This is unconditional: it uses only Tate's computation over `ℚ` and Bass and Tate's generators for a
simple extension.  In particular it needs no input about the tame kernel of `F`. -/
theorem milnorKDeg_numberField_torsion {F : Type*} [Field F] [Algebra ℚ F]
    [FiniteDimensional ℚ F] (m : ℕ) (hm : Module.finrank ℚ F + 1 ≤ m) (x : MilnorKDeg F m) :
    x ∈ torsionAddSubgroup (MilnorKDeg F m) := by
  refine milnorKDeg_torsion_of_finite_separable (F := ℚ) (E := F) (n₀ := 2)
    (fun j hj x => milnorKDeg_rat_torsion j hj x) m ?_ x
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  omega

/-- **The degree drop along a tower.**  Each step of a tower of number fields costs only its own
degree minus one, so a field with subfields is reached in far lower degree than its own degree
suggests. -/
theorem milnorKDeg_torsion_tower {E L : Type*} [Field E] [Field L]
    [Algebra ℚ E] [Algebra ℚ L] [Algebra E L] [IsScalarTower ℚ E L]
    [FiniteDimensional ℚ E] [FiniteDimensional E L]
    (m : ℕ) (hm : 2 + (Module.finrank ℚ E - 1) + (Module.finrank E L - 1) ≤ m)
    (x : MilnorKDeg L m) : x ∈ torsionAddSubgroup (MilnorKDeg L m) := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ E).injective
  have hE : ∀ j, 2 + (Module.finrank ℚ E - 1) ≤ j →
      ∀ y : MilnorKDeg E j, y ∈ torsionAddSubgroup (MilnorKDeg E j) :=
    fun j hj y => milnorKDeg_torsion_of_finite_separable (F := ℚ) (E := E) (n₀ := 2)
      (fun i hi z => milnorKDeg_rat_torsion i hi z) j hj y
  exact milnorKDeg_torsion_of_finite_separable (F := E) (E := L)
    (n₀ := 2 + (Module.finrank ℚ E - 1)) hE m (by omega) x

end GaloisForLFunctions.HTGeometry
