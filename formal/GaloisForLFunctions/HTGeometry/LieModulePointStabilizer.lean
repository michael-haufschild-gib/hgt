import Mathlib.Algebra.Lie.Subalgebra

/-!
# The point stabiliser of a Lie module

For a Lie algebra `L` over `R` acting on a module `M`, the elements annihilating a fixed vector
`v : M` form a Lie subalgebra of `L`.  Closure under addition and scalars is bilinearity of the
action in its left argument; closure under brackets is the Leibniz rule `⁅⁅A, B⁆, v⁆ =
⁅A, ⁅B, v⁆⁆ - ⁅B, ⁅A, v⁆⁆`, both of whose terms vanish when `A` and `B` annihilate `v`.

The construction depends on nothing about `L` beyond its Lie-module structure, so the current-mode
stabilisers used in the projective-horizon files are instances of the single law below.
-/

namespace HTGeometry

variable (R L : Type*) {M : Type*}
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The annihilator of a vector is a Lie subalgebra.**  The elements of `L` sending `v` to zero
are closed under addition, scalars and brackets. -/
def lieModulePointStabilizer (v : M) : LieSubalgebra R L where
  carrier := {A | ⁅A, v⁆ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change ⁅A, v⁆ = 0 at hA
    change ⁅B, v⁆ = 0 at hB
    change ⁅A + B, v⁆ = 0
    simp [hA, hB]
  smul_mem' := by
    intro c A hA
    change ⁅A, v⁆ = 0 at hA
    change ⁅c • A, v⁆ = 0
    simp [hA]
  lie_mem' := by
    intro A B hA hB
    change ⁅A, v⁆ = 0 at hA
    change ⁅B, v⁆ = 0 at hB
    change ⁅⁅A, B⁆, v⁆ = 0
    rw [lie_lie, hA, hB]
    simp

@[simp] theorem mem_lieModulePointStabilizer {v : M} {A : L} :
    A ∈ lieModulePointStabilizer R L v ↔ ⁅A, v⁆ = 0 := Iff.rfl

end HTGeometry
