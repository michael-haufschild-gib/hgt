import GaloisForLFunctions.HTGeometry.SteinbergFinFourUpperNormalForm
import GaloisForLFunctions.HTGeometry.SteinbergUpperKernelNormalForm

/-!
# The rank-four upper Steinberg subgroup meets `K₂` trivially

Over a field `F`, every element of the upper Steinberg subgroup of `St(4, F)` has the tetrahedron
normal form, and a tetrahedron element lies in `K₂` only if all its coordinates vanish. Hence the
upper unipotent subgroup injects into `GL_4(F)`.

## Main results

- `upperSteinbergSubgroup_fin4_inter_KTwo_eq_bot`: the intersection of the upper Steinberg
  subgroup of `St(4, F)` with `K₂(4, F)` is trivial.

## Hypotheses

Unconditional.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- Over a field, the upper Steinberg subgroup of `St(4, F)` intersects `K₂` trivially. -/
theorem upperSteinbergSubgroup_fin4_inter_KTwo_eq_bot :
    upperSteinbergSubgroup (F := F) (Fin 4) ⊓ KTwo F (Fin 4) = ⊥ := by
  apply bot_unique
  rintro x ⟨hxupper, hxKTwo⟩
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at hxupper
  rcases hxupper with ⟨a, b, c, d, e, f, hx⟩
  have hcoordinates :
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 :=
    steinbergUpperTetrahedron_mem_KTwo_iff
      (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3)
      a b c d e f |>.mp (by rw [← hx]; exact hxKTwo)
  rcases hcoordinates with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hx]
  simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
    steinbergX_zero, mul_one]
  exact Subgroup.one_mem _

end GaloisForLFunctions.HTGeometry
