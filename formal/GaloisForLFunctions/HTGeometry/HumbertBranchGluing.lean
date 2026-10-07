import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The finite gluing group of five four-branched double covers

An even-degree edge subset of the complete graph on five vertices is determined by
its six edges not incident with vertex zero. At each vertex its four incident bits
form an even vector; quotienting by the constant vector leaves two branch-difference
coordinates. The resulting gluing group has 32 elements and intersects every single
local factor trivially.

This module proves the exact linear algebra of this gluing presentation. Identifying
the presentation with the normalization sequence of an admissible curve cover is a
separate geometric statement.
-/

namespace HTGeometry.HumbertBranchGluing

abbrev Bit := ZMod 2
abbrev Cycles := Fin 6 → Bit
abbrev LocalClasses := Fin 5 → Bit × Bit

/-- Coordinates are the edges `12,13,14,23,24,34`; the four remaining edges are
their incident sums. Each output pair records two differences in a four-branch row. -/
def gluing : Cycles →ₗ[Bit] LocalClasses where
  toFun v := ![
    (v 1+v 2+v 3+v 4, v 0+v 2+v 3+v 5),
    (v 1+v 2, v 0+v 2),
    (v 3+v 4, v 0+v 4),
    (v 3+v 5, v 1+v 5),
    (v 4+v 5, v 2+v 5)]
  map_add' v w := by
    ext i <;> fin_cases i <;> simp <;> ring
  map_smul' a v := by
    ext i <;> fin_cases i <;> simp <;> ring

/-- The only cycles invisible in every local branch quotient are the empty
and full edge subsets. -/
theorem gluing_eq_zero_iff (v : Cycles) :
    gluing v = 0 ↔ ∀ i, v i = v 5 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [gluing, CharTwo.add_eq_zero] at h₁ h₂ h₃
    intro i
    fin_cases i
    · exact h₁.2.trans (h₁.1.symm.trans h₃.2)
    · exact h₃.2
    · exact h₁.1.symm.trans h₃.2
    · exact h₃.1
    · exact h₂.1.symm.trans h₃.1
    · rfl
  · intro h
    have hv : v = fun _ => v 5 := funext h
    rw [hv]
    ext i <;> fin_cases i <;> simp [gluing, CharTwo.add_self_eq_zero]

/-- Subtracting the last edge bit fixes the unique representative whose last bit is zero. -/
def normalize : Cycles →ₗ[Bit] (Fin 5 → Bit) where
  toFun v i := v i.castSucc + v 5
  map_add' v w := by ext i; simp; ring
  map_smul' a v := by ext i; simp; ring

theorem normalize_eq_zero_iff (v : Cycles) :
    normalize v = 0 ↔ ∀ i, v i = v 5 := by
  constructor
  · intro h
    have hv (i : Fin 5) : v i.castSucc = v 5 :=
      CharTwo.add_eq_zero.mp (congrFun h i)
    intro i
    fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
    · exact hv 4
    · rfl
  · intro h
    ext i
    change v i.castSucc + v 5 = 0
    rw [h, CharTwo.add_self_eq_zero]

theorem normalize_surjective : Function.Surjective normalize := by
  intro v
  refine ⟨![v 0, v 1, v 2, v 3, v 4, 0], ?_⟩
  ext i
  fin_cases i <;> simp [normalize]

theorem gluing_ker_eq_normalize_ker : gluing.ker = normalize.ker := by
  ext v
  simp only [LinearMap.mem_ker, gluing_eq_zero_iff, normalize_eq_zero_iff]

/-- An explicit five-dimensional presentation of the gluing group. -/
noncomputable def gluingRangeEquiv : gluing.range ≃ₗ[Bit] (Fin 5 → Bit) :=
  gluing.quotKerEquivRange.symm |>.trans
    ((Submodule.quotEquivOfEq _ _ gluing_ker_eq_normalize_ker).trans
      (normalize.quotKerEquivOfSurjective normalize_surjective))

theorem gluing_range_card : Nat.card gluing.range = 32 := by
  rw [Nat.card_congr gluingRangeEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- No nonzero gluing class is supported in a single local factor. -/
theorem no_single_channel (v : Cycles) (i : Fin 5)
    (h : ∀ j, j ≠ i → gluing v j = 0) : gluing v = 0 := by
  apply (gluing_eq_zero_iff v).2
  fin_cases i
  · have h₁ := h 1 (by decide)
    have h₂ := h 2 (by decide)
    have h₃ := h 3 (by decide)
    simp [gluing, CharTwo.add_eq_zero] at h₁ h₂ h₃
    intro j
    fin_cases j <;> simp_all
  · have h₂ := h 2 (by decide)
    have h₃ := h 3 (by decide)
    have h₄ := h 4 (by decide)
    simp [gluing, CharTwo.add_eq_zero] at h₂ h₃ h₄
    intro j
    fin_cases j <;> simp_all
  · have h₁ := h 1 (by decide)
    have h₃ := h 3 (by decide)
    have h₄ := h 4 (by decide)
    simp [gluing, CharTwo.add_eq_zero] at h₁ h₃ h₄
    intro j
    fin_cases j <;> simp_all
  · have h₁ := h 1 (by decide)
    have h₂ := h 2 (by decide)
    have h₄ := h 4 (by decide)
    simp [gluing, CharTwo.add_eq_zero] at h₁ h₂ h₄
    intro j
    fin_cases j <;> simp_all
  · have h₁ := h 1 (by decide)
    have h₂ := h 2 (by decide)
    have h₃ := h 3 (by decide)
    simp [gluing, CharTwo.add_eq_zero] at h₁ h₂ h₃
    intro j
    fin_cases j <;> simp_all

end HTGeometry.HumbertBranchGluing
