import Mathlib

/-!
# Functionals annihilating the finitely supported mean-zero directions are constant

Testing against the two-point direction `δ_p − δ_q` shows that a coefficient sequence whose
functional kills every finitely supported mean-zero vector takes the same value at every index.
This is the finite-support control block behind the moment-fibre probe.
-/

namespace GaloisForLFunctions.HTGeometry

open Finsupp

variable {ι : Type*} [DecidableEq ι]

/-- **Finite-support mean-zero control.**  A coefficient sequence whose functional annihilates every
finitely supported mean-zero direction is constant. -/
theorem eq_of_annihilates_meanZero {F : ι → ℝ}
    (h : ∀ w : ι →₀ ℝ, (w.sum fun _ x => x) = 0 → (w.sum fun n x => F n * x) = 0)
    (p q : ι) : F p = F q := by
  classical
  by_cases hpq : p = q
  · rw [hpq]
  set w : ι →₀ ℝ := Finsupp.single p (1 : ℝ) - Finsupp.single q (1 : ℝ) with hw
  have hmean : (w.sum fun _ x => x) = 0 := by
    rw [hw, Finsupp.sum_sub_index (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Finsupp.sum_single_index rfl, sub_self]
  have hval := h w hmean
  rw [hw, Finsupp.sum_sub_index (fun a b₁ b₂ => by ring), Finsupp.sum_single_index (by ring),
    Finsupp.sum_single_index (by ring), mul_one, mul_one, sub_eq_zero] at hval
  exact hval

end GaloisForLFunctions.HTGeometry
