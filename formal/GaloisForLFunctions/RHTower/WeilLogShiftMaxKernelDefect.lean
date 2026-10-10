import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! The max kernel has a strictly positive rank-one defect above its nodes. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteMaxKernelForm {ι : Type*} (s : Finset ι) (p u : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, u i * u j * max (p i) (p j)

/-- Strict upper bounds turn the max kernel into a positive definite defect. -/
theorem finiteMaxKernel_defect {ι : Type*} (s : Finset ι) (p u : ι → ℝ)
    (hp : Function.Injective p) (R : ℝ) (hR : ∀ i ∈ s, p i < R) :
    0 ≤ R * (∑ i ∈ s, u i) ^ 2 - finiteMaxKernelForm s p u ∧
      (R * (∑ i ∈ s, u i) ^ 2 - finiteMaxKernelForm s p u = 0 ↔
        ∀ i ∈ s, u i = 0) := by
  classical
  induction s using Finset.induction_on_max_value p generalizing R with
  | empty => simp [finiteMaxKernelForm]
  | insert a s ha hmax ih =>
    have hstrict (i) (hi : i ∈ s) : p i < p a := by
      refine lt_of_le_of_ne (hmax i hi) ?_
      intro he
      exact ha (hp he ▸ hi)
    obtain ⟨hd, hz⟩ := ih (p a) hstrict
    have hRa : 0 < R - p a := sub_pos.mpr (hR a (Finset.mem_insert_self a s))
    have hrow : (∑ j ∈ s, u a * u j * max (p a) (p j)) =
        p a * u a * ∑ j ∈ s, u j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [max_eq_left (hmax j hj)]
      ring
    have hcol : (∑ i ∈ s, u i * u a * max (p i) (p a)) =
        p a * u a * ∑ i ∈ s, u i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [max_eq_right (hmax i hi)]
      ring
    have hq : finiteMaxKernelForm (insert a s) p u = finiteMaxKernelForm s p u +
        2 * p a * u a * (∑ i ∈ s, u i) + p a * u a ^ 2 := by
      unfold finiteMaxKernelForm
      rw [Finset.sum_insert ha]
      simp_rw [Finset.sum_insert ha]
      rw [Finset.sum_add_distrib, hrow, hcol]
      simp only [max_self]
      ring
    have hdef : R * (∑ i ∈ insert a s, u i) ^ 2 -
        finiteMaxKernelForm (insert a s) p u =
        (R - p a) * (u a + ∑ i ∈ s, u i) ^ 2 +
          (p a * (∑ i ∈ s, u i) ^ 2 - finiteMaxKernelForm s p u) := by
      rw [Finset.sum_insert ha, hq]
      ring
    rw [hdef]
    constructor
    · exact add_nonneg (mul_nonneg hRa.le (sq_nonneg _)) hd
    · constructor
      · intro he
        have hd0 : p a * (∑ i ∈ s, u i) ^ 2 - finiteMaxKernelForm s p u = 0 := by
          nlinarith [mul_nonneg hRa.le (sq_nonneg (u a + ∑ i ∈ s, u i))]
        have hs := hz.mp hd0
        have hsum : ∑ i ∈ s, u i = 0 := Finset.sum_eq_zero hs
        have hua : u a = 0 := by
          rw [hd0, hsum] at he
          have hsq : u a ^ 2 = 0 := (mul_eq_zero.mp (by simpa using he)).resolve_left
            (ne_of_gt hRa)
          exact sq_eq_zero_iff.mp hsq
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hua
        · exact hs i hi
      · intro hu
        have hs : ∀ i ∈ s, u i = 0 := fun i hi => hu i (Finset.mem_insert_of_mem hi)
        rw [hz.mpr hs, hu a (Finset.mem_insert_self a s), Finset.sum_eq_zero hs]
        ring

end RHTower
