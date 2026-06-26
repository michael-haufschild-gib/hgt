/-
# Discrete primitive of a closed cyclic cocycle (hDisc lift, loop-closure core)

The genuine bottleneck of the dyadic-cover lift `hliftF`/`hliftG` is the **loop closure**: around the
cover annulus the local Böttcher branches `β i` differ on consecutive overlaps by unit constants `u i`
(`β i = u i · β (i+1)`), and the multiplicative cocycle `u` closes up (`∏ u = exp(2πi) = 1`,
`CoverConstruction.no_singlevalued_branch_of_dyadic_period`). H¹-vanishing on the circle: a closed cyclic
cocycle is a coboundary, i.e. there is `c` with `c(i+1) = c(i)·u(i)`. Then the adjusted branches
`β̃ i = c i · β i` agree on consecutive overlaps, and `SheafGlue.analyticOnNhd_glue_finite` produces the
global single-valued lift. This file proves the algebraic heart — the discrete primitive — independent of
the analysis.
-/
import Mathlib

open Finset

namespace Bottcher

/-- **Period closure: integer period ⟹ unit cocycle product.** If the imaginary jumps `a i` of the
green-conjugate cocycle sum to an integer multiple of `2πi` around the loop, the multiplicative cocycle
`u i = exp(a i)` closes: `∏ exp(a i) = 1`. This is the bridge from the ANALYTIC period — `∑ a i = k·2πi`,
the output of `LiftPeriod.fractional_period_of_lift` / `LiftExists.multiplier_eq_exp_of_period` summed
over the `2ⁿ`-fold cover loop (where `ζ = exp(2πi/2ⁿ)` raised to `2ⁿ` is `exp(2πi)`) — to the `∏ u = 1`
hypothesis of `LoopGlue.exists_bottcherLift_of_cyclic_greenConjugate`. -/
theorem prod_exp_eq_one_of_sum_eq_int_two_pi_I {ι : Type*} (s : Finset ι) (a : ι → ℂ) (k : ℤ)
    (h : ∑ i ∈ s, a i = (k : ℂ) * (2 * Real.pi * Complex.I)) :
    ∏ i ∈ s, Complex.exp (a i) = 1 := by
  rw [← Complex.exp_sum, h, Complex.exp_int_mul_two_pi_mul_I]

/-- **Discrete primitive of a closed cyclic cocycle (H¹-vanishing on the circle).** For a cyclic cocycle
`u : Fin (n+1) → ℂ` (nonzero entries) with `∏ u = 1`, there is `c` with `c(i+1) = c(i)·u(i)` for ALL `i` —
including the wrap `i = last → 0`, where `∏ u = 1` is exactly what closes it (`c 0 =` empty product `= 1`,
`c(last)·u(last) = ∏ u = 1`). Take `c i = ∏_{j.val < i.val} u j`. The trivialization turning the
multiplicative branch-cocycle of the cover annulus into pairwise-agreeing branches (`β̃ i = c i · β i`),
which `SheafGlue.analyticOnNhd_glue_finite` then glues into the global single-valued lift. -/
theorem exists_cocycle_primitive {n : ℕ} (u : Fin (n + 1) → ℂ) (hu : ∀ i, u i ≠ 0)
    (hprod : ∏ i, u i = 1) :
    ∃ c : Fin (n + 1) → ℂ, (∀ i, c i ≠ 0) ∧ (∀ i : Fin (n + 1), c (i + 1) = c i * u i) ∧
      (∀ i, ‖c i‖ = ∏ j ∈ univ.filter (fun j : Fin (n + 1) => j.val < i.val), ‖u j‖) := by
  classical
  refine ⟨fun i => ∏ j ∈ univ.filter (fun j : Fin (n + 1) => j.val < i.val), u j, ?_, ?_,
    fun i => by rw [norm_prod]⟩
  · intro i; exact Finset.prod_ne_zero_iff.mpr (fun j _ => hu j)
  · intro i
    by_cases hlast : i = Fin.last n
    · subst hlast
      have h0 : (Fin.last n + 1) = 0 := by ext; simp [Fin.val_add_one, Fin.val_last]
      show (∏ j ∈ univ.filter (fun j : Fin (n + 1) => j.val < (Fin.last n + 1).val), u j)
          = (∏ j ∈ univ.filter (fun j : Fin (n + 1) => j.val < (Fin.last n).val), u j) * u (Fin.last n)
      rw [h0]
      have hc0 : univ.filter (fun j : Fin (n + 1) => j.val < (0 : Fin (n + 1)).val) = ∅ := by
        ext j; simp [Fin.val_zero]
      have hclast : univ.filter (fun j : Fin (n + 1) => j.val < (Fin.last n).val)
          = univ.erase (Fin.last n) := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_erase, Fin.val_last]
        constructor
        · intro hj; refine ⟨?_, trivial⟩; intro h; subst h; rw [Fin.val_last] at hj; omega
        · intro ⟨hj, _⟩
          have hjlt := j.isLt
          rcases Nat.lt_or_ge j.val n with h | h
          · exact h
          · exact absurd (Fin.ext (by rw [Fin.val_last]; omega)) hj
      rw [hc0, hclast, Finset.prod_empty]
      rw [mul_comm, Finset.mul_prod_erase univ u (mem_univ _), hprod]
    · have hval : (i + 1).val = i.val + 1 := by rw [Fin.val_add_one, if_neg hlast]
      show (∏ j ∈ univ.filter (fun j : Fin (n + 1) => j.val < (i + 1).val), u j)
          = (∏ j ∈ univ.filter (fun j : Fin (n + 1) => j.val < i.val), u j) * u i
      have hsplit : univ.filter (fun j : Fin (n + 1) => j.val < (i + 1).val)
          = insert i (univ.filter (fun j : Fin (n + 1) => j.val < i.val)) := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_insert, hval]
        constructor
        · intro hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (rfl | hj)
          · omega
          · omega
      rw [hsplit, Finset.prod_insert (by simp)]
      ring

end Bottcher
