import Mathlib

open Polynomial
open scoped Classical

namespace GaloisForLFunctions.RHTower

/-- A finite algebraic family is covered away from zero by one integer polynomial whose constant
coefficient is nonzero. This is the exact root packet required by Hermite's analytic estimate. -/
theorem exists_integer_polynomial_cover_of_finite_algebraic
    {ι : Type*} [Fintype ι] (E : ι → ℂ) (hE : ∀ i, IsAlgebraic ℤ (E i)) :
    ∃ g : ℤ[X], g.eval 0 ≠ 0 ∧ ∀ i, E i ≠ 0 → E i ∈ g.aroots ℂ := by
  classical
  have hex : ∀ i, ∃ q : ℤ[X], q.coeff 0 ≠ 0 ∧ (E i ≠ 0 → Polynomial.aeval (E i) q = 0) := by
    intro i
    by_cases hi : E i = 0
    · exact ⟨1, by simp, fun h => absurd hi h⟩
    · obtain ⟨q, hq0, hq⟩ :=
        (hE i).exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_iff_ne_zero.mpr hi)
      exact ⟨q, hq0, fun _ => hq⟩
  choose q hq0 hqroot using hex
  let g : ℤ[X] := ∏ i : ι, q i
  have hg0 : g.eval 0 ≠ 0 := by
    change (∏ i : ι, q i).eval 0 ≠ 0
    rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro i _
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hq0 i
  refine ⟨g, hg0, fun i hi => ?_⟩
  rw [Polynomial.mem_aroots]
  refine ⟨fun hzero => hg0 (by rw [hzero, Polynomial.eval_zero]), ?_⟩
  change Polynomial.aeval (E i) (∏ j : ι, q j) = 0
  rw [map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  exact hqroot i hi

end GaloisForLFunctions.RHTower
