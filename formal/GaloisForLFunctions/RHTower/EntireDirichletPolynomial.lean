import GaloisForLFunctions.HTGeometry.TwistedDirichletMeanValue

/-!
# A finite Dirichlet polynomial as an entire function

The mean-value machinery of this development uses `cdpoly`, a Dirichlet polynomial written as a
function of the *height* along a fixed vertical line.  Littlewood's rectangle identity instead needs
the same object as an entire function of the complex variable.  This file supplies that form,
`edPoly`, proves it entire, and identifies its restriction to any vertical line with `cdpoly`.

Two elementary estimates come with it: the triangle-inequality upper bound, and the head-dominance
lower bound `‖Ψ(z)‖ ≥ ‖a₁‖ − ∑_{n ≥ 2} ‖aₙ‖ n^{-Re z}` which is what a far-right edge estimate
consumes.
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A finite Dirichlet polynomial as an entire function of the complex variable. -/
def edPoly (a : ℕ → ℂ) (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, a n * ((n : ℝ) : ℂ) ^ (-z)

theorem differentiable_edPoly (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) :
    Differentiable ℂ (edPoly a s) := by
  have hterm : ∀ n ∈ s, Differentiable ℂ (fun z : ℂ => a n * ((n : ℝ) : ℂ) ^ (-z)) := by
    intro n hn z
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs n hn
    have hne : (((n : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
    exact (DifferentiableAt.const_cpow (differentiable_id.neg z) (Or.inl hne)).const_mul (a n)
  have hsum := Differentiable.sum (u := s) fun n hn => hterm n hn
  have heq : (∑ n ∈ s, fun z : ℂ => a n * ((n : ℝ) : ℂ) ^ (-z)) = edPoly a s := by
    funext z
    simp [edPoly, Finset.sum_apply]
  rwa [heq] at hsum

theorem analyticOnNhd_edPoly (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) :
    AnalyticOnNhd ℂ (edPoly a s) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (differentiable_edPoly a hs)

/-- On a vertical line the entire Dirichlet polynomial is the height-parameterized one. -/
theorem edPoly_line (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (σ t : ℝ) :
    edPoly a s ((σ : ℂ) + (t : ℂ) * I) = cdpoly a s σ t := by
  unfold edPoly cdpoly cdterm
  refine Finset.sum_congr rfl fun n hn => ?_
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs n hn
  have hterm : ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
      = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-(Real.log n) * t : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
      Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [← Complex.ofReal_log hpos.le]
    push_cast
    ring
  rw [hterm, mul_assoc]

theorem norm_edPoly_le (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (z : ℂ) :
    ‖edPoly a s z‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-z.re)) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs n hn
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  simp

/-- **Head dominance.**  If the coefficient at `n = 1` dominates the rest of the polynomial on the
vertical line `Re z = x`, the polynomial is bounded below there. -/
theorem norm_edPoly_ge (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (h1 : 1 ∈ s) (z : ℂ) :
    ‖a 1‖ - (∑ n ∈ s.erase 1, ‖a n‖ * ((n : ℝ) ^ (-z.re))) ≤ ‖edPoly a s z‖ := by
  classical
  have hsplit : edPoly a s z = a 1 + ∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z) := by
    unfold edPoly
    rw [← Finset.sum_erase_add _ _ h1]
    have : a 1 * (((1 : ℕ) : ℝ) : ℂ) ^ (-z) = a 1 := by norm_num
    rw [this]
    ring
  have htail : ‖∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z)‖
      ≤ ∑ n ∈ s.erase 1, ‖a n‖ * ((n : ℝ) ^ (-z.re)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hs n (Finset.mem_of_mem_erase hn)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  rw [hsplit]
  have hge : ‖a 1‖ - ‖∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z)‖
      ≤ ‖a 1 + ∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z)‖ := by
    have hz := norm_sub_le (a 1 + ∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z))
      (∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z))
    simp only [add_sub_cancel_right] at hz
    linarith
  linarith

end RHTower

end
