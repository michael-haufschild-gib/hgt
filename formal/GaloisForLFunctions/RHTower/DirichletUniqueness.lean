import GaloisForLFunctions.RHTower.DirichletCoeffBound

/-!
# Uniqueness of Dirichlet coefficients

A Dirichlet series converging uniformly to zero on a half-plane has all coefficients zero, and
consequently two series with the same sum have the same coefficients.

This is Bohr's coefficient estimate at `C = 0`: the bound `‖a_n‖ ≤ C (n+1)^σ` degenerates to
`‖a_n‖ ≤ 0`.  No separate argument is needed, and in particular no analytic continuation and no
identity theorem for holomorphic functions.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **A Dirichlet series summing to zero has zero coefficients.** -/
theorem coeff_eq_zero_of_tendstoUniformlyOn_zero {a : ℕ → ℂ} {x : ℝ}
    (hF : TendstoUniformlyOn (dirichletPartialSum a) 0 atTop {s : ℂ | x ≤ s.re}) (n : ℕ) :
    a n = 0 := by
  have hC : ∀ s : ℂ, x ≤ s.re → ‖(0 : ℂ → ℂ) s‖ ≤ 0 := by
    intro s _
    simp
  have h := norm_coeff_le hF hC n (le_refl x)
  rw [zero_mul] at h
  exact norm_eq_zero.1 (le_antisymm h (norm_nonneg _))

/-- The partial sums of a difference are the difference of the partial sums. -/
theorem dirichletPartialSum_sub (a b : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    dirichletPartialSum (fun n => a n - b n) N s
      = dirichletPartialSum a N s - dirichletPartialSum b N s := by
  rw [dirichletPartialSum, dirichletPartialSum, dirichletPartialSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Uniqueness of Dirichlet coefficients.**  Two series converging uniformly to the same sum on a
half-plane have the same coefficients. -/
theorem coeff_eq_of_tendstoUniformlyOn {a b : ℕ → ℂ} {x : ℝ} {F : ℂ → ℂ}
    (ha : TendstoUniformlyOn (dirichletPartialSum a) F atTop {s : ℂ | x ≤ s.re})
    (hb : TendstoUniformlyOn (dirichletPartialSum b) F atTop {s : ℂ | x ≤ s.re}) (n : ℕ) :
    a n = b n := by
  have hsub : TendstoUniformlyOn (dirichletPartialSum (fun m => a m - b m)) 0 atTop
      {s : ℂ | x ≤ s.re} := by
    have h := ha.sub hb
    refine h.congr ?_ |>.congr_right ?_
    · filter_upwards with N
      intro s _
      exact (dirichletPartialSum_sub a b N s).symm
    · intro s _
      simp
  have := coeff_eq_zero_of_tendstoUniformlyOn_zero hsub n
  linear_combination (norm := ring_nf) this

end GaloisForLFunctions.RHTower

end
