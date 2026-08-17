import Mathlib.Analysis.Complex.Liouville

/-!
# One Cauchy step for a second-order operator

An operator of the shape `c₀·f + c₁·f′ − f″` acting on a function holomorphic on a disc is
controlled by the sup norm on the boundary circle alone: Cauchy's estimates give

`‖f(z)‖ ≤ M`,  `‖f′(z)‖ ≤ M/R`,  `‖f″(z)‖ ≤ 2M/R²`,

so the value at the centre is at most `‖c₀‖M + ‖c₁‖M/R + 2M/R²`.

This is the step of the caustic iteration: the first coefficient carries the symbol, which is small
on the balance window, and the two derivative terms are paid for by the radius.  Choosing the radius
comparable with the window width makes all three contributions of the same order.
-/

open Complex Metric

namespace HTGeometry

noncomputable section

/-- The second iterated derivative is the derivative of the derivative. -/
theorem iteratedDeriv_two (f : ℂ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- **One Cauchy step.**  A second-order operator at the centre of a disc, in terms of the boundary
sup norm. -/
theorem norm_secondOrderOperator_le {f : ℂ → ℂ} {z c₀ c₁ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball z R))
    (hM : ∀ ζ ∈ sphere z R, ‖f ζ‖ ≤ M) :
    ‖c₀ * f z + c₁ * deriv f z - deriv (deriv f) z‖
      ≤ ‖c₀‖ * M + ‖c₁‖ * (M / R) + 2 * M / R ^ 2 := by
  have h0 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0 hR hf hM
  have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hf hM
  have h2 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR hf hM
  rw [iteratedDeriv_zero] at h0
  rw [iteratedDeriv_one] at h1
  rw [iteratedDeriv_two] at h2
  simp only [Nat.factorial] at h1 h2
  have h0' : ‖f z‖ ≤ M := by simpa using h0
  have h1' : ‖deriv f z‖ ≤ M / R := by
    refine le_trans h1 (le_of_eq ?_)
    push_cast
    ring
  have h2' : ‖deriv (deriv f) z‖ ≤ 2 * M / R ^ 2 := by
    refine le_trans h2 (le_of_eq ?_)
    push_cast
    ring
  have hc0 : ‖c₀ * f z‖ ≤ ‖c₀‖ * M := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left h0' (norm_nonneg _)
  have hc1 : ‖c₁ * deriv f z‖ ≤ ‖c₁‖ * (M / R) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
  calc ‖c₀ * f z + c₁ * deriv f z - deriv (deriv f) z‖
      ≤ ‖c₀ * f z + c₁ * deriv f z‖ + ‖deriv (deriv f) z‖ := norm_sub_le _ _
    _ ≤ (‖c₀ * f z‖ + ‖c₁ * deriv f z‖) + ‖deriv (deriv f) z‖ := by
        linarith [norm_add_le (c₀ * f z) (c₁ * deriv f z)]
    _ ≤ ‖c₀‖ * M + ‖c₁‖ * (M / R) + 2 * M / R ^ 2 := by linarith

end

end HTGeometry
