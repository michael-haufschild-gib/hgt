import GaloisForLFunctions.RHTower.MixedStateQutritRecurrenceSeparation

/-!
# No uniform damping gap for a periodic complement character

The proposed all-order extension previously used a uniform `c > 0` with
`Re (E(n * α) - 1) ≤ -c` at every nonzero complement index.  That estimate is impossible:
Dirichlet recurrence returns every real additive character arbitrarily close to `1` along a
nonzero positive integer.  This is a closed obstruction, not an analytic assumption.

It does not refute Abe's point- and tangent-separation theorems.  It rules out only the uniform
global exponential-majorant route and forces any all-order proof to use a genuine two-scale tail
argument.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- **Periodic complement characters admit no uniform negative real-part gap.** -/
theorem not_exists_uniform_negative_re_ee_sub_one (α : ℝ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n ≠ 0 →
      (ee ((n : ℝ) * α) - 1).re ≤ -c := by
  rintro ⟨c, hc, hgap⟩
  have hε : 0 < c / (4 * Real.pi) := by positivity
  obtain ⟨n, hn, r, happrox⟩ :=
    RHTower.exists_fin_simultaneous_integer_approximation
      (fun _ : Fin 1 => α) hε
  have hnorm : ‖ee ((n : ℝ) * α) - 1‖ ≤ 2 * Real.pi * (c / (4 * Real.pi)) :=
    RHTower.norm_ee_sub_one_le_two_pi_mul_of_integer_approximation (r 0) (happrox 0)
  have hhalf : 2 * Real.pi * (c / (4 * Real.pi)) = c / 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  have hnorm_lt : ‖ee ((n : ℝ) * α) - 1‖ < c := by
    rw [hhalf] at hnorm
    exact hnorm.trans_lt (half_lt_self hc)
  have hbelow : -‖ee ((n : ℝ) * α) - 1‖ ≤ (ee ((n : ℝ) * α) - 1).re := by
    exact (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hstrict : -c < (ee ((n : ℝ) * α) - 1).re :=
    (neg_lt_neg hnorm_lt).trans_le hbelow
  exact (not_lt_of_ge (hgap n (Nat.ne_of_gt hn))) hstrict

end

end GaloisForLFunctions.HTGeometry
