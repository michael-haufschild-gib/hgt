import GaloisForLFunctions.HTGeometry.LinearExponentialSum
import Mathlib.NumberTheory.DiophantineApproximation.Basic

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

open _root_.HTGeometry
open scoped BigOperators

noncomputable section

/-- **Periodic complement characters admit no uniform negative real-part gap.** -/
theorem not_exists_uniform_negative_re_ee_sub_one (α : ℝ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n ≠ 0 →
      (ee ((n : ℝ) * α) - 1).re ≤ -c := by
  rintro ⟨c, hc, hgap⟩
  have hε : 0 < c / (4 * Real.pi) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn, hnN, happrox⟩ :=
    Real.exists_nat_abs_mul_sub_round_le α (n := N + 1) (Nat.succ_pos N)
  have happrox_lt : |(n : ℝ) * α - round ((n : ℝ) * α)| < c / (4 * Real.pi) :=
    happrox.trans_lt (by
      calc
        1 / ((↑(N + 1) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          gcongr
          exact_mod_cast Nat.le_succ N
        _ < c / (4 * Real.pi) := hN)
  have hnorm : ‖ee ((n : ℝ) * α) - 1‖ ≤
      2 * Real.pi * (c / (4 * Real.pi)) :=
    norm_ee_sub_one_le_two_pi_mul_of_integer_approximation
      (round ((n : ℝ) * α)) happrox_lt.le
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
