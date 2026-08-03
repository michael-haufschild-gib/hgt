import GaloisForLFunctions.RHTower.Sieve.ZeroLineSum

/-!
# Gram entries of separated Dirichlet rows

The Gram entry of two Dirichlet rows is the zero-line exponential sum at the frequency difference,

`⟪dirRow N t, dirRow N u⟫ = ∑_{n ≤ N} n^{i(u-t)}`,

so the estimate of `ZeroLineSum.lean` applies verbatim:

`‖⟪dirRow N t, dirRow N u⟫‖ ≤ (N+2)/|u-t| + |u-t| (1 + log N)`.

Together with the near-diagonal Lipschitz bound of `DirichletLipschitz.lean` this brackets the Gram
entry from both sides: it is close to `N` for `|u-t| ≪ 1/log N`, and much smaller than `N` once
`|u-t|` exceeds `1` while staying below `N/log N`.  The transition between the two regimes is what a
mean value theorem exploits.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **The Gram entry is a zero-line exponential sum.** -/
theorem inner_dirRow_eq_sum_zpow0 (N : ℕ) (t u : ℝ) :
    ⟪dirRow N t, dirRow N u⟫_ℂ = ∑ n ∈ Finset.range N, zpow0 (u - t) ((n : ℝ) + 1) := by
  rw [inner_dirRow, ← Fin.sum_univ_eq_sum_range (fun n => zpow0 (u - t) ((n : ℝ) + 1)) N]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [zpow0_eq]

/-- **The far-field Gram bound.** -/
theorem norm_inner_dirRow_le_far (N : ℕ) (t u : ℝ) :
    ‖⟪dirRow N t, dirRow N u⟫_ℂ‖
      ≤ ((N : ℝ) + 2) / ‖(1 : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I‖
        + |u - t| * (1 + Real.log N) := by
  rw [inner_dirRow_eq_sum_zpow0]
  exact norm_sum_zpow0_le (u - t) N

/-- The imaginary part is dominated by the modulus. -/
theorem abs_le_norm_one_add_mul_I (d : ℝ) : |d| ≤ ‖(1 : ℂ) + (d : ℂ) * Complex.I‖ := by
  have h := Complex.abs_im_le_norm ((1 : ℂ) + (d : ℂ) * Complex.I)
  simpa using h

/-- **The far-field Gram bound in terms of the frequency gap.** -/
theorem norm_inner_dirRow_le_gap (N : ℕ) {t u : ℝ} (h : t ≠ u) :
    ‖⟪dirRow N t, dirRow N u⟫_ℂ‖
      ≤ ((N : ℝ) + 2) / |u - t| + |u - t| * (1 + Real.log N) := by
  have hgap : (0 : ℝ) < |u - t| := by
    rw [abs_pos]
    exact sub_ne_zero_of_ne (Ne.symm h)
  have hle : |u - t| ≤ ‖(1 : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I‖ := abs_le_norm_one_add_mul_I _
  have hmono : ((N : ℝ) + 2) / ‖(1 : ℂ) + ((u - t : ℝ) : ℂ) * Complex.I‖
      ≤ ((N : ℝ) + 2) / |u - t| := by
    gcongr
  exact le_trans (norm_inner_dirRow_le_far N t u) (by linarith)

end RHTower.Sieve
