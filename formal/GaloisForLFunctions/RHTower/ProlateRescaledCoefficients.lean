import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# The rescaled prolate equation in normal form, and its distance to the Hermite equation

The exact Hermite-scale defect identity

`u″ − ξ²u + μ u = (ξ² u″ + 2ξ u′)/c`

is a *regular* linear equation wherever `ξ² ≠ c`: solving for `u″` gives

`u″ = P_c u + Q_c u′` ,   `P_c ξ = c(ξ² − μ)/(c − ξ²)` ,   `Q_c ξ = 2ξ/(c − ξ²)` .

On a window `|ξ| ≤ K` with `2K² ≤ c` the denominator is at least `c/2`, and then

`|P_c − (ξ² − (2n+1))| ≤ 2|μ − (2n+1)| + 2K²(K² + 2n+1)/c` ,   `|Q_c| ≤ 4K/c` .

Both perturbations vanish as the bandwidth grows and the separation constant approaches the `n`-th
oscillator rung, so on every fixed window the rescaled prolate equation converges to the Hermite
equation with explicit rates.
-/

open Set

namespace RHTower

/-- Coefficient of the profile in the rescaled prolate equation written in normal form. -/
noncomputable def rescaledProlateP (c mu xi : ℝ) : ℝ := c * (xi ^ (2 : ℕ) - mu) / (c - xi ^ (2 : ℕ))

/-- Coefficient of the profile's derivative in the rescaled prolate equation. -/
noncomputable def rescaledProlateQ (c xi : ℝ) : ℝ := 2 * xi / (c - xi ^ (2 : ℕ))

/-- Coefficient of the Hermite equation at the `n`-th oscillator rung. -/
noncomputable def hermiteRungP (n : ℕ) (xi : ℝ) : ℝ := xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1)

/-- On the window the square is dominated by the window's square. -/
theorem sq_le_sq_of_abs_le {K xi : ℝ} (hxi : |xi| ≤ K) : xi ^ (2 : ℕ) ≤ K ^ (2 : ℕ) := by
  nlinarith [sq_abs xi, abs_nonneg xi]

/-- The bandwidth is positive once it dominates twice the window's square. -/
theorem pos_of_window {c K : ℝ} (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c) : 0 < c := by
  have : (0 : ℝ) < K ^ (2 : ℕ) := by positivity
  linarith

/-- On the window the normal-form denominator is at least half the bandwidth. -/
theorem half_le_sub_sq {c K xi : ℝ} (_hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c) (hxi : |xi| ≤ K) :
    c / 2 ≤ c - xi ^ (2 : ℕ) := by
  have := sq_le_sq_of_abs_le hxi
  linarith

/-- **Normal form.**  Away from `ξ² = c` the exact Hermite-scale defect identity solves for the
second derivative. -/
theorem deriv2_eq_of_hermiteDefect {c mu : ℝ} {u : ℝ → ℝ} {xi : ℝ}
    (hc : c ≠ 0) (hcx : c - xi ^ (2 : ℕ) ≠ 0)
    (hdef : hermiteSLAction u xi + mu * u xi
      = (xi ^ (2 : ℕ) * deriv (deriv u) xi + 2 * xi * deriv u xi) / c) :
    deriv (deriv u) xi
      = rescaledProlateP c mu xi * u xi + rescaledProlateQ c xi * deriv u xi := by
  have h : (deriv (deriv u) xi - xi ^ (2 : ℕ) * u xi + mu * u xi) * c
      = xi ^ (2 : ℕ) * deriv (deriv u) xi + 2 * xi * deriv u xi := by
    rw [hermiteSLAction] at hdef
    rw [hdef]
    field_simp
  have key : deriv (deriv u) xi * (c - xi ^ (2 : ℕ))
      = c * (xi ^ (2 : ℕ) - mu) * u xi + 2 * xi * deriv u xi := by linear_combination h
  rw [rescaledProlateP, rescaledProlateQ, div_mul_eq_mul_div, div_mul_eq_mul_div,
    ← add_div, eq_div_iff hcx]
  exact key

/-- The limiting Hermite coefficient is bounded on the window. -/
theorem abs_hermiteRungP_le {K xi : ℝ} {n : ℕ} (hxi : |xi| ≤ K) :
    |hermiteRungP n xi| ≤ K ^ (2 : ℕ) + (2 * (n : ℝ) + 1) := by
  have hx2 : xi ^ (2 : ℕ) ≤ K ^ (2 : ℕ) := sq_le_sq_of_abs_le hxi
  have hx0 : (0 : ℝ) ≤ xi ^ (2 : ℕ) := sq_nonneg xi
  have hn : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
  rw [hermiteRungP, abs_le]
  constructor <;> linarith

/-- The first-derivative coefficient is `O(K/c)` on the window. -/
theorem abs_rescaledProlateQ_le {c K xi : ℝ} (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (hxi : |xi| ≤ K) : |rescaledProlateQ c xi| ≤ 4 * K / c := by
  have hc : 0 < c := pos_of_window hK hcK
  have hhalf : c / 2 ≤ c - xi ^ (2 : ℕ) := half_le_sub_sq hK hcK hxi
  have hcx : (0 : ℝ) < c - xi ^ (2 : ℕ) := by linarith
  have h2 : |2 * xi| ≤ 2 * K := by
    rw [abs_mul, abs_two]
    linarith [abs_nonneg xi]
  rw [rescaledProlateQ, abs_div, abs_of_pos hcx, div_le_iff₀ hcx]
  have hstep : 4 * K / c * (c - xi ^ (2 : ℕ)) = 4 * K * (c - xi ^ (2 : ℕ)) / c := by ring
  rw [hstep, le_div_iff₀ hc]
  nlinarith [mul_nonneg hK.le (by linarith : (0 : ℝ) ≤ c - xi ^ (2 : ℕ) - c / 2),
    mul_nonneg hc.le (by linarith : (0 : ℝ) ≤ 2 * K - |2 * xi|)]

/-- **Coefficient distance.**  On the window the normal-form coefficient differs from the Hermite
rung coefficient by at most twice the separation defect plus an explicit `1/c` term. -/
theorem abs_rescaledProlateP_sub_le {c K mu xi : ℝ} {n : ℕ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c) (hxi : |xi| ≤ K) :
    |rescaledProlateP c mu xi - hermiteRungP n xi|
      ≤ 2 * |mu - (2 * (n : ℝ) + 1)|
        + 2 * (K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1))) / c := by
  have hc : 0 < c := pos_of_window hK hcK
  have hhalf : c / 2 ≤ c - xi ^ (2 : ℕ) := half_le_sub_sq hK hcK hxi
  have hcx : (0 : ℝ) < c - xi ^ (2 : ℕ) := by linarith
  have hcxne : c - xi ^ (2 : ℕ) ≠ 0 := ne_of_gt hcx
  have hx2 : xi ^ (2 : ℕ) ≤ K ^ (2 : ℕ) := sq_le_sq_of_abs_le hxi
  have hx0 : (0 : ℝ) ≤ xi ^ (2 : ℕ) := sq_nonneg xi
  have hn : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
  have hid : rescaledProlateP c mu xi - hermiteRungP n xi
      = (c * ((2 * (n : ℝ) + 1) - mu) + xi ^ (2 : ℕ) * (xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1)))
        / (c - xi ^ (2 : ℕ)) := by
    rw [rescaledProlateP, hermiteRungP]
    field_simp
    ring
  have hnum : |c * ((2 * (n : ℝ) + 1) - mu) + xi ^ (2 : ℕ) * (xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1))|
      ≤ c * |mu - (2 * (n : ℝ) + 1)| + K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1)) := by
    refine le_trans (abs_add_le _ _) ?_
    have hA : |c * ((2 * (n : ℝ) + 1) - mu)| = c * |mu - (2 * (n : ℝ) + 1)| := by
      rw [abs_mul, abs_of_pos hc, abs_sub_comm]
    have hB : |xi ^ (2 : ℕ) * (xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1))|
        ≤ K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1)) := by
      rw [abs_mul, abs_of_nonneg hx0]
      have hb1 : |xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1)| ≤ K ^ (2 : ℕ) + (2 * (n : ℝ) + 1) := by
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul hx2 hb1 (abs_nonneg _) (by positivity)
    rw [hA]
    linarith
  have hnn : (0 : ℝ) ≤ c * |mu - (2 * (n : ℝ) + 1)| + K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1)) := by
    have h1 : (0 : ℝ) ≤ c * |mu - (2 * (n : ℝ) + 1)| :=
      mul_nonneg hc.le (abs_nonneg _)
    have h2 : (0 : ℝ) ≤ K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1)) := by positivity
    linarith
  have hfrac : |c * ((2 * (n : ℝ) + 1) - mu) + xi ^ (2 : ℕ) * (xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1))|
      / (c - xi ^ (2 : ℕ))
      ≤ (c * |mu - (2 * (n : ℝ) + 1)| + K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1))) / (c / 2) := by
    gcongr
  have hfin : (c * |mu - (2 * (n : ℝ) + 1)| + K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1))) / (c / 2)
      = 2 * |mu - (2 * (n : ℝ) + 1)| + 2 * (K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1))) / c := by
    field_simp
  rw [hid, abs_div, abs_of_pos hcx]
  calc |c * ((2 * (n : ℝ) + 1) - mu) + xi ^ (2 : ℕ) * (xi ^ (2 : ℕ) - (2 * (n : ℝ) + 1))| / (c - xi ^ (2 : ℕ))
      ≤ (c * |mu - (2 * (n : ℝ) + 1)| + K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1))) / (c / 2) := hfrac
    _ = 2 * |mu - (2 * (n : ℝ) + 1)|
          + 2 * (K ^ (2 : ℕ) * (K ^ (2 : ℕ) + (2 * (n : ℝ) + 1))) / c := hfin

end RHTower
