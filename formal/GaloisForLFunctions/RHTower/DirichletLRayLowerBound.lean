import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Tactic

/-!
# The Dirichlet L-series is eventually bounded below on the real ray

As the real part grows the L-series of a Dirichlet character tends to its first coefficient
`χ 1 = 1`, so it is eventually at least `1/2` in modulus along the positive real axis.

No numerical estimate is involved: the bound comes from the limit, not from summing a tail.  This
is the factor needed to transfer the super-linear growth of the Gamma factor to the completed
L-function.
-/

open Filter Topology
open scoped LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- The L-series of a Dirichlet character tends to `1` along the real ray. -/
theorem tendsto_LSeries_atTop (χ : DirichletCharacter ℂ N) :
    Tendsto (fun x : ℝ => L ↗χ (x : ℂ)) atTop (𝓝 1) := by
  have habs : LSeries.abscissaOfAbsConv ↗χ < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) χ]
    exact EReal.coe_lt_top 1
  have htend := LSeries.tendsto_atTop habs
  have hone : χ ((1 : ℕ) : ZMod N) = 1 := by
    rw [Nat.cast_one, map_one]
  rwa [hone] at htend

/-- **Eventual lower bound on the ray.**  Along the positive real axis the L-series is eventually
at least `1/2` in modulus. -/
theorem eventually_half_le_norm_LSeries (χ : DirichletCharacter ℂ N) :
    ∀ᶠ x : ℝ in atTop, (1 / 2 : ℝ) ≤ ‖L ↗χ (x : ℂ)‖ := by
  have hnorm : Tendsto (fun x : ℝ => ‖L ↗χ (x : ℂ)‖) atTop (𝓝 1) := by
    simpa using (tendsto_LSeries_atTop χ).norm
  exact hnorm.eventually_const_le (by norm_num)

end RHTower
