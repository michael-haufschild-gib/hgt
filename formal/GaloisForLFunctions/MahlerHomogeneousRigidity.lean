import Mathlib

/-!
# Rigidity of homogeneous Mahler equations in formal power series

The homogeneous Mahler equation `Y(X^k) = c·Y(X)` with `k ≥ 2` and `c ∉ {0,1}` has no nonzero
formal power-series solution (`mahler_homogeneous_eq_zero`): comparing coefficients, positions
not divisible by `k` are killed by `c ≠ 0`, the constant term by `c ≠ 1`, and the remaining
positions descend along `n ↦ n/k` to smaller ones.  In particular `Y(X²) = 2·Y(X)` forces
`Y = 0` (`mahler_homogeneous_two_eq_zero`) — the exceptional-equation check in the order-one
Mahler dichotomy: the inhomogeneous equation of the first Böttcher parameter velocity has no
homogeneous obstruction, so irrationality upgrades to differential transcendence there.
-/

open PowerSeries

namespace GaloisForLFunctions

/-- **Homogeneous Mahler rigidity.**  `Y(X^k) = c·Y` with `k ≥ 2`, `c ≠ 0`, `c ≠ 1` forces
`Y = 0` in `ℂ⟦X⟧`. -/
theorem mahler_homogeneous_eq_zero {Y : ℂ⟦X⟧} {k : ℕ} (hk : 2 ≤ k) {c : ℂ}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (h : subst (PowerSeries.X ^ k) Y = PowerSeries.C c * Y) : Y = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (fun G => PowerSeries.coeff n G) h
    simp only [] at hc
    rw [PowerSeries.coeff_subst_X_pow (by omega : k ≠ 0), coeff_C_mul] at hc
    by_cases hdvd : k ∣ n
    · rw [if_pos hdvd] at hc
      by_cases hn0 : n = 0
      · subst hn0
        simp only [Nat.zero_div, Algebra.algebraMap_self, RingHom.id_apply] at hc
        have hfac : (1 - c) * PowerSeries.coeff 0 Y = 0 := by linear_combination hc
        rcases mul_eq_zero.mp hfac with h1 | h1
        · exact absurd (by linear_combination -h1) hc1
        · exact h1
      · have hlt : n / k < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
        rw [ih (n / k) hlt] at hc
        simp only [map_zero] at hc
        rcases mul_eq_zero.mp hc.symm with h1 | h1
        · exact absurd h1 hc0
        · exact h1
    · rw [if_neg hdvd] at hc
      rcases mul_eq_zero.mp hc.symm with h1 | h1
      · exact absurd h1 hc0
      · exact h1

/-- The exceptional homogeneous equation of the Böttcher velocity's Mahler equation:
`Y(X²) = 2·Y` has no nonzero power-series solution. -/
theorem mahler_homogeneous_two_eq_zero {Y : ℂ⟦X⟧}
    (h : subst (PowerSeries.X ^ 2) Y = 2 * Y) : Y = 0 := by
  refine mahler_homogeneous_eq_zero le_rfl (two_ne_zero) (by norm_num) ?_
  rw [h]
  congr 1

/-- **The Mahler substitution endomorphism is injective**: `f(X^k) = g(X^k)` forces `f = g`
for `k ≥ 1` — the coefficient at `k·n` of the substituted series reads off the coefficient at
`n`. -/
theorem subst_X_pow_injective {k : ℕ} (hk : k ≠ 0) :
    Function.Injective (fun f : ℂ⟦X⟧ => (subst (PowerSeries.X ^ k) f : ℂ⟦X⟧)) := by
  intro f g h
  ext n
  have hc := congrArg (PowerSeries.coeff (k * n)) h
  simp only [] at hc
  rw [PowerSeries.coeff_subst_X_pow hk, PowerSeries.coeff_subst_X_pow hk,
    if_pos (Dvd.intro n rfl), if_pos (Dvd.intro n rfl),
    Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hk)] at hc
  simpa using hc

end GaloisForLFunctions
