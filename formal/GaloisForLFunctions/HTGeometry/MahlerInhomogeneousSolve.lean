import GaloisForLFunctions.HTGeometry.MahlerHomogeneousRigidity

/-!
# Unique solvability of inhomogeneous Mahler equations in formal power series

For `k ≥ 2` and `c ∉ {0,1}` the equation `Y(X^k) = c·Y + H` has exactly one formal
power-series solution for every right-hand side `H`
(`mahler_inhomogeneous_solvable`): coefficients are determined recursively — the constant
term by `y₀ = h₀/(1−c)`, positions not divisible by `k` by `yₙ = −hₙ/c`, and divisible
positions by descent along `n ↦ n/k` — and uniqueness is the homogeneous rigidity.  This is
the existence engine for the higher Böttcher parameter jets: each jet of the conjugacy
constraint satisfies such an equation whose inhomogeneity is built from the lower jets, so
the whole jet tower is pinned inductively.
-/

open PowerSeries

namespace GaloisForLFunctions

/-- Coefficient recursion solving `Y(X^k) = c·Y + H`. -/
noncomputable def mahlerSolveCoeff (k : ℕ) (c : ℂ) (h : ℕ → ℂ) : ℕ → ℂ
  | 0 => h 0 / (1 - c)
  | (n + 1) =>
    ((if _hd : 2 ≤ k ∧ k ∣ (n + 1) then mahlerSolveCoeff k c h ((n + 1) / k) else 0)
      - h (n + 1)) / c
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by omega)

theorem mahlerSolveCoeff_zero (k : ℕ) (c : ℂ) (h : ℕ → ℂ) :
    mahlerSolveCoeff k c h 0 = h 0 / (1 - c) := by
  rw [mahlerSolveCoeff.eq_def]

theorem mahlerSolveCoeff_succ (k : ℕ) (c : ℂ) (h : ℕ → ℂ) (n : ℕ) :
    mahlerSolveCoeff k c h (n + 1)
      = ((if _hd : 2 ≤ k ∧ k ∣ (n + 1) then mahlerSolveCoeff k c h ((n + 1) / k) else 0)
          - h (n + 1)) / c := by
  rw [mahlerSolveCoeff.eq_def]

/-- **Unique solvability of the inhomogeneous Mahler equation** `Y(X^k) = c·Y + H`. -/
theorem mahler_inhomogeneous_solvable {k : ℕ} (hk : 2 ≤ k) {c : ℂ}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (H : ℂ⟦X⟧) :
    ∃! Y : ℂ⟦X⟧, subst (PowerSeries.X ^ k) Y = PowerSeries.C c * Y + H := by
  have hc1' : (1 : ℂ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have hW : subst (PowerSeries.X ^ k)
        (PowerSeries.mk (mahlerSolveCoeff k c fun j => PowerSeries.coeff j H))
      = PowerSeries.C c
          * PowerSeries.mk (mahlerSolveCoeff k c fun j => PowerSeries.coeff j H) + H := by
    ext n
    rw [PowerSeries.coeff_subst_X_pow (by omega : k ≠ 0), map_add, coeff_C_mul,
      PowerSeries.coeff_mk]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    cases n with
    | zero =>
      rw [if_pos (dvd_zero k), Nat.zero_div, PowerSeries.coeff_mk, mahlerSolveCoeff_zero]
      field_simp
      ring
    | succ n =>
      conv_rhs => rw [PowerSeries.coeff_mk]
      rw [mahlerSolveCoeff_succ]
      by_cases hdvd : k ∣ n + 1
      · rw [if_pos hdvd, dif_pos ⟨hk, hdvd⟩]
        field_simp
        ring
      · rw [if_neg hdvd, dif_neg (fun hh => hdvd hh.2)]
        field_simp
        ring
  refine ⟨_, hW, fun Y₂ h₂ => ?_⟩
  have hsub : subst (PowerSeries.X ^ k)
        (Y₂ - PowerSeries.mk (mahlerSolveCoeff k c fun j => PowerSeries.coeff j H))
      = PowerSeries.C c
          * (Y₂ - PowerSeries.mk (mahlerSolveCoeff k c fun j => PowerSeries.coeff j H)) := by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X_pow (by omega : k ≠ 0)),
      map_sub, PowerSeries.coe_substAlgHom, h₂, hW]
    ring
  exact sub_eq_zero.mp (mahler_homogeneous_eq_zero hk hc0 hc1 hsub)

end GaloisForLFunctions
