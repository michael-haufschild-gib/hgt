import GaloisForLFunctions.RHTower.MoebiusResidualTailForm

/-!
# The design problem for modular coefficients, and the absence of exact solutions

The residual identities of the previous files are instances of one algebraic law.  For *any* coefficients
`c : ℕ → ℝ` on `[1,N]`, since `g_d(n) = n/d − ⌊n/d⌋`,

**`residual_eq_of_coeff` — `1 − ∑_{d ≤ N} c_d·g_d(n) = 1 + D_c(n) − n·C₁(c)`**,
`D_c(n) = ∑_{d ≤ N} c_d⌊n/d⌋`,  `C₁(c) = ∑_{d ≤ N} c_d/d`.

So the design problem is explicit: choose `c` supported on `[1,N]` making `D_c(n)` close to `−1` uniformly
while keeping `C₁(c)` small.  The Möbius choice `c = −μ` makes `D_c(n) = −1` *exactly* for `n ≤ N`
(`moebius_floor_summatory`) at the cost `C₁ = −M₁(N)`; every other proposal — Vasyunin-type damping
included — is a different trade between the two terms.

No choice can be exact.  The generator `g_d` vanishes on the multiples of `d`, so at `n₀ = N !`, which every
`d ≤ N` divides, *every* combination vanishes while the target is `1`:

**`no_exact_modular_representation` — there is no finitely supported `c` with `∑_d c_d·g_d(n) = 1` for all
`n ≥ 1`.**

This is the pointwise form of the arithmetic obstruction of `ArithmeticEvaluationObstruction`, and it explains
why the criterion is a statement about limits: exact representation is impossible for divisibility reasons,
so `d_N → 0` is the only shape the conclusion could take.
-/

open Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- **The residual of an arbitrary modular combination.** -/
theorem residual_eq_of_coeff (c : ℕ → ℝ) (n N : ℕ) :
    1 - ∑ d ∈ Finset.Icc 1 N, c d * (((n % d : ℕ) : ℝ) / (d : ℝ))
      = 1 + (∑ d ∈ Finset.Icc 1 N, c d * ((n / d : ℕ) : ℝ))
        - (n : ℝ) * (∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ)) := by
  have hsplit : ∀ d ∈ Finset.Icc 1 N,
      c d * (((n % d : ℕ) : ℝ) / (d : ℝ))
        = (n : ℝ) * (c d / (d : ℝ)) - c d * ((n / d : ℕ) : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [modSeq_eq_sub_floor hd1]
    have hd0 : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      exact ne_of_gt this
    field_simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- A modular combination vanishes at any common multiple of its moduli. -/
theorem sum_modSeq_eq_zero_of_forall_dvd (c : ℕ → ℝ) {N n₀ : ℕ}
    (hdvd : ∀ d ∈ Finset.Icc 1 N, d ∣ n₀) :
    ∑ d ∈ Finset.Icc 1 N, c d * (((n₀ % d : ℕ) : ℝ) / (d : ℝ)) = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  have hmod : n₀ % d = 0 := Nat.dvd_iff_mod_eq_zero.mp (hdvd d hd)
  rw [hmod]
  norm_num

/-- **No exact modular representation of the target.**  For any `N` and any coefficients, the combination
misses the target at `n₀ = N !`. -/
theorem no_exact_modular_representation (c : ℕ → ℝ) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, c d * (((Nat.factorial N % d : ℕ) : ℝ) / (d : ℝ)) ≠ 1 := by
  have hdvd : ∀ d ∈ Finset.Icc 1 N, d ∣ Nat.factorial N := by
    intro d hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    exact Nat.dvd_factorial (by omega) hdN
  rw [sum_modSeq_eq_zero_of_forall_dvd c hdvd]
  norm_num

/-- The Möbius choice, as an instance of the design law: `D_c(n) = −1` on `[1,N]`. -/
theorem sum_neg_moebius_floor_of_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, (-((moebius d : ℤ) : ℝ)) * ((n / d : ℕ) : ℝ) = -1 := by
  have h := moebius_floor_summatory_le hn hnN
  rw [← neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
  rw [← h]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

end RHTower

end
