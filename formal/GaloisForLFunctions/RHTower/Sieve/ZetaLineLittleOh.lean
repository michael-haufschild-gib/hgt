import GaloisForLFunctions.RHTower.Sieve.ZetaLineIndexBridge

/-!
# `ζ` on the line `Re s = 1`

Feeding the derivative-test bound through the truncation gives a bound on `ζ(1 + it)` itself.  The
two tail terms of the truncation are `1/t` and `‖1 + it‖ / M`, and the truncation point `M` exceeds
`(t/8π)^(3 : ℕ) - 1`, so both are explicit and tend to zero while the head is `o (log t)`.
-/

namespace RHTower.Sieve

open Finset

/-- The truncation point of the chain, one below a power of two. -/
noncomputable def lineTruncation (t : ℝ) : ℕ := 2 ^ (topExponent t + 1) - 1

theorem one_le_lineTruncation (t : ℝ) : 1 ≤ lineTruncation t := by
  have h2 : 2 ≤ 2 ^ (topExponent t + 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (topExponent t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [lineTruncation]
  omega

theorem lineTruncation_add_one (t : ℝ) : lineTruncation t + 1 = 2 ^ (topExponent t + 1) := by
  have h1 := one_le_lineTruncation t
  rw [lineTruncation]
  have h2 : 1 ≤ 2 ^ (topExponent t + 1) := Nat.one_le_two_pow
  omega

/-- The truncation point exceeds `(t/8π)^(3 : ℕ) - 1`. -/
theorem cube_sub_one_le_lineTruncation {t : ℝ} (ht : 8 * Real.pi ≤ t) :
    (t / (8 * Real.pi)) ^ (3 : ℕ) - 1 ≤ ((lineTruncation t : ℕ) : ℝ) := by
  have h2 := lineTruncation_add_one t
  have hR : ((lineTruncation t : ℕ) : ℝ) + 1 = ((2 ^ (topExponent t + 1) : ℕ) : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    push_cast at this ⊢
    linarith
  linarith [cube_le_two_pow_topExponent ht, hR]

/-- **`ζ(1 + it)` is `o (log t)`.**  The head is the derivative-test bound, the two tail terms are
explicit and vanish. -/
theorem norm_riemannZeta_line_littleOh {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖riemannZeta (1 + Complex.I * (t : ℂ))‖
        ≤ 1 + Real.log 2 + ε * Real.log (t / (2 * Real.pi))
          + 1 / t + (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) := by
  obtain ⟨T₀, hT₀⟩ := littlewood_littleOh hε
  have hπ := Real.pi_pos
  refine ⟨max T₀ (16 * Real.pi), fun t hT => ?_⟩
  have ht0 : T₀ ≤ t := le_trans (le_max_left _ _) hT
  have ht16 : 16 * Real.pi ≤ t := le_trans (le_max_right _ _) hT
  have ht8 : 8 * Real.pi ≤ t := by linarith
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hM1 : 1 ≤ lineTruncation t := one_le_lineTruncation t
  -- the truncation
  have htrunc := norm_riemannZeta_one_add_I_mul_le ht hM1
  -- rewrite the head into the derivative-test range
  have hhead : ∑ k ∈ Finset.Icc 1 (lineTruncation t),
        ((k : ℝ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))
      = ∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) := by
    rw [sum_Icc_cpow_eq_sum_Ico t (lineTruncation t), lineTruncation_add_one t]
  rw [hhead] at htrunc
  refine le_trans htrunc ?_
  -- head bound
  have hlittle := hT₀ t ht0
  -- tail bound
  have hcube : (1 : ℝ) < (t / (8 * Real.pi)) ^ (3 : ℕ) := by
    have h2 : (2 : ℝ) ≤ t / (8 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc (1 : ℝ) < 2 ^ (3 : ℕ) := by norm_num
      _ ≤ (t / (8 * Real.pi)) ^ (3 : ℕ) := by
        exact pow_le_pow_left₀ (by norm_num) h2 3
  have hden : (0 : ℝ) < (t / (8 * Real.pi)) ^ (3 : ℕ) - 1 := by linarith
  have hMpos : (0 : ℝ) < ((lineTruncation t : ℕ) : ℝ) :=
    lt_of_lt_of_le hden (cube_sub_one_le_lineTruncation ht8)
  have hnorm : ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ 1 + t := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
  have htail : ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ / ((lineTruncation t : ℕ) : ℝ)
      ≤ (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) := by
    have hA : ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ / ((lineTruncation t : ℕ) : ℝ)
        ≤ (1 + t) / ((lineTruncation t : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnorm hMpos.le
    have hB : (1 + t) / ((lineTruncation t : ℕ) : ℝ)
        ≤ (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) :=
      div_le_div_of_nonneg_left (by linarith) hden (cube_sub_one_le_lineTruncation ht8)
    linarith
  linarith [hlittle, htail]

end RHTower.Sieve
