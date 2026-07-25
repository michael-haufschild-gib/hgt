/-
# Contracting scale induction

Bourgain's bilinear-to-linear argument ends with a recurrence in which the
normalized mean-value constant at scale `N` is a fixed contraction times the
constant at a smaller scale, plus `O(N^ε)`.  This module proves the abstract
strong-induction step for dyadic scale reduction.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace RHTower

noncomputable section

/-- A dyadic contracting recurrence with coefficient `q < 1` preserves an
`N^ε` bound. -/
theorem subpower_bound_of_dyadic_contraction
    (b : ℕ → ℝ) {q C B ε : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : b 1 ≤ B)
    (hrec :
      ∀ n : ℕ, 2 ≤ n →
        b n ≤ q * b (n / 2) + C * (n : ℝ) ^ ε) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ n : ℕ, 0 < n →
        b n ≤ D * (n : ℝ) ^ ε := by
  let D : ℝ := max B (C / (1 - q))
  have honeMinusQ : 0 < 1 - q := by linarith
  have hDnonneg : 0 ≤ D := by
    exact hB.trans (le_max_left _ _)
  have hBD : B ≤ D := le_max_left _ _
  have hCDiv : C / (1 - q) ≤ D := le_max_right _ _
  have hcontract : q * D + C ≤ D := by
    have hCD : C ≤ D * (1 - q) := by
      exact (div_le_iff₀ honeMinusQ).mp hCDiv
    nlinarith
  refine ⟨D, hDnonneg, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst n
        simpa using hbase.trans hBD
      · have hn2 : 2 ≤ n := by omega
        have hdivPos : 0 < n / 2 := by omega
        have hdivLt : n / 2 < n :=
          Nat.div_lt_self hn (by norm_num)
        have hind :
            b (n / 2) ≤ D * ((n / 2 : ℕ) : ℝ) ^ ε :=
          ih (n / 2) hdivLt hdivPos
        have hcast :
            (((n / 2 : ℕ) : ℝ)) ≤ (n : ℝ) := by
          exact_mod_cast Nat.div_le_self n 2
        have hrpow :
            (((n / 2 : ℕ) : ℝ)) ^ ε ≤ (n : ℝ) ^ ε :=
          Real.rpow_le_rpow (by positivity) hcast hε
        have hDpow :
            D * (((n / 2 : ℕ) : ℝ)) ^ ε ≤
              D * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hrpow hDnonneg
        have hqDpow :
            q * (D * (((n / 2 : ℕ) : ℝ)) ^ ε) ≤
              q * (D * (n : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hDpow hq0
        calc
          b n ≤ q * b (n / 2) + C * (n : ℝ) ^ ε :=
            hrec n hn2
          _ ≤ q * (D * (((n / 2 : ℕ) : ℝ)) ^ ε) +
              C * (n : ℝ) ^ ε :=
            add_le_add (mul_le_mul_of_nonneg_left hind hq0) le_rfl
          _ ≤ q * (D * (n : ℝ) ^ ε) +
              C * (n : ℝ) ^ ε :=
            add_le_add hqDpow le_rfl
          _ = (q * D + C) * (n : ℝ) ^ ε := by ring
          _ ≤ D * (n : ℝ) ^ ε :=
            mul_le_mul_of_nonneg_right hcontract
              (Real.rpow_nonneg (by positivity) ε)

end

end RHTower
