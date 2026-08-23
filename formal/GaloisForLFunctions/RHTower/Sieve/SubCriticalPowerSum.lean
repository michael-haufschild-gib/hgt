import GaloisForLFunctions.RHTower.Sieve.BlockCountAssembly
import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff

/-!
# The sub-critical power sum

`Σ_{r ≤ N} r^{-c} ≤ N^{1-c}/(1-c) + 1` for `0 < c < 1`, by comparison with the integral on each
unit step.  This is the `r`-sum of the growing term of the exponent budget; the decaying terms are
covered by the corpus's `sum_rpow_neg_tail_le`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

theorem rpow_neg_step_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ (-c) ≤ (((n : ℝ) + 1) ^ (1 - c) - (n : ℝ) ^ (1 - c)) / (1 - c) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hint : (∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-c))
      = (((n : ℝ) + 1) ^ (-c + 1) - (n : ℝ) ^ (-c + 1)) / (-c + 1) := by
    refine integral_rpow (Or.inr ⟨by linarith, ?_⟩)
    rw [Set.uIcc_of_le hle]
    intro hmem
    rw [Set.mem_Icc] at hmem
    linarith [hmem.1]
  have hmono : (∫ t in (n : ℝ)..((n : ℝ) + 1), ((n : ℝ) + 1) ^ (-c))
      ≤ ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-c) := by
    refine intervalIntegral.integral_mono_on hle intervalIntegrable_const ?_ ?_
    · refine intervalIntegral.intervalIntegrable_rpow ?_
      right
      rw [Set.uIcc_of_le hle]
      intro hmem
      rw [Set.mem_Icc] at hmem
      linarith [hmem.1]
    · intro t ht
      rw [Set.mem_Icc] at ht
      exact Real.rpow_le_rpow_of_nonpos (by linarith) ht.2 (by linarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hsimp : ((n : ℝ) + 1 - (n : ℝ)) * ((n : ℝ) + 1) ^ (-c) = ((n : ℝ) + 1) ^ (-c) := by ring
  rw [hsimp, hint] at hmono
  have hexp : -c + 1 = 1 - c := by ring
  rw [hexp] at hmono
  exact hmono

/-- **The sub-critical power sum.** -/
theorem sum_rpow_neg_subcritical_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 N, (r : ℝ) ^ (-c)) ≤ (N : ℝ) ^ (1 - c) / (1 - c) + 1 := by
  induction N with
  | zero => simp; positivity
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp
      linarith
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep := rpow_neg_step_le hc0 hc1 hN
      have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hden : (0 : ℝ) < 1 - c := by linarith
      have hid : (((N : ℝ) + 1) ^ (1 - c) - (N : ℝ) ^ (1 - c)) / (1 - c)
          = ((N : ℝ) + 1) ^ (1 - c) / (1 - c) - (N : ℝ) ^ (1 - c) / (1 - c) := by
        rw [sub_div]
      rw [hid] at hstep
      linarith [ih, hstep]

end

end RHTower.Sieve
