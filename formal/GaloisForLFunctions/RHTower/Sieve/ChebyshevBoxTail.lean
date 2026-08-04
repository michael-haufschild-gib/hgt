import GaloisForLFunctions.RHTower.Sieve.ChebyshevBoxSubstitution
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSeriesBound

/-!
# The tail with the series bound substituted

The last quantity in the box estimate that still refers to the primes is the value of the von
Mangoldt series at the right abscissa.  Replacing it by `8/w²` leaves a bound in which every term is
built from the cutoff, the strip half-width and the truncation height alone.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction RHTower GaloisForLFunctions.HTGeometry

/-- **The Chebyshev estimate on the zero-free box, tail included.** -/
theorem norm_tsum_vonMangoldt_sub_full_main_le_box_tail {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {T Cc Cd δ₀ M₀ : ℝ} (hT : 9 ≤ T) (hM₀ : 0 ≤ M₀) (hCd : 0 ≤ Cd)
    (hfit : zetaLowerA / Real.log T ^ 9 ≤ δ₀)
    (hlowzf : ∀ c d : ℝ, 1 - δ₀ ≤ c → c ≤ 1 → 1 ≤ d →
      ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-9 : ℝ) 9, s ≠ 1 → riemannZeta s ≠ 0)
    (hlowbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 9 → ‖zetaLogDerivReg s‖ ≤ M₀)
    (hbdc : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 - zetaLowerA / Real.log T ^ 9 →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cc)
    (hbdd : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 + zetaLowerA / Real.log T ^ 9 →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cd) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((2 * Real.arctan (T / (zetaLowerA / Real.log T ^ 9))
                - 2 * Real.arctan (T / (-(zetaLowerA / Real.log T ^ 9))) : ℝ)) : ℂ)‖
      ≤ 2 * ((8 / (zetaLowerA / Real.log T ^ 9) ^ 2) * Cd) / T
        + ((zetaLowerA / Real.log T ^ 9)⁻¹
            * (2 * ((N + H) ^ (1 - zetaLowerA / Real.log T ^ 9)
                / (1 - zetaLowerA / Real.log T ^ 9)) + 2 * Cc)
          + 2 * ((2 * (zetaLowerA / Real.log T ^ 9)) * ((Cd / T ^ (1 + 1)
              + ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1‖) / T)))
        + (max M₀ (2240 / zetaLowerA * Real.log T ^ 9 + 1 / 9)
              * (2 * ((N + H) ^ (1 - zetaLowerA / Real.log T ^ 9)
                  / (1 - zetaLowerA / Real.log T ^ 9)) + 2 * Cc)
          + 2 * ((2 * (zetaLowerA / Real.log T ^ 9))
              * (max M₀ (2240 / zetaLowerA * Real.log T ^ 9 + 1 / 9) * (Cd / T ^ (1 + 1))))) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hlogT : 2 < Real.log T := by
    have hexp2 := exp_two_lt_eight
    have h1 : Real.log (Real.exp 2) < Real.log T :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hLT0 : (0 : ℝ) < Real.log T := by linarith
  have hw0 : (0 : ℝ) < zetaLowerA / Real.log T ^ 9 := by positivity
  have hw1 : zetaLowerA / Real.log T ^ 9 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : (2 : ℝ) ^ 9 ≤ Real.log T ^ 9 := pow_le_pow_left₀ (by norm_num) hlogT.le 9
    nlinarith
  have hTpos : (0 : ℝ) < T := by linarith
  refine le_trans (norm_tsum_vonMangoldt_sub_full_main_le_box hN hH hT hM₀ hfit hlowzf hlowbox
    hbdc hbdd) ?_
  have hseries : ∑' n : ℕ, (vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-(1 + zetaLowerA / Real.log T ^ 9))
      ≤ 8 / (zetaLowerA / Real.log T ^ 9) ^ 2 := by
    have h := tsum_vonMangoldt_rpow_neg_le (d := 1 + zetaLowerA / Real.log T ^ 9)
      (by linarith) (by linarith)
    have hsub : ((1 : ℝ) + zetaLowerA / Real.log T ^ 9) - 1
        = zetaLowerA / Real.log T ^ 9 := by ring
    rwa [hsub] at h
  have hmul : (∑' n : ℕ, (vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-(1 + zetaLowerA / Real.log T ^ 9))) * Cd
      ≤ (8 / (zetaLowerA / Real.log T ^ 9) ^ 2) * Cd :=
    mul_le_mul_of_nonneg_right hseries hCd
  have hdiv : 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-(1 + zetaLowerA / Real.log T ^ 9))) * Cd) / T
      ≤ 2 * ((8 / (zetaLowerA / Real.log T ^ 9) ^ 2) * Cd) / T := by
    gcongr
  linarith

end RHTower.Sieve
