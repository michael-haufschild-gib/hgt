import GaloisForLFunctions.RHTower.Sieve.ChebyshevBoxTail
import GaloisForLFunctions.RHTower.Sieve.ChebyshevDecayAtChoice
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLimitTool

/-!
# The estimate at the balanced parameters

Substituting `T = exp((log N)^{1/10})` and `H = N/exp((log N)^{1/20})` turns the box estimate into a
statement about `N` alone: the strip half-width becomes `A/(log N)^{9/10}` and the decay constants
become the explicit multiples of `N` computed at the balanced width.

The bracket on the left is `2·arctan(T/w) - 2·arctan(-T/w)`, which tends to `2π`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction RHTower GaloisForLFunctions.HTGeometry

/-- **The Chebyshev estimate at the balanced parameters.** -/
theorem norm_tsum_vonMangoldt_sub_main_at_choice {N : ℝ} {Cj M₀ δ₀ : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hNine : (Real.log 9) ^ (10 : ℕ) ≤ Real.log N)
    (hM₀ : 0 ≤ M₀) (hCj : 0 ≤ Cj)
    (hfit : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) ≤ δ₀)
    (hlowzf : ∀ c d : ℝ, 1 - δ₀ ≤ c → c ≤ 1 → 1 ≤ d →
      ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-9 : ℝ) 9, s ≠ 1 → riemannZeta s ≠ 0)
    (hlowbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 9 → ‖zetaLogDerivReg s‖ ≤ M₀)
    (hdecay : ∀ N' H' : ℝ, 0 < N' → 0 < H' → ∀ σ : ℝ, ∀ s : ℂ, 0 < s.re → s.re ≤ σ →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N' H' x : ℝ) : ℂ)) s‖
        ≤ Cj / H' ^ (1 + 1) * (N' + H' + 1) ^ (1 + 1 : ℕ) * (N' + H' + 1) ^ σ) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
          * ((smoothWeight N (chebWidth N) (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1
            * (((2 * Real.arctan (chebHeight N / (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
                - 2 * Real.arctan (chebHeight N
                    / (-(zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))) : ℝ)) : ℂ)‖
      ≤ 2 * ((8 / (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) ^ 2)
              * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
                * (N + chebWidth N + 1)
                  ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))) / chebHeight N
        + ((zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))⁻¹
            * (2 * ((N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
                / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
              + 2 * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
                * (N + chebWidth N + 1)
                  ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))))
          + 2 * ((2 * (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
              * (((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
                    * (N + chebWidth N + 1)
                      ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
                  / chebHeight N ^ (1 + 1)
                + ‖mellin (fun x : ℝ => ((smoothWeight N (chebWidth N) x : ℝ) : ℂ)) 1‖)
                / chebHeight N)))
        + (max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
              * (2 * ((N + chebWidth N) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
                  / (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
                + 2 * (Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
                  * (N + chebWidth N + 1)
                    ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))))
          + 2 * ((2 * (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
              * (max M₀ (2240 / zetaLowerA * (Real.log N) ^ ((9 : ℝ) / 10) + 1 / 9)
                * ((Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
                    * (N + chebWidth N + 1)
                      ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
                  / chebHeight N ^ (1 + 1))))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
  have hL0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hTnine : (9 : ℝ) ≤ chebHeight N := nine_le_chebHeight hNine
  have hlogpow : Real.log (chebHeight N) ^ 9 = (Real.log N) ^ ((9 : ℝ) / 10) :=
    log_chebHeight_pow_nine hL0
  have hCd0 : (0 : ℝ) ≤ Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
      * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) := by
    have hY0 : (0 : ℝ) < N + chebWidth N + 1 := by linarith
    have : (0 : ℝ) ≤ (N + chebWidth N + 1)
        ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) := Real.rpow_nonneg hY0.le _
    positivity
  have hmain := norm_tsum_vonMangoldt_sub_full_main_le_box_tail (N := N) (H := chebWidth N)
    (T := chebHeight N)
    (Cc := Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
      * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
    (Cd := Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
      * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)))
    (δ₀ := δ₀) (M₀ := M₀) hN0 hH0 hTnine hM₀ hCd0
    (by rw [hlogpow]; exact hfit) hlowzf hlowbox
    (fun s hs hsσ => by
      rw [hlogpow] at hsσ
      exact hdecay N (chebWidth N) hN0 hH0 _ s hs hsσ)
    (fun s hs hsσ => by
      rw [hlogpow] at hsσ
      exact hdecay N (chebWidth N) hN0 hH0 _ s hs hsσ)
  rw [hlogpow] at hmain
  exact hmain

end RHTower.Sieve
