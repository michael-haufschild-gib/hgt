import GaloisForLFunctions.RHTower.XiShiftedHardEdgeTrivialFourier
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerron

/-!
# The prime sum of the rational hard-edge test

Beyond the aperture the information cone gives `|ĝ²(log n)| ≤ 2(N+1)e^{2Nσ}·n^{-a·rate(σ)}·‖g‖₂²`,
so the completed prime term of the explicit formula is bounded by

`∑_n Λ(n)n^{-1/2}|ĝ²(log n)| ≤ 2(N+1)e^{2Nσ}·(∑_n Λ(n)n^{-2})·‖g‖₂²`

as soon as the total exponent `1/2 + a·rate(σ)` clears `2`.  The prime series is then dominated by
the absolutely convergent von Mangoldt tail at exponent two, uniformly in `a`, so the whole prime
contribution is coefficient-uniform: only the scaled degree enters.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- The absolutely convergent von Mangoldt tail at exponent two. -/
def routeUVonMangoldtTailConst : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))

theorem summable_vonMangoldt_rpow_two :
    Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
  have h := RHTower.Sieve.summable_vonMangoldt_rpow (σ := (2 : ℝ)) (by norm_num)
  refine h.congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]

theorem routeUVonMangoldtTailConst_nonneg : 0 ≤ routeUVonMangoldtTailConst := by
  refine tsum_nonneg fun n => ?_
  have h1 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  positivity

/-- **The uniform von Mangoldt tail.**  Beyond exponent two the von Mangoldt series is dominated by
its value there, uniformly. -/
theorem tsum_vonMangoldt_rpow_le {s : ℝ} (hs : 2 ≤ s) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s))
      ≤ routeUVonMangoldtTailConst := by
  have hsumm : Summable fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s) := by
    have h := RHTower.Sieve.summable_vonMangoldt_rpow (σ := s) (by linarith)
    refine h.congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
  refine hsumm.tsum_le_tsum ?_ summable_vonMangoldt_rpow_two
  intro n
  rcases Nat.lt_or_ge n 1 with hn | hn
  · interval_cases n
    · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    exact mul_le_mul_of_nonneg_left hpow ArithmeticFunction.vonMangoldt_nonneg

/-- The reciprocal square root as a real power. -/
theorem one_div_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) : 1 / Real.sqrt x = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hx, one_div]

/-- **(CSHC.13) The completed prime term.**  The prime sum of the rational hard-edge test is at most
a coefficient-uniform multiple of its `L²` mass. -/
theorem routeUHardEdgePrimeSum_le {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) {N : ℕ}
    (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N) {σ : ℝ} (hσ : 0 < σ)
    (hs : 2 ≤ 1 / 2 + a * routeUCayleyDecayRate σ) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n)
        * ‖routeUHardEdgeFourierSq a p (Real.log n)‖)
      ≤ (2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2 * routeUVonMangoldtTailConst)
          * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    positivity
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hterm : ∀ n : ℕ,
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n)
          * ‖routeUHardEdgeFourierSq a p (Real.log n)‖
        ≤ (K * I) * ((ArithmeticFunction.vonMangoldt n : ℝ)
            * (n : ℝ) ^ (-(1 / 2 + a * routeUCayleyDecayRate σ))) := by
    intro n
    rcases Nat.lt_or_ge n 1 with hn | hn
    · interval_cases n
      · simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      have hcone := norm_routeUHardEdgeFourierSq_le ha p hN hlog hσ
      rw [← hIdef] at hcone
      have hexp : Real.exp (-(a * Real.log (n : ℝ) * routeUCayleyDecayRate σ))
          = (n : ℝ) ^ (-(a * routeUCayleyDecayRate σ)) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
      rw [hexp] at hcone
      have hsplit : (n : ℝ) ^ (-(1 / 2 + a * routeUCayleyDecayRate σ))
          = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(a * routeUCayleyDecayRate σ)) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      have hsqrt : (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
          = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← one_div_sqrt_eq_rpow (le_of_lt hnpos), div_eq_mul_one_div]
      rw [hsqrt, hsplit, hKdef]
      have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hr : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hnpos.le _
      have hmul := mul_le_mul_of_nonneg_left hcone (mul_nonneg hΛ hr)
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
            * ‖routeUHardEdgeFourierSq a p (Real.log (n : ℝ))‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
              * ((2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2
                    * (n : ℝ) ^ (-(a * routeUCayleyDecayRate σ))) * I) := hmul
        _ = 2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2 * I
              * ((ArithmeticFunction.vonMangoldt n : ℝ)
                  * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(a * routeUCayleyDecayRate σ)))) := by
            ring
  have hsummL : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-(1 / 2 + a * routeUCayleyDecayRate σ)) := by
    have h := RHTower.Sieve.summable_vonMangoldt_rpow
      (σ := 1 / 2 + a * routeUCayleyDecayRate σ) (by linarith)
    refine h.congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
  have hsummLeft : Summable fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n)
        * ‖routeUHardEdgeFourierSq a p (Real.log n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hterm (hsummL.mul_left (K * I))
    have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hs0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    positivity
  refine le_trans (hsummLeft.tsum_le_tsum hterm (hsummL.mul_left (K * I))) ?_
  rw [tsum_mul_left, ← hIdef, hKdef]
  have htail := tsum_vonMangoldt_rpow_le hs
  have hcoef : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2 * I := by
    have : (0 : ℝ) ≤ I := hI0
    positivity
  calc 2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2 * I
        * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
            * (n : ℝ) ^ (-(1 / 2 + a * routeUCayleyDecayRate σ)))
      ≤ 2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2 * I * routeUVonMangoldtTailConst :=
        mul_le_mul_of_nonneg_left htail hcoef
    _ = 2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ 2 * routeUVonMangoldtTailConst * I := by
        ring

end RHTower

end
