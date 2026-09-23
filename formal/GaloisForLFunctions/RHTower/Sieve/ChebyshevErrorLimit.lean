import GaloisForLFunctions.RHTower.Sieve.ChebyshevFiveTerms

/-!
# The smoothed Chebyshev error is `o(N)`

Assembling the five term bounds and dividing by `N`, the whole contour error tends to zero relative
to the cutoff:

    ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·(2·arctan(T/w) - 2·arctan(-T/w)) ‖ / N → 0.

The main term's bracket tends to `2π`, so this says `∑ₙ Λ(n)w(n) = W(1) + o(N)` with `W(1)` the mass
of the cutoff, between `N` and `N + H`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction Filter Topology RHTower
open GaloisForLFunctions.HTGeometry

variable {N Cj M₀ δ₀ : ℝ}

/-- **The error as five decaying terms.** -/
theorem norm_tsum_vonMangoldt_sub_main_five_terms
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
      ≤ 1296 * Cj / zetaLowerA ^ (2 : ℕ)
            * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ (18 : ℕ) * (N * savingG N))
        + (8 + 54 * Cj) / zetaLowerA
            * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * (N * savingE N))
        + (324 * Cj + 8) * (N * savingG N)
        + ((M₀ + 1 / 9) * (8 + 54 * Cj) * (N * savingE N)
          + 2240 * (8 + 54 * Cj) / zetaLowerA
            * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * (N * savingE N)))
        + (324 * Cj * (M₀ + 1 / 9) * (N * savingG N)
          + 324 * Cj * 2240 / zetaLowerA
            * (((Real.log N) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * (N * savingG N))) := by
  refine le_trans (norm_tsum_vonMangoldt_sub_main_at_choice hN hL hNine hM₀ hCj hfit
    hlowzf hlowbox hdecay) ?_
  have h1 := term_tail_le (N := N) (Cj := Cj) hN hL hCj
  have h2 := term_left_dslope_le (N := N) (Cj := Cj) hN hL hCj
  have h3 := term_horizontal_dslope_le (N := N) (Cj := Cj) hN hL hCj
  have h4 := term_left_reg_le (N := N) (Cj := Cj) (M₀ := M₀) hN hL hCj hM₀
  have h5 := term_horizontal_reg_le (N := N) (Cj := Cj) (M₀ := M₀) hN hL hCj hM₀
  linarith

/-- **The majorant, divided by the cutoff, tends to zero.** -/
theorem tendsto_five_term_majorant (Cj M₀ : ℝ) :
    Tendsto (fun x : ℝ =>
        1296 * Cj / zetaLowerA ^ (2 : ℕ) * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (18 : ℕ) * savingG x)
          + (8 + 54 * Cj) / zetaLowerA
              * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * savingE x)
          + (324 * Cj + 8) * savingG x
          + ((M₀ + 1 / 9) * (8 + 54 * Cj) * savingE x
            + 2240 * (8 + 54 * Cj) / zetaLowerA
              * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * savingE x))
          + (324 * Cj * (M₀ + 1 / 9) * savingG x
            + 324 * Cj * 2240 / zetaLowerA
              * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * savingG x))) atTop (𝓝 0) := by
  have hE0 : Tendsto (fun x : ℝ => savingE x) atTop (𝓝 0) := by
    have h := tendsto_pow_savingE 0
    refine h.congr fun x => ?_
    rw [pow_zero, one_mul]
  have hG0 : Tendsto (fun x : ℝ => savingG x) atTop (𝓝 0) := by
    have h := tendsto_pow_savingG 0
    refine h.congr fun x => ?_
    rw [pow_zero, one_mul]
  have hE9 := tendsto_pow_savingE 9
  have hG9 := tendsto_pow_savingG 9
  have hG18 := tendsto_pow_savingG 18
  have hsum := ((((hG18.const_mul (1296 * Cj / zetaLowerA ^ (2 : ℕ))).add
    (hE9.const_mul ((8 + 54 * Cj) / zetaLowerA))).add
    (hG0.const_mul (324 * Cj + 8))).add
    (((hE0.const_mul ((M₀ + 1 / 9) * (8 + 54 * Cj))).add
      (hE9.const_mul (2240 * (8 + 54 * Cj) / zetaLowerA))))).add
    (((hG0.const_mul (324 * Cj * (M₀ + 1 / 9))).add
      (hG9.const_mul (324 * Cj * 2240 / zetaLowerA))))
  simp only [mul_zero, add_zero] at hsum
  exact hsum

/-- **The smoothed Chebyshev error is `o(N)`.** -/
theorem tendsto_norm_tsum_vonMangoldt_sub_main_div :
    Tendsto (fun x : ℝ =>
        ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
              * ((smoothWeight x (chebWidth x) (n : ℝ) : ℝ) : ℂ))
            - mellin (fun y : ℝ => ((smoothWeight x (chebWidth x) y : ℝ) : ℂ)) 1
                * (((2 * Real.arctan (chebHeight x / (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))
                    - 2 * Real.arctan (chebHeight x
                        / (-(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))) : ℝ)) : ℂ)‖ / x)
      atTop (𝓝 0) := by
  obtain ⟨Cj, hCj, hdecay⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨T₀, δ₀, M₀, hT₀, hδ₀, hM₀, hfitT, hlowzf, hlowbox⟩ := exists_chebyshev_contour_data
  have hlogtop : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hheighttop : Tendsto chebHeight atTop atTop := tendsto_chebHeight
  have hnonneg : ∀ᶠ x : ℝ in atTop, (0 : ℝ) ≤
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((smoothWeight x (chebWidth x) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun y : ℝ => ((smoothWeight x (chebWidth x) y : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (chebHeight x / (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))
                  - 2 * Real.arctan (chebHeight x
                      / (-(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))) : ℝ)) : ℂ)‖ / x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
            * ((smoothWeight x (chebWidth x) (n : ℝ) : ℝ) : ℂ))
          - mellin (fun y : ℝ => ((smoothWeight x (chebWidth x) y : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (chebHeight x / (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))
                  - 2 * Real.arctan (chebHeight x
                      / (-(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))) : ℝ)) : ℂ)‖ / x
        ≤ 1296 * Cj / zetaLowerA ^ (2 : ℕ) * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (18 : ℕ) * savingG x)
          + (8 + 54 * Cj) / zetaLowerA
              * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * savingE x)
          + (324 * Cj + 8) * savingG x
          + ((M₀ + 1 / 9) * (8 + 54 * Cj) * savingE x
            + 2240 * (8 + 54 * Cj) / zetaLowerA
              * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * savingE x))
          + (324 * Cj * (M₀ + 1 / 9) * savingG x
            + 324 * Cj * 2240 / zetaLowerA
              * (((Real.log x) ^ ((1 : ℝ) / 10)) ^ (9 : ℕ) * savingG x)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hlogtop.eventually_ge_atTop (1 : ℝ),
      hlogtop.eventually_ge_atTop ((Real.log 9) ^ (10 : ℕ)),
      hheighttop.eventually_ge_atTop T₀] with x hx hlx hninex hheightx
    have hx0 : (0 : ℝ) < x := by linarith
    have hfit : zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10) ≤ δ₀ := by
      have h := hfitT (chebHeight x) hheightx
      rwa [log_chebHeight_pow_nine (by linarith)] at h
    have hbound := norm_tsum_vonMangoldt_sub_main_five_terms (N := x) (Cj := Cj) (M₀ := M₀)
      (δ₀ := δ₀) hx hlx hninex hM₀ hCj hfit hlowzf hlowbox hdecay
    rw [div_le_iff₀ hx0]
    refine le_trans hbound (le_of_eq ?_)
    field_simp
  exact squeeze_zero' hnonneg hle (tendsto_five_term_majorant Cj M₀)

end RHTower.Sieve
