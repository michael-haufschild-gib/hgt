import GaloisForLFunctions.RHTower.Sieve.PerronChebyshevIdentification

/-!
# The master inequality for the Chebyshev error

Combining the Perron formula at the half-integer cutoff with the contour shift gives the Chebyshev
error as the Perron truncation error plus the three sides of the rectangle, with no analytic input
left implicit.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

noncomputable section

/-- The Perron error series converges. -/
theorem summable_perron_error {c : ℕ → ℂ} {x σ T : ℝ} (hx : 0 < x) (hσ : 0 < σ) (hT : 0 < T)
    (hconv : Summable (fun n : ℕ => ‖c n‖ * (x / n) ^ σ)) :
    Summable (fun n : ℕ => ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|))) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set F : ℕ → ℝ := fun n => ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)) with hF
  have hsplit : F = (fun n : ℕ => if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then F n else 0)
      + fun n : ℕ => if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0 else F n := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  rw [hsplit]
  refine Summable.add ?_ ?_
  · refine summable_of_hasFiniteSupport ?_
    refine Set.Finite.subset (Set.finite_Icc 0 ⌈2 * x⌉₊) ?_
    intro n hn
    simp only [Function.mem_support] at hn
    by_cases hnear : x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x
    · simp only [Set.mem_Icc]
      refine ⟨Nat.zero_le n, ?_⟩
      have : (n : ℝ) ≤ (⌈2 * x⌉₊ : ℝ) := le_trans hnear.2 (Nat.le_ceil _)
      exact_mod_cast this
    · exact absurd (if_neg hnear) hn
  · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (hconv.mul_left (1 / (Real.pi * T * Real.log 2)))
    · split_ifs with h
      · exact le_rfl
      · rw [hF]
        have : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
        positivity
    · have hmaj := perron_error_far_le (c := c) (x := x) (σ := σ) (T := T) hx hσ hT hconv
      have hpt : (if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then 0 else F n)
          ≤ (1 / (Real.pi * T * Real.log 2)) * (‖c n‖ * (x / n) ^ σ) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have hz : (x / ((0 : ℕ) : ℝ)) = 0 := by simp
          rw [hF]
          simp only [hz, Real.zero_rpow hσ.ne']
          split_ifs <;> simp
        · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hxn : (0 : ℝ) < x / n := div_pos hx hn0
          have hxσ : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg hxn.le σ
          split_ifs with hnear
          · positivity
          · have hcase : x / n ≤ 1 / 2 ∨ 2 ≤ x / n := by
              by_contra hcon
              push Not at hcon
              have h1 : x < 2 * (n : ℝ) := by
                have h := hcon.2
                rw [div_lt_iff₀ hn0] at h
                linarith
              have h2 : (n : ℝ) < 2 * x := by
                have h := hcon.1
                rw [lt_div_iff₀ hn0] at h
                linarith
              exact hnear ⟨by linarith, by linarith⟩
            have hkey := log_two_le_abs_log hxn hcase
            have hden : (0 : ℝ) < Real.pi * T * Real.log 2 := by
              have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
              positivity
            have hden2 : Real.pi * T * Real.log 2 ≤ Real.pi * T * |Real.log (x / n)| := by
              have hpT : (0 : ℝ) < Real.pi * T := by positivity
              nlinarith [hkey, hpT]
            have hstep : (x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)
                ≤ (x / n) ^ σ / (Real.pi * T * Real.log 2) := by gcongr
            have hid : (1 / (Real.pi * T * Real.log 2)) * (‖c n‖ * (x / n) ^ σ)
                = ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * Real.log 2)) := by ring
            rw [hF, hid]
            exact mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
      exact hpt

/-- **The master inequality.**  Under the Riemann hypothesis the Chebyshev error at a half-integer
cutoff is the Perron truncation error plus the three sides of the shifted rectangle. -/
theorem norm_chebyshev_sub_halfInt_le (hRH : RiemannHypothesis) {N : ℕ} {σ₁ σ₀ T : ℝ}
    (hσ₁ : 1 / 2 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT : 0 < T) :
    |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - ((N : ℝ) + 1 / 2)|
      ≤ (∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖
            * ((((N : ℝ) + 1 / 2) / n) ^ σ₀
              / (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)))
        + (1 / (2 * Real.pi))
          * (‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
                * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) σ₁ (-T) T‖
            + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
                * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) σ₁ σ₀ T‖
            + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
                * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) σ₁ σ₀ (-T)‖) := by
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hσ₀0 : (0 : ℝ) < σ₀ := by linarith
  have hne : ∀ n : ℕ, (n : ℝ) ≠ (N : ℝ) + 1 / 2 := by
    intro n hcon
    have h2 : (2 * n : ℤ) = 2 * (N : ℤ) + 1 := by
      have : (2 * (n : ℝ)) = 2 * (N : ℝ) + 1 := by linarith
      exact_mod_cast this
    omega
  have hconv := summable_vonMangoldt_perron hx hσ₀
  have hdef := summable_perron_error (c := fun n : ℕ => ((Λ n : ℝ) : ℂ))
    hx hσ₀0 hT hconv
  have hperron := norm_tsum_lt_sub_perron_integral_le
    (c := fun n : ℕ => ((Λ n : ℝ) : ℂ)) (by simp) hx hne hσ₀0 hT hconv hdef
  rw [tsum_indicator_vonMangoldt_eq N,
    perron_integral_eq_vIntegral' (x := (N : ℝ) + 1 / 2) (σ := σ₀) (T := T) hσ₀] at hperron
  have hshift := norm_vIntegral'_perron_sub_le hRH (x := (N : ℝ) + 1 / 2) hx hσ₁ hσ₁1 hσ₀ hT
  have htri : ‖((∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) : ℝ) : ℂ) - (((N : ℝ) + 1 / 2 : ℝ) : ℂ)‖
      ≤ _ + _ := norm_sub_le_norm_sub_add_norm_sub _
        (VIntegral' (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
          * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) σ₀ (-T) T) _
  have hreal : ‖((∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) : ℝ) : ℂ) - (((N : ℝ) + 1 / 2 : ℝ) : ℂ)‖
      = |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - ((N : ℝ) + 1 / 2)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hreal] at htri
  linarith [htri, hperron, hshift]

end

end RHTower.Sieve
