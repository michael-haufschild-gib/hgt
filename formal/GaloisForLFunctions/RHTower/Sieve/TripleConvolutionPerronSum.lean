import GaloisForLFunctions.RHTower.Sieve.PerronVerticalTripleBound
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound
import GaloisForLFunctions.RHTower.Sieve.ConvolutionSupport
import GaloisForLFunctions.RHTower.Sieve.ProductFirstMoment

/-!
# The partial sum of a triple convolution, through the sharp Perron formula

The Perron step of a threefold convolution needs three things, and all three are now available: the
convolution of finitely supported sequences is finitely supported, so the truncated Perron formula
applies with its half-integer error; the Dirichlet series of a convolution is the product of the series,
so the integrand is `L(A)L(B)L(g)·x^s/s`; and the vertical integral of that product is bounded by the
dyadic split against two prime-sieve mean squares and a pointwise bound on the third factor.

`‖∑_{n ≤ M_AM_BM_g} (A ⍟ (B ⍟ g))(n)‖ ≤ (Perron error) + (1/2π)·(triple analytic bound)`.

Nothing here restricts the third factor beyond finite support and a bound on its size on the line: it is
where the arithmetic of the multiplicative function under study enters, and where a distance saving would
be applied.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- A finitely supported Dirichlet series is bounded on a vertical line by the damped `ℓ¹` mass of its
coefficients. -/
theorem norm_LSeries_line_le_l1 {g : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ s) (σ t : ℝ) :
    ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ ∑ n ∈ s, ‖g n‖ * (n : ℝ) ^ (-σ) := by
  rw [← sum_mul_cpow_neg_eq_LSeries hs0 hsupp]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
  have hre : (-((σ : ℂ) + (t : ℝ) * I)).re = -σ := by simp
  rw [hre]

/-- The Dirichlet series of a threefold convolution of finitely supported sequences is the product of
the three series. -/
theorem LSeries_convolution_triple_of_support {A B g : ℕ → ℂ} {MA MB Mg : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg) (w : ℂ) :
    LSeries (LSeries.convolution A (LSeries.convolution B g)) w
      = LSeries A w * LSeries B w * LSeries g w := by
  have hBg : ∀ k : ℕ, (LSeries.convolution B g) k ≠ 0 → k ∈ Finset.Icc 1 (MB * Mg) :=
    fun k hk => convolution_mem_Icc_of_support_mul hBsupp hgsupp hk
  rw [LSeries_convolution' (LSeriesSummable_of_support hAsupp w)
      (LSeriesSummable_of_support hBg w),
    LSeries_convolution' (LSeriesSummable_of_support hBsupp w)
      (LSeriesSummable_of_support hgsupp w), mul_assoc]

/-- **The partial sum of a triple convolution.**  Two prime-supported factors through the sieve, a
finitely supported third factor through a bound on its size on the line, and the sharp Perron formula
with its half-integer truncation error. -/
theorem norm_sum_Icc_triple_le {A B g : ℕ → ℂ} {MA MB Mg N : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hAprime : ∀ n ∈ Finset.Icc 1 MA, A n ≠ 0 → n.Prime)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hBprime : ∀ n ∈ Finset.Icc 1 MB, B n ≠ 0 → n.Prime)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    (hMN : MA * (MB * Mg) ≤ N) (hN : 1 ≤ N)
    {Bc V σ t₀ : ℝ}
    (hBc : ∀ n, ‖(LSeries.convolution A (LSeries.convolution B g)) n‖ ≤ Bc) (hV : 0 ≤ V)
    (hgV : ∀ t : ℝ, ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V)
    (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 (MA * (MB * Mg)),
        (LSeries.convolution A (LSeries.convolution B g)) n‖
      ≤ 2 * ((N : ℝ) + 1) * Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (1 + Real.log ((MA * (MB * Mg) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound A B (Finset.Icc 1 MA) (Finset.Icc 1 MB) σ
                    ((N : ℝ) + 1 / 2) t₀ V zA YA zB YB K
                  + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst A (Finset.Icc 1 MA) σ YA
                            + sieveMeanSquareRate A (Finset.Icc 1 MA) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst B (Finset.Icc 1 MB) σ YB
                            + sieveMeanSquareRate B (Finset.Icc 1 MB) σ zB YB * t₀))) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hone : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hT : (0 : ℝ) < t₀ * 2 ^ K := by positivity
  have hTle : -(t₀ * 2 ^ K) ≤ t₀ * 2 ^ K := by linarith
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hA0 : (0 : ℕ) ∉ Finset.Icc 1 MA := by simp
  have hB0 : (0 : ℕ) ∉ Finset.Icc 1 MB := by simp
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 Mg := by simp
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  set T : ℝ := t₀ * 2 ^ K with hTdef
  set c : ℕ → ℂ := LSeries.convolution A (LSeries.convolution B g) with hc
  -- the convolution is supported in `[1, M_A M_B M_g]`
  have hBg : ∀ k : ℕ, (LSeries.convolution B g) k ≠ 0 → k ∈ Finset.Icc 1 (MB * Mg) :=
    fun k hk => convolution_mem_Icc_of_support_mul hBsupp hgsupp hk
  have hcsupp : ∀ k : ℕ, c k ≠ 0 → k ∈ Finset.Icc 1 (MA * (MB * Mg)) := by
    intro k hk
    rw [hc] at hk
    exact convolution_mem_Icc_of_support_mul hAsupp hBg hk
  have hcs0 : (0 : ℕ) ∉ Finset.Icc 1 (MA * (MB * Mg)) := by simp
  -- the Perron formula, with the polynomial recognised as the product of the three series
  have hP := norm_sum_Icc_sub_perron_integral_le (c := c) (M := MA * (MB * Mg)) (N := N)
    hMN hN hBc (σ := σ) (T := T) hσ hT
  have hbridge : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 (MA * (MB * Mg)), c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I)))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) := by
    intro t
    rw [sum_mul_cpow_neg_eq_LSeries hcs0 hcsupp, hc,
      LSeries_convolution_triple_of_support hAsupp hBsupp hgsupp]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
          * LSeries g ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    (fun t _ => hbridge t)] at hP
  -- the vertical integral
  have hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hg0 hgsupp σ
  have hanalytic := integral_symm_norm_perron_triple_le hA0 hAsupp hAprime hB0 hBsupp hBprime
    hσ0 hx ht₀ hV hgc hgV zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K
  have hnormint : ‖∫ t in (-T)..T,
        LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ ∫ t in (-T)..T,
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hTle
  have hscale : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ (1 / (2 * Real.pi))
          * (2 * perronVerticalProductBound A B (Finset.Icc 1 MA) (Finset.Icc 1 MB) σ x t₀ V
                zA YA zB YB K
              + (V * x ^ σ / σ)
                  * (Real.sqrt (sieveMeanSquareConst A (Finset.Icc 1 MA) σ YA
                        + sieveMeanSquareRate A (Finset.Icc 1 MA) σ zA YA * t₀)
                      * Real.sqrt (sieveMeanSquareConst B (Finset.Icc 1 MB) σ YB
                        + sieveMeanSquareRate B (Finset.Icc 1 MB) σ zB YB * t₀))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left (le_trans hnormint hanalytic) (by positivity)
  have htri : ‖∑ n ∈ Finset.Icc 1 (MA * (MB * Mg)), c n‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 (MA * (MB * Mg)), c n) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
              * LSeries g ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
          + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
              * LSeries g ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 (MA * (MB * Mg)), c n)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
          LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
          * LSeries g ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    simpa using this
  linarith [hP, hscale, htri]

end RHTower.Sieve
end
