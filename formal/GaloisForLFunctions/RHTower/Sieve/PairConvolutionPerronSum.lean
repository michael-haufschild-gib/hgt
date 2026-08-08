import GaloisForLFunctions.RHTower.Sieve.PerronVerticalPairBound
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal
import GaloisForLFunctions.RHTower.Sieve.ConvolutionSupport
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound
import GaloisForLFunctions.RHTower.Sieve.ProductFirstMoment

/-!
# The partial sum of a pair convolution, through the sharp Perron formula

The same three ingredients as for a threefold convolution, at two factors: the convolution of finitely
supported sequences is finitely supported, the Dirichlet series of a convolution is the product of the
series, and the vertical integral of that product is bounded by the affine mean square of the first
factor against a pointwise bound on the second.

`‖∑_{n ≤ min(M_cM_g, N)} (c ⍟ g)(n)‖ ≤ (truncation error) + (1/2π)·(analytic bound)`.

Both inputs are parameters, so every pair of estimates composes through this one law; the two
instances built here are the near-diagonal truncation error and the general affine mean square, neither
of which asks anything of the support beyond finiteness.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The Perron step of a pair convolution, against any truncation error and any bound on its vertical
integral.**  The identification of the Dirichlet polynomial with the product of the two series and the
triangle inequality, with both estimates left as parameters. -/
theorem norm_sum_Icc_pair_of_error_and_analytic_le {c g : ℕ → ℂ} {Mc Mg N : ℕ}
    (hcsupp : ∀ n : ℕ, c n ≠ 0 → n ∈ Finset.Icc 1 Mc)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    {E P σ t₀ : ℝ} (ht₀ : 0 ≤ t₀) (K : ℕ)
    (hE : ‖(∑ n ∈ Finset.Icc 1 (min (Mc * Mg) N), (LSeries.convolution c g) n)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-(t₀ * 2 ^ K))..(t₀ * 2 ^ K),
                (∑ n ∈ Finset.Icc 1 (Mc * Mg),
                    (LSeries.convolution c g) n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                  * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                      / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E)
    (hP : (∫ t in (-(t₀ * 2 ^ K))..(t₀ * 2 ^ K),
        ‖LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                / ((σ : ℂ) + (t : ℝ) * I))‖) ≤ P) :
    ‖∑ n ∈ Finset.Icc 1 (min (Mc * Mg) N), (LSeries.convolution c g) n‖
      ≤ E + (1 / (2 * Real.pi)) * P := by
  have hTle : -(t₀ * 2 ^ K) ≤ t₀ * 2 ^ K := by
    have : (0 : ℝ) ≤ t₀ * 2 ^ K := by positivity
    linarith
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  set T : ℝ := t₀ * 2 ^ K with hTdef
  set d : ℕ → ℂ := LSeries.convolution c g with hd
  have hdsupp : ∀ k : ℕ, d k ≠ 0 → k ∈ Finset.Icc 1 (Mc * Mg) := by
    intro k hk
    rw [hd] at hk
    exact convolution_mem_Icc_of_support_mul hcsupp hgsupp hk
  have hds0 : (0 : ℕ) ∉ Finset.Icc 1 (Mc * Mg) := by simp
  have hPerron := hE
  have hbridge : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 (Mc * Mg), d n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I)))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) := by
    intro t
    rw [sum_mul_cpow_neg_eq_LSeries hds0 hdsupp, hd,
      LSeries_convolution' (LSeriesSummable_of_support hcsupp _)
        (LSeriesSummable_of_support hgsupp _)]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    (fun t _ => hbridge t)] at hPerron
  have hnormint : ‖∫ t in (-T)..T,
        LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ ∫ t in (-T)..T,
        ‖LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hTle
  have hscale : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ (1 / (2 * Real.pi)) * P := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left (le_trans hnormint hP) (by positivity)
  have htri : ‖∑ n ∈ Finset.Icc 1 (min (Mc * Mg) N), d n‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 (min (Mc * Mg) N), d n) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
          + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 (min (Mc * Mg) N), d n)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
          LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries c ((σ : ℂ) + (t : ℝ) * I) * LSeries g ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    simpa using this
  linarith [hPerron, hscale, htri]

/-- **The Perron step of a pair convolution at the near-diagonal truncation error and the general
affine mean square.**  Neither estimate asks anything of the two supports beyond finiteness: no
primality, no sieve level, and no lower bound on the cutoff. -/
theorem norm_sum_Icc_pair_general_near_le {c g : ℕ → ℂ} {Mc Mg N : ℕ}
    (hcsupp : ∀ n : ℕ, c n ≠ 0 → n ∈ Finset.Icc 1 Mc)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    {Bc V σ t₀ : ℝ} (hBc : ∀ n, ‖(LSeries.convolution c g) n‖ ≤ Bc) (hV : 0 ≤ V)
    (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (Mc * Mg) N), (LSeries.convolution c g) n‖
      ≤ Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((Mc * Mg : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * perronVerticalPairBound σ ((N : ℝ) + 1 / 2) t₀ V
                  (generalMeanSquareConst c (Finset.Icc 1 Mc) σ)
                  (generalMeanSquareRate c (Finset.Icc 1 Mc) σ) K := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hT : (0 : ℝ) < t₀ * 2 ^ K := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hc0 : (0 : ℕ) ∉ Finset.Icc 1 Mc := by simp
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 Mg := by simp
  refine norm_sum_Icc_pair_of_error_and_analytic_le (σ := σ) (t₀ := t₀) hcsupp hgsupp
    (by linarith) K ?_ ?_
  · exact norm_sum_Icc_sub_perron_integral_near_le (c := LSeries.convolution c g)
      (M := Mc * Mg) (N := N) hBc (σ := σ) (T := t₀ * 2 ^ K) hσ hT
  · exact integral_symm_norm_perron_pair_general_le hc0 hcsupp (by linarith) hx ht₀ hV
      (continuous_LSeries_line_of_support hg0 hgsupp σ) K hgV

end RHTower.Sieve
end
