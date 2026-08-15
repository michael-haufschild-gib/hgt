import GaloisForLFunctions.RHTower.Sieve.GhsPerronL1Low
import GaloisForLFunctions.RHTower.Sieve.PerronAntitwistEscape

/-!
# The GHS Perron step with one exceptional frequency window

The third factor of the GHS triple convolution enters the Perron step only through its size on the
integration line.  When that size is small everywhere except on a unit window at height `c` — which is
what twisting by `n^{-ic}` produces — the window is charged the trivial size against the Perron kernel
there, `x^σ/(|c|−1)`, and the two prime polynomials against their damped `ℓ¹` masses.  The result is the
ordinary damped Perron bound plus one escape term of order `1/|c|`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The GHS Perron step with one exceptional window.**  The flanks and the low range carry the damped
size `V`; the exceptional window at height `c` carries the trivial size `V_triv` against the two damped
`ℓ¹` masses and the kernel weight `1/(|c|−1)`. -/
theorem norm_sum_Icc_ghsTriple_punctured_near_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L N : ℕ}
    (hprod : 1 ≤ N₀ * (M * L))
    {V Vtr σ t₀ c : ℝ} (hV : 0 ≤ V) (hVtr : 0 ≤ Vtr) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ)
    (hc : 1 < |c|)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K → 1 ≤ |t - c| →
      ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V)
    (hgtr : ∀ t : ℝ, ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ Vtr) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * ((2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                      (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ V zA YA zB YB K
                    + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                        * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N₀) (Finset.Icc 1 N₀) σ YA
                              + sieveMeanSquareRate (ghsOuter f N₀) (Finset.Icc 1 N₀) σ zA YA * t₀)
                            * Real.sqrt (sieveMeanSquareConst (ghsInner f M) (Finset.Icc 1 M) σ YB
                              + sieveMeanSquareRate (ghsInner f M) (Finset.Icc 1 M) σ zB YB * t₀)))
                  + 2 * (dampedL1 (ghsOuter f N₀) (Finset.Icc 1 N₀) σ
                          * dampedL1 (ghsInner f M) (Finset.Icc 1 M) σ
                          * (Vtr * (((N : ℝ) + 1 / 2) ^ σ / (|c| - 1))))) := by
  have hA0 : (0 : ℕ) ∉ Finset.Icc 1 N₀ := by simp
  have hB0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 L := by simp
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hAsupp : ∀ n : ℕ, ghsOuter f N₀ n ≠ 0 → n ∈ Finset.Icc 1 N₀ :=
    fun _ hn => ghsOuter_mem_Icc hn
  have hBsupp : ∀ n : ℕ, ghsInner f M n ≠ 0 → n ∈ Finset.Icc 1 M :=
    fun _ hn => ghsInner_mem_Icc hn
  refine norm_sum_Icc_triple_of_analytic_near_le hAsupp hBsupp
    (fun _ hn => truncSeq_support hn) (norm_ghsTriple_trunc_le_uniform hf hprod) hσ ht₀ K ?_
  rw [perronVerticalProductBound_eq]
  exact integral_symm_norm_perron_triple_punctured_affine_le hA0 hAsupp hB0 hBsupp
    (by linarith) hx ht₀ hV hVtr (dampedL1_nonneg _ _ _) (dampedL1_nonneg _ _ _)
    (sieveMeanSquareConst_nonneg _ _ σ hlogA) (sieveMeanSquareRate_nonneg _ _ σ hzA hlogA)
    (sieveMeanSquareConst_nonneg _ _ σ hlogB) (sieveMeanSquareRate_nonneg _ _ σ hzB hlogB)
    (continuous_LSeries_line_of_support hg0 (fun _ hn => truncSeq_support hn) σ)
    (fun U hU => integral_Icc_normSq_LSeries_le_affine hA0 hAsupp
      (fun _ _ hn => ghsOuter_support hn) σ hU zA YA hYA hYzA hzA hlogA)
    (fun U hU => integral_Icc_normSq_LSeries_le_affine hB0 hBsupp
      (fun _ _ hn => ghsInner_support hn) σ hU zB YB hYB hYzB hzB hlogB)
    K hc hgV hgtr
    (fun t => norm_LSeries_line_le_dampedL1 hA0 hAsupp σ t)
    (fun t => norm_LSeries_line_le_dampedL1 hB0 hBsupp σ t)

end RHTower.Sieve
end
