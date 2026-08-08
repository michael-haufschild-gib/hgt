import GaloisForLFunctions.RHTower.Sieve.GhsPerronSum
import GaloisForLFunctions.RHTower.Sieve.GhsStepFourTruncated

/-!
# The Perron step with the low range charged pointwise

The two prime polynomials may be charged their damped `ℓ¹` masses on the low range instead of their mean
squares.  For the outer weight `f(p)log p/log⌊N₀/p⌋` that mass is `∑_p (log p/log(N₀/p))p^{−σ}`, and for
the inner weight `f(q)log q` it is `∑_q (log q)q^{−σ}` — both a logarithm below the square roots of the
`n`-weighted masses the mean-square route charges, because the `ℓ¹` mass of a prime weight is a sum over
primes of `1/p` rather than of `1/p` against `n`.

The universal Perron law then converts either analytic estimate into a bound on the partial sum; only the
vertical integral changes.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

theorem dampedL1_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) : 0 ≤ dampedL1 a s σ := by
  rw [dampedL1]
  refine Finset.sum_nonneg fun n _ => ?_
  positivity

/-- A finitely supported Dirichlet series is bounded on a line by its damped `ℓ¹` mass. -/
theorem norm_LSeries_line_le_dampedL1 {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ t : ℝ) :
    ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)‖ ≤ dampedL1 a s σ := by
  rw [dampedL1]
  exact norm_LSeries_line_le_l1 hs0 hsupp σ t

/-- **The GHS Perron step with the low range charged pointwise.**  The flanks carry the sieve mean
squares; the low range carries the two damped `ℓ¹` masses. -/
theorem norm_sum_Icc_ghsTriple_l1_low_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L N : ℕ}
    (hprod : 1 ≤ N₀ * (M * L)) (hN : 1 ≤ N)
    {V σ t₀ : ℝ} (hV : 0 ≤ V) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ 2 * ((N : ℝ) + 1) * ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ V zA YA zB YB K
                  + (2 * t₀)
                      * (dampedL1 (ghsOuter f N₀) (Finset.Icc 1 N₀) σ
                          * dampedL1 (ghsInner f M) (Finset.Icc 1 M) σ
                          * (V * ((N : ℝ) + 1 / 2) ^ σ / σ))) := by
  have hA0 : (0 : ℕ) ∉ Finset.Icc 1 N₀ := by simp
  have hB0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 L := by simp
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hAsupp : ∀ n : ℕ, ghsOuter f N₀ n ≠ 0 → n ∈ Finset.Icc 1 N₀ :=
    fun _ hn => ghsOuter_mem_Icc hn
  have hBsupp : ∀ n : ℕ, ghsInner f M n ≠ 0 → n ∈ Finset.Icc 1 M :=
    fun _ hn => ghsInner_mem_Icc hn
  refine norm_sum_Icc_triple_of_analytic_le hAsupp hBsupp
    (fun _ hn => truncSeq_support hn) hN (norm_ghsTriple_trunc_le_uniform hf hprod) hσ ht₀ K ?_
  exact integral_symm_norm_perron_triple_l1_low_le hA0 hAsupp (fun _ _ hn => ghsOuter_support hn)
    hB0 hBsupp (fun _ _ hn => ghsInner_support hn) (by linarith) hx ht₀ hV
    (dampedL1_nonneg _ _ _) (dampedL1_nonneg _ _ _)
    (continuous_LSeries_line_of_support hg0 (fun _ hn => truncSeq_support hn) σ)
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV
    (fun t _ => norm_LSeries_line_le_dampedL1 hA0 hAsupp σ t)
    (fun t _ => norm_LSeries_line_le_dampedL1 hB0 hBsupp σ t)

/-- **The GHS Perron step with the low range charged pointwise and the near-diagonal truncation
error.**  The flanks carry the sieve mean squares, the low range the two damped `ℓ¹` masses, and the
truncation error is free of its factor `N`. -/
theorem norm_sum_Icc_ghsTriple_l1_low_near_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L N : ℕ}
    (hprod : 1 ≤ N₀ * (M * L))
    {V σ t₀ : ℝ} (hV : 0 ≤ V) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ V zA YA zB YB K
                  + (2 * t₀)
                      * (dampedL1 (ghsOuter f N₀) (Finset.Icc 1 N₀) σ
                          * dampedL1 (ghsInner f M) (Finset.Icc 1 M) σ
                          * (V * ((N : ℝ) + 1 / 2) ^ σ / σ))) := by
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
  exact integral_symm_norm_perron_triple_l1_low_le hA0 hAsupp (fun _ _ hn => ghsOuter_support hn)
    hB0 hBsupp (fun _ _ hn => ghsInner_support hn) (by linarith) hx ht₀ hV
    (dampedL1_nonneg _ _ _) (dampedL1_nonneg _ _ _)
    (continuous_LSeries_line_of_support hg0 (fun _ hn => truncSeq_support hn) σ)
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV
    (fun t _ => norm_LSeries_line_le_dampedL1 hA0 hAsupp σ t)
    (fun t _ => norm_LSeries_line_le_dampedL1 hB0 hBsupp σ t)

end RHTower.Sieve
end
