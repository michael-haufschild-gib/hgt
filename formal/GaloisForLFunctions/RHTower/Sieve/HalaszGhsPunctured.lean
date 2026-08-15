import GaloisForLFunctions.RHTower.Sieve.GhsPerronPunctured
import GaloisForLFunctions.RHTower.Sieve.HalaszGhsSharpCutoff

/-!
# The sharp Halász bound with one exceptional frequency window

The two halves of the Granville–Harper–Soundararajan argument compose exactly as before when the size of
the third factor is only known away from one unit window: the paper half is untouched, and the analytic
half acquires the single escape term of the punctured Perron step.  This is the form a twisted
multiplicative function needs, because twisting moves the trivial frequency of the Euler product to the
twist and no uniform distance bound survives there.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **A Halász-type mean value bound with one exceptional frequency window.**  Away from the window at
height `c` the third factor is charged the size `V`; on the window it is charged `V_triv` against the
kernel weight `1/(|c|−1)`. -/
theorem norm_sum_Icc_mul_log_le_punctured_near {f : ℕ → ℂ}
    (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {N : ℕ} (hN : 2 ≤ N)
    {σ t₀ V Vtr c : ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V) (hVtr : 0 ≤ Vtr) (K : ℕ)
    (hc : 1 < |c|)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K → 1 ≤ |t - c| →
      ‖LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V)
    (hgtr : ∀ t : ℝ, ‖LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ Vtr)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
          + (9 + RHTower.Mertens.mertensTail)
              * ((N : ℝ)
                  * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                        / Real.log 2)
                      * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
        + (((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
                * (((N : ℝ) + 1 / 2)) ^ σ
                * (5 * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
                / (Real.pi * (t₀ * 2 ^ K))
            + (1 / (2 * Real.pi))
                * ((2 * perronVerticalProductBound (ghsOuter f N) (ghsInner f N)
                        (Finset.Icc 1 N) (Finset.Icc 1 N) σ ((N : ℝ) + 1 / 2) t₀ V zA YA zB YB K
                      + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                          * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N) (Finset.Icc 1 N) σ YA
                                + sieveMeanSquareRate (ghsOuter f N) (Finset.Icc 1 N) σ zA YA * t₀)
                              * Real.sqrt (sieveMeanSquareConst (ghsInner f N) (Finset.Icc 1 N) σ YB
                                + sieveMeanSquareRate (ghsInner f N) (Finset.Icc 1 N) σ zB YB
                                    * t₀)))
                    + 2 * (dampedL1 (ghsOuter f N) (Finset.Icc 1 N) σ
                            * dampedL1 (ghsInner f N) (Finset.Icc 1 N) σ
                            * (Vtr * (((N : ℝ) + 1 / 2) ^ σ / (|c| - 1)))))) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hNcube : N ≤ N * (N * N) := by
    calc N = N * 1 := by ring
      _ ≤ N * (N * N) := Nat.mul_le_mul_left N (by nlinarith)
  have hprod : 1 ≤ N * (N * N) := le_trans hN1 hNcube
  have hpaper := norm_sum_Icc_mul_log_sub_ghsTriple_le hf hbdd N hN
  have hanalytic := norm_sum_Icc_ghsTriple_punctured_near_le (f := f) hbdd
    (N₀ := N) (M := N) (L := N) (N := N) hprod hV hVtr hσ.le ht₀
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hc hgV hgtr
  rw [min_eq_right hNcube] at hanalytic
  rw [← sum_Icc_convolution_triple_truncSeq_eq (le_refl N)] at hanalytic
  have hsplit : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ n ∈ Finset.Icc 1 N,
              (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖
          + ‖∑ n ∈ Finset.Icc 1 N,
              (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N,
          (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
      (∑ n ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
    simpa using this
  have hnorm : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      = ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
  rw [hnorm] at hsplit
  linarith [hsplit, hpaper, hanalytic]

end RHTower.Sieve
end
