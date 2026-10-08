import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeMasks
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseRationalBound

/-!
# Every fixed coprime mask inherits the rational source bound

Finite Fourier expansion is applied to the literal source coefficients, with
absolute Dirichlet convergence established before exchanging the finite sum.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem summable_sourceCosineCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (r : ℝ) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (sourceCosineCoeff lam r) s :=
  (sourceSquareCoeff_summable hW hs).norm.of_norm_bounded fun n =>
    LSeries.norm_term_le s (norm_sourceCosineCoeff_le lam r n)

private theorem coprimePart_sourceSquareCoeff_eq_sum (lam : ℕ → ℝ) (Q : ℕ) [NeZero Q]
    (a : ZMod Q → ℝ)
    (ha : ∀ n : ℕ, coprimeMask Q n =
      ∑ j : ZMod Q, a j * Real.cos (2 * Real.pi * ((n : ℝ) * (j.val / Q)))) :
    coprimePart Q (sourceSquareCoeff lam) =
      ∑ j : ZMod Q, (a j : ℂ) • sourceCosineCoeff lam (j.val / Q) := by
  funext n
  simp only [coprimePart, ha n, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sourceCosineCoeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Full positivity bounds the normalized actual convolution after any fixed coprime deletion. -/
theorem exists_abs_coprime_sourceSquare_normalized_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
        LSeries (coprimePart Q (sourceSquareCoeff lam)) (σ : ℂ)).re| ≤ C := by
  classical
  obtain ⟨a, ha⟩ := exists_coprimeMask_cosine_expansion Q
  have hq : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  choose C hC0 hC using fun j : ZMod Q =>
    exists_abs_sourceCosineSeries_rat_normalized_le hW j.val hq
  refine ⟨∑ j : ZMod Q, |a j| * C j,
    Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hC0 j)), ?_⟩
  have hall := Filter.eventually_all.mpr hC
  filter_upwards [self_mem_nhdsWithin, hall] with σ hσ hCσ
  have hseries : LSeries (coprimePart Q (sourceSquareCoeff lam)) (σ : ℂ) =
      ∑ j : ZMod Q, (a j : ℂ) * sourceCosineSeries lam (j.val / Q) (σ : ℂ) := by
    have hj (j : ZMod Q) : LSeriesSummable
        ((a j : ℂ) • sourceCosineCoeff lam ((j.val : ℝ) / Q)) (σ : ℂ) :=
      LSeriesSummable.smul (a j : ℂ)
        (summable_sourceCosineCoeff hW ((j.val : ℝ) / Q) (s := (σ : ℂ)) hσ)
    rw [coprimePart_sourceSquareCoeff_eq_sum lam Q a ha,
      LSeries_sum (fun (j : ZMod Q) _ => hj j)]
    simp only [LSeries_smul, sourceCosineSeries]
  have he : (σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
        LSeries (coprimePart Q (sourceSquareCoeff lam)) (σ : ℂ)).re =
      ∑ j : ZMod Q, a j * ((σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
        sourceCosineSeries lam (j.val / Q) (σ : ℂ)).re) := by
    rw [hseries, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj : Gammaℝ (σ : ℂ) * ((a j : ℂ) * sourceCosineSeries lam (j.val / Q) (σ : ℂ)) =
        (a j : ℂ) * (Gammaℝ (σ : ℂ) * sourceCosineSeries lam (j.val / Q) (σ : ℂ)) := by ring
    rw [hj]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [he]
  calc
    _ ≤ ∑ j : ZMod Q, |a j * ((σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
        sourceCosineSeries lam (j.val / Q) (σ : ℂ)).re)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCσ j) (abs_nonneg _)

end RHTower.WeilSingularArithmetic
