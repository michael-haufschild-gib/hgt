import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal

/-!
# Sharp Perron formula for a short interval

Subtracting the two half-integer prefix formulae produces the exact short-interval kernel.  The
error is the sum of the two near-diagonal errors, so no global minimum separation or artificial
factor of the cutoff is introduced.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set

/-- Truncated Perron integral selecting coefficients below `N + 1/2`. -/
def perronPrefixIntegral (c : ℕ → ℂ) (M N : ℕ) (σ T : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
    (∑ n ∈ Finset.Icc 1 M, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
      * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
          / ((σ : ℂ) + (t : ℝ) * I))

/-- Explicit near-diagonal error attached to one prefix cutoff. -/
def perronNearError (B : ℝ) (M N : ℕ) (σ T : ℝ) : ℝ :=
  B * ((N : ℝ) + 1 / 2) ^ σ
    * (5 * (1 + Real.log M) + 4 * (1 + Real.log N)) / (Real.pi * T)

theorem norm_sum_Icc_sub_perronPrefixIntegral_near_le
    {c : ℕ → ℂ} {M N : ℕ} {B σ T : ℝ}
    (hB : ∀ n, ‖c n‖ ≤ B) (hσ : 1 ≤ σ) (hT : 0 < T) :
    ‖(∑ n ∈ Finset.Icc 1 (min M N), c n) - perronPrefixIntegral c M N σ T‖ ≤
      perronNearError B M N σ T := by
  simpa [perronPrefixIntegral, perronNearError] using
    (norm_sum_Icc_sub_perron_integral_near_le
      (c := c) (M := M) (N := N) hB hσ hT)

/-- **Two-cutoff short-interval Perron formula.** -/
theorem norm_sum_Icc_sub_sum_Icc_sub_perronInterval_le
    {c : ℕ → ℂ} {M A B : ℕ} {K σ T : ℝ}
    (hK : ∀ n, ‖c n‖ ≤ K) (hσ : 1 ≤ σ) (hT : 0 < T) :
    ‖((∑ n ∈ Finset.Icc 1 (min M B), c n) -
          ∑ n ∈ Finset.Icc 1 (min M A), c n) -
        (perronPrefixIntegral c M B σ T - perronPrefixIntegral c M A σ T)‖
      ≤ perronNearError K M B σ T + perronNearError K M A σ T := by
  have hB := norm_sum_Icc_sub_perronPrefixIntegral_near_le
    (c := c) (M := M) (N := B) hK hσ hT
  have hA := norm_sum_Icc_sub_perronPrefixIntegral_near_le
    (c := c) (M := M) (N := A) hK hσ hT
  have hid :
      ((∑ n ∈ Finset.Icc 1 (min M B), c n) -
          ∑ n ∈ Finset.Icc 1 (min M A), c n) -
        (perronPrefixIntegral c M B σ T - perronPrefixIntegral c M A σ T) =
      ((∑ n ∈ Finset.Icc 1 (min M B), c n) - perronPrefixIntegral c M B σ T) -
        ((∑ n ∈ Finset.Icc 1 (min M A), c n) - perronPrefixIntegral c M A σ T) := by
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add hB hA)

end RHTower.Sieve
