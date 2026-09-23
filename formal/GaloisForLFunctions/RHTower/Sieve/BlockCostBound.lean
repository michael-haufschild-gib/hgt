import GaloisForLFunctions.RHTower.Sieve.LinearRangeEstimate

/-!
# The block cost, without logarithms

Both logarithms in the block cost are bounded by their arguments, `log(1+x) ≤ x`, so

    blockCost L Y ε M₁ M₂ W ≤ 2M₁·(L/Y) + 4M₂/(π²W) + 2(εL+1)²·ε .

In this form the three contributions are visible as what they are: the cancellation term, the
frequency-tail term, and the excess term.  The first two decrease in `Y` and `W`, the third increases
in `ε`, and the numerical step of the argument is the balance between them.
-/

namespace RHTower.Sieve

/-- **The block cost without logarithms.** -/
theorem blockCost_le {L Y ε M₁ M₂ W : ℝ} (hL : 0 ≤ L) (hY : 0 < Y) (hε : 0 ≤ ε) (hW : 0 < W)
    (hM₁ : 0 ≤ M₁) :
    blockCost L Y ε M₁ M₂ W
      ≤ 2 * M₁ * (L / Y) + 4 * M₂ / (Real.pi ^ (2 : ℕ) * W) + 2 * (ε * L + 1) ^ (2 : ℕ) * ε := by
  have hLY : 0 ≤ L / Y := by positivity
  have hlog1 : Real.log (1 + L / Y) ≤ L / Y := by
    have := Real.log_le_sub_one_of_pos (x := 1 + L / Y) (by linarith)
    linarith
  have hlog2 : Real.log (1 + ε) ≤ ε := by
    have := Real.log_le_sub_one_of_pos (x := 1 + ε) (by linarith)
    linarith
  have hsq : (0 : ℝ) ≤ (ε * L + 1) ^ (2 : ℕ) := sq_nonneg _
  rw [blockCost]
  have h1 : M₁ * Real.log (1 + L / Y) ≤ M₁ * (L / Y) :=
    mul_le_mul_of_nonneg_left hlog1 hM₁
  have h2 : 2 * (ε * L + 1) ^ (2 : ℕ) * Real.log (1 + ε) ≤ 2 * (ε * L + 1) ^ (2 : ℕ) * ε :=
    mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have h3 : (2 : ℝ) * (M₂ * (2 / (Real.pi ^ (2 : ℕ) * W))) = 4 * M₂ / (Real.pi ^ (2 : ℕ) * W) := by
    field_simp
    ring
  linarith [h1, h2, h3]

end RHTower.Sieve
