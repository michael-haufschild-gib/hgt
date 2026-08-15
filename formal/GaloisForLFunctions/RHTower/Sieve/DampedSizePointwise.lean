import GaloisForLFunctions.RHTower.Sieve.GhsPerronDamped

/-!
# The damped size at a single frequency

The corpus's damped estimate for a truncated multiplicative Dirichlet series only ever uses the
distance bound at the frequency being evaluated.  Stating it that way — one frequency, one distance —
is what a twisted function needs: after twisting by `n^{-iτ}` the distance varies across the frequency
range and no single uniform bound holds near the antitwist centre.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The damped size of the truncated series at one frequency.**  The distance is used only at the
frequency of evaluation. -/
theorem norm_LSeries_truncSeq_line_le_damped_at {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    {L : ℕ} (hL : 1 ≤ L) {t : ℝ}
    (hfar : δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ dampedSize σ δ z L := by
  rw [dampedSize]
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℝ) * I).im = t := by simp
  have hs : ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := by
    intro h
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    exact absurd hre.symm (by linarith : σ ≠ 0)
  have hdamp := norm_tsum_twistedSummand_le_of_far hf1 hmul hbdd
    (s := (σ : ℂ) + (t : ℝ) * I) (by rw [hre]; exact hσ) hz hδ (by rw [him]; exact hfar)
  rw [hre] at hdamp
  have htail := norm_tsum_sub_sum_range_le_pow (f := f) hbdd
    (s := (σ : ℂ) + (t : ℝ) * I) (by rw [hre]; exact hσ) hL
  rw [hre] at htail
  rw [LSeries_truncSeq_eq_sum_range hs]
  have hsplit : (∑ n ∈ Finset.range (L + 1), twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
      = (∑' n : ℕ, twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
        - ((∑' n : ℕ, twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
            - ∑ n ∈ Finset.range (L + 1), twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n) := by
    ring
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ htail)
  exact hdamp

/-- **The trivial size of the truncated series.**  The damped size at zero distance. -/
theorem norm_LSeries_truncSeq_line_le_trivial_size {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z) {L : ℕ} (hL : 1 ≤ L) (t : ℝ) :
    ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ dampedSize σ 0 z L :=
  norm_LSeries_truncSeq_line_le_damped_at hf1 hmul hbdd hσ hz le_rfl hL
    (Real.sqrt_nonneg _)

end RHTower.Sieve
end
