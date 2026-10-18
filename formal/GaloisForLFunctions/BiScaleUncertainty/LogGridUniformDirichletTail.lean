import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Uniform tails on the logarithmic integer grid

Absolute convergence at one real abscissa pays an exponential tail bound on the entire
right half-plane. The bound allows arbitrary complex coefficient phases and a separate
coefficient majorant; no frequency averaging or replacement of the signed series occurs.
-/

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The literal coefficient tail, with every coefficient at and above `b` retained. -/
def logGridTail (b : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if b ≤ n then a n else 0

/-- Pointwise scale separation, uniform in the imaginary part of `s`. -/
theorem norm_logGridTerm_le_geometric
    {a g : ℕ → ℂ} {b : ℕ} (hb : 1 ≤ b) {σ : ℝ} {s : ℂ}
    (hs : σ ≤ s.re) (ha : ∀ n < b, a n = 0)
    (hdom : ∀ n, ‖a n‖ ≤ ‖g n‖) (n : ℕ) :
    ‖LSeries.term a s n‖ ≤
      (b : ℝ) ^ (-(s.re - σ)) * ‖LSeries.term g (σ : ℂ) n‖ := by
  by_cases hn : n < b
  · rw [LSeries.norm_term_eq]
    simp only [ha n hn, norm_zero, zero_div, ite_self]
    positivity
  have hbn : b ≤ n := Nat.le_of_not_gt hn
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hd : 0 ≤ s.re - σ := sub_nonneg.mpr hs
  have hpow : (b : ℝ) ^ (s.re - σ) ≤ (n : ℝ) ^ (s.re - σ) :=
    Real.rpow_le_rpow hbR.le (by exact_mod_cast hbn) hd
  have hsplit : (n : ℝ) ^ σ * (n : ℝ) ^ (s.re - σ) = (n : ℝ) ^ s.re := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hden : (n : ℝ) ^ σ * (b : ℝ) ^ (s.re - σ) ≤ (n : ℝ) ^ s.re := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hnR.le _)
  have hpos : 0 < (n : ℝ) ^ σ * (b : ℝ) ^ (s.re - σ) :=
    mul_pos (Real.rpow_pos_of_pos hnR _) (Real.rpow_pos_of_pos hbR _)
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0,
    Complex.ofReal_re, Real.rpow_neg hbR.le]
  calc
    ‖a n‖ / (n : ℝ) ^ s.re ≤ ‖g n‖ / (n : ℝ) ^ s.re := by
      exact div_le_div_of_nonneg_right (hdom n) (Real.rpow_nonneg hnR.le _)
    _ ≤ ‖g n‖ / ((n : ℝ) ^ σ * (b : ℝ) ^ (s.re - σ)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hpos hden
    _ = ((b : ℝ) ^ (s.re - σ))⁻¹ * (‖g n‖ / (n : ℝ) ^ σ) := by ring

/-- A coefficient majorant at one abscissa supplies both admission and a full vertical-line
tail budget. The same majorant can serve an arbitrary family of signed coefficients. -/
theorem lSeries_geometric_bound_of_support
    {a g : ℕ → ℂ} {b : ℕ} (hb : 1 ≤ b) {σ : ℝ}
    (hg : LSeriesSummable g (σ : ℂ)) {s : ℂ} (hs : σ ≤ s.re)
    (ha : ∀ n < b, a n = 0) (hdom : ∀ n, ‖a n‖ ≤ ‖g n‖) :
    LSeriesSummable a s ∧
      ‖LSeries a s‖ ≤ (b : ℝ) ^ (-(s.re - σ)) *
        ∑' n : ℕ, ‖LSeries.term g (σ : ℂ) n‖ := by
  have hmajor := (summable_norm_iff.mpr hg).mul_left ((b : ℝ) ^ (-(s.re - σ)))
  have hbound := norm_logGridTerm_le_geometric hb hs ha hdom
  have habs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hmajor
  refine ⟨habs.of_norm, ?_⟩
  calc
    ‖LSeries a s‖ ≤ ∑' n : ℕ, ‖LSeries.term a s n‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' n : ℕ, (b : ℝ) ^ (-(s.re - σ)) * ‖LSeries.term g (σ : ℂ) n‖ :=
      habs.tsum_le_tsum hbound hmajor
    _ = _ := tsum_mul_left

/-- Deleting a finite head improves the rate to the first retained logarithmic node,
without changing any remaining coefficient. -/
theorem lSeries_logGridTail_bound
    {a g : ℕ → ℂ} {b : ℕ} (hb : 1 ≤ b) {σ : ℝ}
    (hg : LSeriesSummable g (σ : ℂ)) {s : ℂ} (hs : σ ≤ s.re)
    (hdom : ∀ n, ‖a n‖ ≤ ‖g n‖) :
    LSeriesSummable (logGridTail b a) s ∧
      ‖LSeries (logGridTail b a) s‖ ≤ (b : ℝ) ^ (-(s.re - σ)) *
        ∑' n : ℕ, ‖LSeries.term g (σ : ℂ) n‖ := by
  apply lSeries_geometric_bound_of_support hb hg hs
  · intro n hn
    simp [logGridTail, Nat.not_le_of_gt hn]
  · intro n
    by_cases hn : b ≤ n
    · simpa [logGridTail, hn] using hdom n
    · simp [logGridTail, hn]

end
end GaloisForLFunctions.BiScaleUncertainty
