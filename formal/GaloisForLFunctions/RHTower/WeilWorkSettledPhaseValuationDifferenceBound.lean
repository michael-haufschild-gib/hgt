import GaloisForLFunctions.RHTower.WeilWorkSettledPhasePrimeDifference
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationCosineBound

/-!
# Bounded normalized Mellin values survive finite local differences

Point-mass convolution multiplies a real-axis L-series by a positive scalar at
most one. Applying this twice to the actual source isolates every valuation
class of the logarithmic deviation behind a fixed coprime square factor.
-/

open Complex Set Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem normalizedCoefficientMellin_point {p : ℕ} (hp : p ≠ 0)
    {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f (σ : ℂ)) :
    normalizedCoefficientMellin (LSeries.convolution (dirichletPoint p) f) σ =
      (p : ℝ) ^ (-σ) * normalizedCoefficientMellin f σ := by
  rw [normalizedCoefficientMellin,
    LSeries_convolution' (summable_dirichletPoint p (σ : ℂ)) hf,
    LSeries_dirichletPoint hp]
  have hr : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg p)]
    simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [hr]
  have he : Gammaℝ (σ : ℂ) * ((((p : ℝ) ^ (-σ) : ℝ) : ℂ) * LSeries f (σ : ℂ)) =
      (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * (Gammaℝ (σ : ℂ) * LSeries f (σ : ℂ)) := by ring
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    normalizedCoefficientMellin]
  ring

theorem boundedNormalizedMellin_point {p : ℕ} (hp : p ≠ 0) {f : ℕ → ℂ}
    (hsf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hf : BoundedNormalizedMellin f) :
    BoundedNormalizedMellin (LSeries.convolution (dirichletPoint p) f) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hf] with σ hσ hf
  rw [normalizedCoefficientMellin_point hp (hsf σ hσ), abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
  have hσ1 : 1 < σ := hσ
  have hpow : (p : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  exact (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans (by simpa using hf)

theorem summable_primeDifference (p : ℕ) {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) : LSeriesSummable (primeDifference p f) s :=
  hf.sub ((summable_dirichletPoint p s).convolution hf)

theorem boundedNormalizedMellin_valuation_primeDifference {p : ℕ} (hp : p ≠ 0)
    {f : ℕ → ℂ} (hsf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hf : ∀ k : ℕ, BoundedNormalizedMellin (valuationPart p k f)) (k : ℕ) :
    BoundedNormalizedMellin (valuationPart p k (primeDifference p f)) := by
  cases k with
  | zero => simpa only [valuationPart_primeDifference_zero] using hf 0
  | succ k =>
    rw [valuationPart_primeDifference_succ hp]
    exact boundedNormalizedMellin_sub
      (fun σ hσ => summable_valuationPart p (k + 1) (hsf σ hσ))
      (fun σ hσ => (summable_dirichletPoint p (σ : ℂ)).convolution
        (summable_valuationPart p k (hsf σ hσ)))
      (hf (k + 1))
      (boundedNormalizedMellin_point hp
        (fun σ hσ => summable_valuationPart p k (hsf σ hσ)) (hf k))

/-- Full positivity controls each logarithmic-deviation stratum after the
fixed coprime square smoothing. -/
theorem boundedNormalizedMellin_valuation_deviation_square {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    BoundedNormalizedMellin (LSeries.convolution
      (LSeries.convolution
        (valuationPart p k (WeilHerglotz.lamC lam -
          fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (coprimePart p 1))
      (coprimePart p 1)) := by
  have hs (σ : ℝ) (hσ : 1 < σ) := sourceSquareCoeff_summable hW (s := (σ : ℂ)) hσ
  have h₁ := boundedNormalizedMellin_valuation_primeDifference hp.ne_zero hs
    (boundedNormalizedMellin_valuation_sourceSquare hW hp.ne_zero)
  have h₂ := boundedNormalizedMellin_valuation_primeDifference hp.ne_zero
    (fun σ hσ => summable_primeDifference p (hs σ hσ)) h₁ k
  rw [sourceSquareCoeff, primeDifference_twice_square hp,
    valuationPart_convolution_coprimePart, valuationPart_convolution_coprimePart] at h₂
  exact h₂

end RHTower.WeilSingularArithmetic
