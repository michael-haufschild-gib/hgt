import GaloisForLFunctions.RHTower.BaezDuarteGammaMajorant

/-!
# The Báez--Duarte wavelet criterion

Equation `(5)` makes the beta-wavelet pairing datum and the Báez--Duarte coefficient datum the same
datum, and the weighted-moment scale law `(12)` turns the complete weighted-domain tower into the
RH-critical `k^{-3/4+ε}` decay.
-/

namespace RHTower

open Real MeasureTheory

noncomputable section

/-- **Equation (16).**  The beta-wavelet pairing datum and the Báez--Duarte coefficient datum are
the same datum: for every threshold the two decay statements are equivalent. -/
theorem bdWaveletPairing_decay_iff (C : ℝ) (θ : ℝ) :
    (∀ k : ℕ, 1 ≤ k →
        ‖∫ t in Set.Ioi (0 : ℝ), mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ)‖
          ≤ C * ((k : ℝ)) ^ θ)
      ↔ ∀ k : ℕ, 1 ≤ k → ‖bdCoeff (k + 1)‖ ≤ C * ((k : ℝ)) ^ θ := by
  constructor
  · intro h k hk
    rw [← integral_criticalMertens_bdKernel k]
    exact h k hk
  · intro h k hk
    rw [integral_criticalMertens_bdKernel k]
    exact h k hk

/-- **Equation (17), first arrow.**  The complete weighted-domain tower supplies the RH-critical
`k^{-3/4+ε}` decay of the Báez--Duarte coefficients. -/
theorem bdCoeff_decay_of_weightedMoments
    (h : ∀ α : ℝ, 0 ≤ α → α < 1 / 2 → WeightedMertensMoment α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖bdCoeff (k + 1)‖ ≤ C * ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε) := by
  intro ε hε
  rcases le_or_gt (1 / 4 : ℝ) ε with hbig | hsmall
  · obtain ⟨C, hC0, hC⟩ := norm_bdCoeff_le_scaleLaw (α := 0) le_rfl (h 0 le_rfl (by norm_num))
    refine ⟨C, hC0, fun k hk => ?_⟩
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hmono : ((k : ℝ)) ^ (-(1 + (0 : ℝ)) / 2) ≤ ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε) := by
      refine Real.rpow_le_rpow_of_exponent_le hk1 ?_
      linarith
    exact le_trans (hC k hk) (mul_le_mul_of_nonneg_left hmono hC0)
  · set α : ℝ := 1 / 2 - 2 * ε with hα
    have hα0 : 0 ≤ α := by rw [hα]; linarith
    have hα1 : α < 1 / 2 := by rw [hα]; linarith
    obtain ⟨C, hC0, hC⟩ := norm_bdCoeff_le_scaleLaw hα0 (h α hα0 hα1)
    refine ⟨C, hC0, fun k hk => ?_⟩
    have hexp : -(1 + α) / 2 = -(3 : ℝ) / 4 + ε := by rw [hα]; ring
    rw [← hexp]
    exact hC k hk

end

end RHTower
