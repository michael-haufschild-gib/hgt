import GaloisForLFunctions.RHTower.Sieve.Section4DiscAnnulus
import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The innermost cofactor on the disc

On the low-frequency disc the two prime polynomials of §4 have no cancellation, so the saving has to
come from the cofactor.  It does: the cofactor is a Möbius polynomial over an interval of
near-maximal length, and `Sieve/CofactorLowFreqBound` gives it a saving better than every power of
the logarithm, uniformly over a frequency range larger than every power of the logarithm.

Squaring a uniform pointwise bound over the disc costs only the disc's length.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- A uniform pointwise bound on the disc gives a mean-square bound. -/
theorem setIntegral_disc_normSq_logPoly_le (c : ℕ → ℂ) (D : Finset ℕ) {w₀ U : ℝ} (hw₀ : 0 ≤ w₀)
    (hU : ∀ w ∈ Set.Icc (-w₀) w₀, ‖logPoly c D w‖ ≤ U) :
    (∫ w in Set.Icc (-w₀) w₀, ‖logPoly c D w‖ ^ 2) ≤ U ^ 2 * (2 * w₀) := by
  classical
  have hcont : Continuous fun w : ℝ => ‖logPoly c D w‖ ^ 2 := ((continuous_logPoly c D).norm).pow 2
  have hint : IntegrableOn (fun w : ℝ => ‖logPoly c D w‖ ^ 2) (Set.Icc (-w₀) w₀) volume :=
    hcont.integrableOn_Icc
  have hint2 : IntegrableOn (fun _ : ℝ => U ^ 2) (Set.Icc (-w₀) w₀) volume :=
    continuous_const.integrableOn_Icc
  have hmono := setIntegral_mono_on hint hint2 measurableSet_Icc (fun w hw => by
    exact pow_le_pow_left₀ (norm_nonneg _) (hU w hw) 2)
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  ring

/-- **The cofactor on the disc, with the low-frequency saving.** -/
theorem exists_setIntegral_disc_normSq_logPoly_moebius_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (a b : ℕ) (w₀ : ℝ), 1 ≤ a → 0 ≤ w₀ →
      N₁ ≤ ((a - 1 : ℕ) : ℝ) → N₁ ≤ (b : ℝ) →
      K₀ ≤ contourParam (((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ)) →
      K₀ ≤ contourParam ((b : ℝ) + smoothWidth (b : ℝ)) →
      5 + 4 * (2 * Real.pi * w₀)
        ≤ ((contourParam (((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ)) : ℕ) : ℝ) →
      5 + 4 * (2 * Real.pi * w₀) ≤ ((contourParam ((b : ℝ) + smoothWidth (b : ℝ)) : ℕ) : ℝ) →
      (∫ w in Set.Icc (-w₀) w₀, ‖logPoly moebiusCoeff (Finset.Icc a b) w‖ ^ 2)
        ≤ (moebiusSharpBound ((a - 1 : ℕ) : ℝ) + moebiusSharpBound (b : ℝ)) ^ 2 * (2 * w₀) := by
  obtain ⟨K₀, N₁, hbd⟩ := exists_norm_logPoly_moebiusCoeff_Icc_le
  refine ⟨K₀, N₁, ?_⟩
  intro a b w₀ ha hw₀ hlo hhi hKlo hKhi hτlo hτhi
  refine setIntegral_disc_normSq_logPoly_le moebiusCoeff (Finset.Icc a b) hw₀ ?_
  intro w hw
  rw [Set.mem_Icc] at hw
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |(-(2 * Real.pi * w))| ≤ 2 * Real.pi * w₀ := by
    rw [abs_neg, abs_mul, abs_of_pos hπ]
    have h1 : |w| ≤ w₀ := abs_le.2 ⟨hw.1, hw.2⟩
    exact mul_le_mul_of_nonneg_left h1 hπ.le
  refine hbd a b w ha hlo hhi hKlo hKhi ?_ ?_
  · linarith [hτlo, habs]
  · linarith [hτhi, habs]

/-- **The cofactor of an initial block on the disc, with the low-frequency saving.**  With `A₀ = 1`
every cofactor block of every ladder is an initial segment, so this is the form the assembly uses. -/
theorem exists_setIntegral_disc_normSq_logPoly_moebius_one_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (b : ℕ) (w₀ : ℝ), 0 ≤ w₀ → N₁ ≤ (b : ℝ) →
      K₀ ≤ contourParam ((b : ℝ) + smoothWidth (b : ℝ)) →
      5 + 4 * (2 * Real.pi * w₀) ≤ ((contourParam ((b : ℝ) + smoothWidth (b : ℝ)) : ℕ) : ℝ) →
      (∫ w in Set.Icc (-w₀) w₀, ‖logPoly moebiusCoeff (Finset.Icc 1 b) w‖ ^ 2)
        ≤ moebiusSharpBound (b : ℝ) ^ 2 * (2 * w₀) := by
  obtain ⟨K₀, N₁, hbd⟩ := exists_norm_logPoly_moebiusCoeff_Icc_one_le
  refine ⟨K₀, N₁, ?_⟩
  intro b w₀ hw₀ hb hK hτ
  refine setIntegral_disc_normSq_logPoly_le moebiusCoeff (Finset.Icc 1 b) hw₀ ?_
  intro w hw
  rw [Set.mem_Icc] at hw
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |(-(2 * Real.pi * w))| ≤ 2 * Real.pi * w₀ := by
    rw [abs_neg, abs_mul, abs_of_pos hπ]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hw.1, hw.2⟩) hπ.le
  exact hbd b w hb hK (by linarith [hτ, habs])

end

end RHTower.Sieve
