import GaloisForLFunctions.RHTower.Sieve.Section4DiscCofactor
import GaloisForLFunctions.RHTower.Sieve.RelMoebiusSharp

/-!
# The cofactor on the disc, relative to the block length

The disc estimate of `Sieve/Section4DiscCofactor` is stated through the absolute majorant
`moebiusSharpBound`.  What the assembly needs is the *relative* form: the block length divided out,
so that the long ladder's scale cancels against the trivial bound for its prime polynomial.  Since
`relMoebiusSharp` is antitone, one value at the shortest cofactor block serves every step.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The cofactor of a ladder step on the disc, relative to its length.** -/
theorem exists_setIntegral_disc_normSq_geomCofactorBlockAt_rel_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (B₀ j : ℕ) (Q η w₀ Nmin : ℝ), 1 ≤ Q → 0 ≤ η → 0 ≤ w₀ → 1 ≤ Nmin →
      N₁ ≤ Nmin → Nmin ≤ ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) →
      K₀ ≤ contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
        + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) →
      5 + 4 * (2 * Real.pi * w₀)
        ≤ ((contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
            + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) : ℕ) : ℝ) →
      (∫ w in Set.Icc (-w₀) w₀,
          ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖ ^ 2)
        ≤ (relMoebiusSharp Nmin * ((B₀ : ℝ) / (Q * (1 + η) ^ j))) ^ 2 * (2 * w₀) := by
  obtain ⟨K₀, N₁, hbd⟩ := exists_norm_logPoly_geomCofactorBlockAt_rel_le
  refine ⟨K₀, N₁, ?_⟩
  intro B₀ j Q η w₀ Nmin hQ hη hw₀ hNmin hN₁ hNle hK hτ
  refine setIntegral_disc_normSq_logPoly_le moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) hw₀ ?_
  intro w hw
  rw [Set.mem_Icc] at hw
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |(-(2 * Real.pi * w))| ≤ 2 * Real.pi * w₀ := by
    rw [abs_neg, abs_mul, abs_of_pos hπ]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hw.1, hw.2⟩) hπ.le
  exact hbd B₀ j Q η w Nmin hQ hη hNmin hN₁ hNle hK (by linarith [hτ, habs])

end

end RHTower.Sieve
