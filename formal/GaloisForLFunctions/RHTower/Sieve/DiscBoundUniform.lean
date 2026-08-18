import GaloisForLFunctions.RHTower.Sieve.RelMoebiusSharp
import GaloisForLFunctions.RHTower.Sieve.ContourParamMono

/-!
# The disc bound, uniformly over the ladder

All cofactor blocks of the ladder exceed the shortest one, and both the relative Möbius majorant and
the admissible twist range are monotone in the block length, so a single check at the shortest block
supplies the disc hypothesis for every step at once.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The disc bound, uniformly over the ladder.** -/
theorem exists_disc_bound_uniform :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (B₀ L : ℕ) (Q η w₀ Nmin : ℝ), 1 ≤ Q → 0 ≤ η → 1 ≤ Nmin →
      N₁ ≤ Nmin → 0 ≤ w₀ →
      (∀ j ∈ Finset.range L, Nmin ≤ ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) →
      K₀ ≤ contourParam Nmin →
      5 + 8 * Real.pi * w₀ ≤ ((contourParam Nmin : ℕ) : ℝ) →
      ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
        ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖
          ≤ relMoebiusSharp Nmin * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) := by
  obtain ⟨K₀, N₁, hbound⟩ := exists_norm_logPoly_geomCofactorBlockAt_rel_le
  refine ⟨K₀, N₁, ?_⟩
  intro B₀ L Q η w₀ Nmin hQ hη hNmin hN₁ hw₀ hNj hK hτ j hj w hw
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  set N : ℝ := ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) with hN
  have hNge : Nmin ≤ N := hNj j hj
  have hN1 : (1 : ℝ) ≤ N := le_trans hNmin hNge
  have hsw : (0 : ℝ) ≤ smoothWidth N := by
    rw [smoothWidth]
    exact div_nonneg (by linarith) (smoothRatio_pos N).le
  have hmono : contourParam Nmin ≤ contourParam (N + smoothWidth N) :=
    contourParam_mono hNmin (by linarith)
  have hmonoR : ((contourParam Nmin : ℕ) : ℝ) ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) := by
    exact_mod_cast hmono
  have hτ' : 5 + 4 * |(-(2 * Real.pi * w))|
      ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) := by
    have habs : |(-(2 * Real.pi * w))| = 2 * Real.pi * |w| := by
      rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rw [Set.mem_Icc] at hw
    have hwabs : |w| ≤ w₀ := abs_le.2 ⟨hw.1, hw.2⟩
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [habs]
    nlinarith [hτ, hmonoR, hwabs, hpi]
  exact hbound B₀ j Q η w Nmin hQ hη hNmin hN₁ hNge (le_trans hK hmono) hτ'

end

end RHTower.Sieve
