import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIWideMeasure
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeBlockSymmetry
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyMoment

/-!
# Two-sided Gallagher-frequency Case-II measure

The wide-smoothed Case-II theorem is naturally stated on one positive physical-frequency band.
This module pulls that band back through both Gallagher-frequency changes of variables.  Evenness of
the harmonic prime-block norm supplies the positive-frequency half from the same analytic estimate.
-/

namespace RHTower.Sieve

noncomputable section

open MeasureTheory Set

/-- Union of both Gallagher-frequency pullbacks of one physical Case-II exceptional band. -/
def menonHarmonicPrimeBlockWideGallagherExceptionalSet
    (a X Y : ℕ) (H B T V : ℝ) : Set ℝ :=
  (fun w : ℝ => -(2 * Real.pi) * w) ⁻¹'
      menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V ∪
    (fun w : ℝ => (2 * Real.pi) * w) ⁻¹'
      menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V

/-- Passing from one physical band to both Gallagher-frequency signs costs exactly two copies of
the Jacobian `(2π)⁻¹`. -/
theorem volume_real_menonHarmonicPrimeBlockWideGallagherExceptionalSet_le
    (a X Y : ℕ) (H B T V : ℝ) :
    volume.real
        (menonHarmonicPrimeBlockWideGallagherExceptionalSet a X Y H B T V) ≤
      2 * (2 * Real.pi)⁻¹ *
        volume.real (menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V) := by
  rw [menonHarmonicPrimeBlockWideGallagherExceptionalSet]
  refine (measureReal_union_le _ _).trans ?_
  rw [volume_real_preimage_neg_mul_left (by positivity : 0 < 2 * Real.pi),
    volume_real_preimage_mul_left (by positivity : 0 < 2 * Real.pi)]
  ring_nf
  exact le_rfl

/-- A large value in the negative Gallagher half belongs to the two-sided pullback. -/
theorem mem_menonHarmonicPrimeBlockWideGallagherExceptionalSet_of_neg
    {a X Y : ℕ} {H B T V w : ℝ}
    (hband : T + V ≤ -(2 * Real.pi) * w ∧ -(2 * Real.pi) * w ≤ 2 * T - V)
    (hlarge :
      (((B + menonWideIntervalTransitionEnvelope X H) + primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
          ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) w‖) :
    w ∈ menonHarmonicPrimeBlockWideGallagherExceptionalSet a X Y H B T V := by
  refine Set.mem_union_left _ ?_
  exact ⟨hband, by simpa [Real.pi_ne_zero] using hlarge⟩

/-- The same analytic set covers a large value in the positive Gallagher half by conjugation. -/
theorem mem_menonHarmonicPrimeBlockWideGallagherExceptionalSet_of_pos
    {a X Y : ℕ} {H B T V w : ℝ}
    (hband : T + V ≤ (2 * Real.pi) * w ∧ (2 * Real.pi) * w ≤ 2 * T - V)
    (hlarge :
      (((B + menonWideIntervalTransitionEnvelope X H) + primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
          ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) w‖) :
    w ∈ menonHarmonicPrimeBlockWideGallagherExceptionalSet a X Y H B T V := by
  refine Set.mem_union_right _ ?_
  refine ⟨hband, ?_⟩
  have harg : -((2 * Real.pi) * w) / (2 * Real.pi) = -w := by
    field_simp [Real.pi_ne_zero]
  change
    (((B + menonWideIntervalTransitionEnvelope X H) + primePowerDefectIoc a Y) /
        Real.log ((a + 1 : ℕ) : ℝ)) /
        ((a + 1 : ℕ) : ℝ) <
      ‖harmonicPrimeBlockPoly (primesRange a Y)
        (-((2 * Real.pi) * w) / (2 * Real.pi))‖
  rw [harg, norm_harmonicPrimeBlockPoly_neg]
  exact hlarge

end


end RHTower.Sieve
