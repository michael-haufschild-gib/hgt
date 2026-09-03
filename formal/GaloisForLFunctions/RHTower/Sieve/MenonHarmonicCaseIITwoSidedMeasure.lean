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

/-- Full Case-II measure theorem simultaneously on both Gallagher-frequency halves. -/
theorem exists_absolute_eventually_volume_real_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_twoSided_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in Filter.atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
        0 < H → (Y : ℝ) + H ≤ (X : ℝ) →
        1 < sigma → 0 ≤ B → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        1 ≤ T → Δ / 2 ≤ T →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        (Real.log (a : ℝ)) ^ (-8 : ℝ) < Q →
        let D : ℕ :=
          3 * (Nat.log 2 X + 1) ^ 3 * (Nat.log 2 L + 1) ^ 3
        let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * W ^ 2 *
              (1 + Real.log (W * (X : ℝ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        volume.real
            (menonHarmonicPrimeBlockWideGallagherExceptionalSet a X Y H B T V) ≤
          2 * (2 * Real.pi)⁻¹ *
            (4 * Δ * (((((cells * D * 12 : ℕ) : ℝ)) * Hmax) / Vexp ^ 2 + 1)) := by
  obtain ⟨C0, hC0, hmain⟩ :=
    exists_absolute_eventually_volume_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_le
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hmain] with a ha
  intro L X Y cells T0 t H B sigma V Δ T hX haY hXL hT0 hscale ha64 hL hLX hXa
    hH hYX hsigma hB hV hΔ hcells hgrid hT hΔT h2T
  dsimp only
  intro hQ
  have hphysical := ha hX haY hXL hT0 hscale ha64 hL hLX hXa hH hYX hsigma hB hV
    hΔ hcells hgrid hT hΔT h2T hQ
  have hpull :=
    volume_real_menonHarmonicPrimeBlockWideGallagherExceptionalSet_le a X Y H B T V
  exact hpull.trans (mul_le_mul_of_nonneg_left hphysical (by positivity))

end


end RHTower.Sieve
