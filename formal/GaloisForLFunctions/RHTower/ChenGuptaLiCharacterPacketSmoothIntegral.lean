/-
# Chen--Gupta--Li smooth fourth-moment packet integral

This module proves the exact finite packet identity behind the smooth
fourth-moment step of Chen--Gupta--Li, Lemma 9.2: a compactly smoothed
quartic character-packet integral is the character-product Fourier-multiplier
sum.  It uses only finite sums, compact support, a change of variables, and
the exact finite character orthogonality expansion already in the corpus.

No RH, GRH, smoothness, energy, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketSmoothFourthMoment

open Complex MeasureTheory Set Filter

noncomputable section

namespace RHTower

/-- The compact smooth cutoff at a certified CGL large scale. -/
def cglCharacterPacketScaledSmoothCutoff (X : CGLCharacterPacketLargeScale) (τ : ℝ) : ℂ :=
  cglCanonicalSmoothCutoff (τ / (X.1 : ℝ))

/-- A nonzero dilation preserves compact support of the canonical cutoff. -/
theorem hasCompactSupport_cglCharacterPacketScaledSmoothCutoff (X : CGLCharacterPacketLargeScale) :
    HasCompactSupport (fun τ : ℝ => cglCanonicalSmoothCutoff (τ / (X.1 : ℝ))) := by
  have hX0 : (X.1 : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one X.2)
  have h := hasCompactSupport_cglCanonicalSmoothCutoff.comp_smul (c := (X.1 : ℝ)⁻¹)
    (inv_ne_zero hX0)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- The compact smooth cutoff at a certified CGL large scale is continuous. -/
theorem continuous_cglCharacterPacketScaledSmoothCutoff (X : CGLCharacterPacketLargeScale) :
    Continuous (fun τ : ℝ => cglCanonicalSmoothCutoff (τ / (X.1 : ℝ))) := by
  change Continuous (cglCanonicalSmoothCutoff ∘ fun τ : ℝ => τ / (X.1 : ℝ))
  have hX0 : (X.1 : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one X.2)
  exact contDiff_cglCanonicalSmoothCutoff.continuous.comp
    (continuous_id.div continuous_const (fun _ => hX0))

/-- A scaled compact cutoff times a character-packet wave pair is integrable. -/
theorem integrable_cglCharacterPacketScaledSmoothWavePair
    (X : CGLCharacterPacketLargeScale) (t u : ℝ) :
    Integrable (fun τ : ℝ => cglCharacterPacketScaledSmoothCutoff X τ *
      (cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ))) := by
  have hcont : Continuous (fun τ : ℝ => cglCharacterPacketScaledSmoothCutoff X τ *
      (cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ))) := by
    unfold cglCharacterPacketScaledSmoothCutoff
    exact (continuous_cglCharacterPacketScaledSmoothCutoff X).mul
      ((continuous_cglCharacterPacketWave t).mul
        (Complex.continuous_conj.comp (continuous_cglCharacterPacketWave u)))
  apply hcont.integrable_of_hasCompactSupport
  unfold cglCharacterPacketScaledSmoothCutoff
  exact (hasCompactSupport_cglCharacterPacketScaledSmoothCutoff X).mul_right

/-- The scaled smooth wave-pair integral equals the CGL Fourier multiplier. -/
theorem integral_cglCharacterPacketScaledSmoothWavePair
    (X : CGLCharacterPacketLargeScale) (t u : ℝ) :
    (∫ τ : ℝ, cglCharacterPacketScaledSmoothCutoff X τ *
      (cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ))) =
      cglCharacterPacketSmoothMultiplier X.1 (t - u) := by
  have hleft : (∫ τ : ℝ, cglCanonicalSmoothCutoff (τ / (X.1 : ℝ)) *
      cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ)) =
      cglCharacterPacketSmoothMultiplier X.1 (t - u) := by
    let G : ℝ → ℂ := fun L =>
      cglCanonicalSmoothCutoff L * cglCharacterPacketWave t ((X.1 : ℝ) * L) *
        star (cglCharacterPacketWave u ((X.1 : ℝ) * L))
    have hpoint : ∀ τ : ℝ,
        cglCanonicalSmoothCutoff (τ / (X.1 : ℝ)) *
          cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ) =
          G (τ / (X.1 : ℝ)) := by
      intro τ
      have hX0 : (X.1 : ℝ) ≠ 0 := by
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one X.2)
      dsimp [G]
      congr 3 <;> field_simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [MeasureTheory.Measure.integral_comp_div G (X.1 : ℝ)]
    have hXnon : (0 : ℝ) ≤ (X.1 : ℝ) := X.1.2
    rw [abs_of_nonneg hXnon, Complex.real_smul]
    change (X.1 : ℝ) * (∫ L : ℝ,
      cglCanonicalSmoothCutoff L * cglCharacterPacketWave t ((X.1 : ℝ) * L) *
        star (cglCharacterPacketWave u ((X.1 : ℝ) * L))) = _
    rw [cglCharacterPacketSmoothMultiplier]
    congr 1
    rw [GaloisForLFunctions.HTGeometry.testTransform]
    apply integral_congr_ae
    filter_upwards with L
    rw [mul_assoc, cglCharacterPacketWave_mul_conj]
    congr 1
    congr 1
    push_cast
    ring
  calc
    (∫ τ : ℝ, cglCharacterPacketScaledSmoothCutoff X τ *
        (cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ))) =
        ∫ τ : ℝ, cglCanonicalSmoothCutoff (τ / (X.1 : ℝ)) *
          cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ) := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [cglCharacterPacketScaledSmoothCutoff]
      ring
    _ = cglCharacterPacketSmoothMultiplier X.1 (t - u) := hleft

/-- The literal compactly smoothed quartic CGL character-packet integral. -/
noncomputable def cglCharacterPacketSmoothQuarticIntegral {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1))
    (X : CGLCharacterPacketLargeScale) : ℂ :=
  ∫ τ : ℝ, cglCharacterPacketScaledSmoothCutoff X τ *
    cglCharacterPacketQuarticHermitianMass q R w τ

/-- Exact finite character-product expansion of the compactly smoothed CGL
quartic packet integral. -/
theorem cglCharacterPacketSmoothQuarticIntegral_eq_smoothFourthMomentContribution
    {q R : ℕ} (w : Fin R → CGLCharacterDyadicRowData (q + 1))
    (X : CGLCharacterPacketLargeScale) :
    cglCharacterPacketSmoothQuarticIntegral w X =
      cglCharacterPacketSmoothFourthMomentContribution w X.1 := by
  have hterm : ∀ p q' : Fin R × Fin R, Integrable (fun τ : ℝ =>
      (if (w p.1).character * (w p.2).character =
          (w q'.1).character * (w q'.2).character then ((q + 1).totient : ℂ) else 0) *
        (cglCharacterPacketScaledSmoothCutoff X τ *
          (cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
            star (cglCharacterPacketWave ((w q'.1).time + (w q'.2).time) τ)))) := by
    intro p q'
    exact (integrable_cglCharacterPacketScaledSmoothWavePair X
      ((w p.1).time + (w p.2).time) ((w q'.1).time + (w q'.2).time)).const_mul _
  have hpoint : ∀ τ : ℝ,
      cglCharacterPacketScaledSmoothCutoff X τ * cglCharacterPacketQuarticHermitianMass q R w τ =
        ∑ p : Fin R × Fin R, ∑ q' : Fin R × Fin R,
          (if (w p.1).character * (w p.2).character =
              (w q'.1).character * (w q'.2).character then ((q + 1).totient : ℂ) else 0) *
            (cglCharacterPacketScaledSmoothCutoff X τ *
              (cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
                star (cglCharacterPacketWave ((w q'.1).time + (w q'.2).time) τ))) := by
    intro τ
    rw [cglCharacterPacketQuarticHermitianMass_expand]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q' hq'
    ring
  unfold cglCharacterPacketSmoothQuarticIntegral
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q' _ => hterm p q']
  simp_rw [integral_finsetSum _ fun q' _ => hterm _ q']
  simp_rw [integral_const_mul,
    integral_cglCharacterPacketScaledSmoothWavePair X]
  unfold cglCharacterPacketSmoothFourthMomentContribution cglCharacterPacketProductIndexSet
  rw [Finset.sum_filter]
  let F : (Fin R × Fin R) → (Fin R × Fin R) → ℂ := fun p q' =>
    (if (w p.1).character * (w p.2).character =
        (w q'.1).character * (w q'.2).character then ((q + 1).totient : ℂ) else 0) *
      cglCharacterPacketSmoothMultiplier X.1
        (((w p.1).time + (w p.2).time) - ((w q'.1).time + (w q'.2).time))
  change (∑ p : Fin R × Fin R, ∑ q' : Fin R × Fin R, F p q') =
    ∑ pq : (Fin R × Fin R) × (Fin R × Fin R),
      if cglCharacterPacketPairCharacter w pq.1 = cglCharacterPacketPairCharacter w pq.2 then
        ((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X.1
          (cglCharacterPacketPairFrequency w pq) else 0
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro pq hpq
  simp [F, cglCharacterPacketPairCharacter, cglCharacterPacketPairFrequency,
    cglCharacterPacketPairOrdinate]

end RHTower
