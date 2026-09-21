import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePFiveChannelKreinFactorization

/-!
# Common-centroid translation gauge of the Route-P SP-E carrier

The complete strict-cross source carrier uses the five literal profiles
`w`, `wd`, `wc`, `wdc`, and `wd²`.  Translating every matched and quantile
centroid by one common amount leaves relative displacement `d` unchanged.  On
those five profiles this is an explicit unipotent transformation, and it
preserves the exact five-channel Krein form.

Consequently the entire finite P source-current matrix is blind to this common
centroid mode.  A graph-closed P/SP-E producer can quotient or transport that
mode as gauge, but must obtain its estimate from relative displacement and
ordered source history.  No cofinal graph bound or RH implication is claimed.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- The unipotent five-profile transformation induced by a common centroid translation. -/
def speQuantileRieszStrictCrossFiveChannelCentroidTranslation (a : ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, 0, a, 0, 0;
    0, 1, 0, a, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

/-- Common centroid translation is an exact isometry of the full five-channel source form. -/
theorem speQuantileRieszStrictCrossFiveChannelCentroidTranslation_preserves :
    ∀ a : ℂ,
      speQuantileRieszStrictCrossFiveChannelCentroidTranslation a *
          speQuantileRieszStrictCrossFiveChannelKreinForm *
          (speQuantileRieszStrictCrossFiveChannelCentroidTranslation a)ᵀ =
        speQuantileRieszStrictCrossFiveChannelKreinForm := by
  intro a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [speQuantileRieszStrictCrossFiveChannelCentroidTranslation,
      speQuantileRieszStrictCrossFiveChannelKreinForm,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

/-- The five literal profiles after translating both centroid systems by the same real amount.
The displacement profile is unchanged. -/
def speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile {ι : Type*}
    (atom : ι → ℕ) (a : ℝ) : Matrix ι (Fin 5) ℂ :=
  fun i => ![(criticalMellinAtomWeight (atom i) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      ccmActualHeadMatchedQuantilePolarDisplacement (atom i) : ℝ) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      (ccmActualHeadMatchedPolarCentroid (atom i) + a) : ℝ) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      ccmActualHeadMatchedQuantilePolarDisplacement (atom i) *
      (ccmActualHeadMatchedPolarCentroid (atom i) + a) : ℝ) : ℂ),
    ((criticalMellinAtomWeight (atom i) *
      ccmActualHeadMatchedQuantilePolarDisplacement (atom i) ^ 2 : ℝ) : ℂ)]

/-- Profile translation is exactly right multiplication by the unipotent gauge. -/
theorem speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile_eq
    {ι : Type*} (atom : ι → ℕ) (a : ℝ) :
    speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile atom a =
      speQuantileRieszStrictCrossFiveChannelProfile atom *
        speQuantileRieszStrictCrossFiveChannelCentroidTranslation (a : ℂ) := by
  ext i j
  fin_cases j <;>
    simp [speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile,
      speQuantileRieszStrictCrossFiveChannelProfile,
      speQuantileRieszStrictCrossFiveChannelCentroidTranslation,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- Full strict-cross current is unchanged by a common centroid translation.  Thus this mode
cannot provide the missing sign or growth control in the P/SP-E cofinal graph estimate. -/
theorem speQuantileRieszStrictCrossFiveChannelCentroidTranslated_current_invariant
    {ι : Type*} (atom : ι → ℕ) (a : ℝ) :
    speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile atom a *
        speQuantileRieszStrictCrossFiveChannelKreinForm *
        (speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile atom a)ᵀ =
      speQuantileRieszStrictCrossFiveChannelProfile atom *
        speQuantileRieszStrictCrossFiveChannelKreinForm *
        (speQuantileRieszStrictCrossFiveChannelProfile atom)ᵀ := by
  rw [speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile_eq]
  simp only [Matrix.transpose_mul]
  have hpres :
      speQuantileRieszStrictCrossFiveChannelCentroidTranslation (a : ℂ) *
          (speQuantileRieszStrictCrossFiveChannelKreinForm *
            (speQuantileRieszStrictCrossFiveChannelCentroidTranslation (a : ℂ))ᵀ) =
        speQuantileRieszStrictCrossFiveChannelKreinForm := by
    simpa only [Matrix.mul_assoc] using
      speQuantileRieszStrictCrossFiveChannelCentroidTranslation_preserves (a : ℂ)
  calc
    _ = speQuantileRieszStrictCrossFiveChannelProfile atom *
        (speQuantileRieszStrictCrossFiveChannelCentroidTranslation (a : ℂ) *
          (speQuantileRieszStrictCrossFiveChannelKreinForm *
            (speQuantileRieszStrictCrossFiveChannelCentroidTranslation (a : ℂ))ᵀ)) *
        (speQuantileRieszStrictCrossFiveChannelProfile atom)ᵀ := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [hpres]

end RHTower
