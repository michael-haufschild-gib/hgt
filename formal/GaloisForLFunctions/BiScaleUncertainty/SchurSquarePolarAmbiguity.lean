import GaloisForLFunctions.BiScaleUncertainty.SchurSquareCorrelation
import GaloisForLFunctions.BiScaleUncertainty.SeparatedCopySquareClassification

/-!
# Smooth sources with identical squared correlations and different polar balance

An exponentially attenuated negative copy cancels the polar moment. Reversing
only the copy's sign preserves the mass and every squared correlation but
doubles the seed's positive normalized polar moment. Thus a square-profile
certificate needs additional signed data to recover polar balance.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SeparatedSquare
set_option autoImplicit false

private theorem attenuation_identity (T : ℝ) :
    2 * Real.exp (-T / 2) * Real.cosh (T / 2) = 1 + Real.exp (-T / 2) ^ 2 := by
  have he : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero]
  rw [Real.cosh_eq, show -(T / 2) = -T / 2 by ring]
  nlinarith only [he]

/-- A hypothesis-free pair of smooth compact sources separates squared data from polar neutrality. -/
theorem exists_smooth_same_square_distinct_polar :
    ∃ f g : C_c(ℝ, ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (g : ℝ → ℝ) ∧
      0 < autocorr f 0 ∧ autocorr g 0 = autocorr f 0 ∧
      (∀ x, SchurSquare.profile g x = SchurSquare.profile f x) ∧
      normalizedPolarMoment f = 0 ∧ 0 < normalizedPolarMoment g := by
  obtain ⟨b, hb, hbc, hR, hP, _⟩ :=
    exists_smooth_source_positive_polar_moment (r := 1) zero_lt_one
  let f : C_c(ℝ, ℝ) := ⟨⟨b, hb.continuous⟩, hbc⟩
  let a := Real.exp (-gap f / 2)
  have hRs : 0 < autocorr (f : ℝ → ℝ) 0 := hR
  have hPs : 0 < normalizedPolarMoment (f : ℝ → ℝ) := hP
  have hf : ContDiff ℝ 2 (f : ℝ → ℝ) := hb.of_le (by norm_num)
  have hminus : normalizedPolarMoment (source f a) = 0 :=
    normalizedPolarMoment_polarCopy hf f.hasCompactSupport (gap f)
  have hfactor : 2 * copyMixingCoefficient a * Real.cosh (gap f / 2) = 1 := by
    have he := attenuation_identity (gap f)
    change 2 * a * Real.cosh (gap f / 2) = 1 + a ^ 2 at he
    have hd : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
    unfold copyMixingCoefficient
    field_simp [hd]
    nlinarith only [he]
  have hplus : normalizedPolarMoment (source f (-a)) = 2 * normalizedPolarMoment f := by
    have hs (x : ℝ) (hx : radius f < |x|) : autocorr f x = 0 :=
      (exists_pos_autocorr_support_radius f.hasCompactSupport).choose_spec.2 x hx
    have he := normalizedPolarMoment_subtractCopy hf f.hasCompactSupport hRs hs
      (radius_lt_gap f) (-a)
    have hc : copyMixingCoefficient (-a) = -copyMixingCoefficient a := by
      simp only [copyMixingCoefficient, neg_sq, neg_div]
    change normalizedPolarMoment (source f (-a)) = _ at he
    rw [hc] at he
    nlinarith only [he, hfactor]
  refine ⟨source f a, source f (-a), contDiff_subtractCopy hb _ _,
    contDiff_subtractCopy hb _ _, ?_, ?_, ?_, hminus, ?_⟩
  · rw [source_mass]
    positivity
  · simp only [source_mass, neg_sq]
  · intro x
    exact source_square_neg f a x
  · rw [hplus]
    exact mul_pos (by positivity) hPs

/-- Polar balance cannot be recovered from the entire squared profile by any scalar functional. -/
theorem polarMoment_not_factor_through_square :
    ¬ ∃ Φ : (ℝ → ℝ) → ℝ, ∀ f : C_c(ℝ, ℝ),
      Φ (SchurSquare.profile f) = normalizedPolarMoment f := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨f, g, _, _, _, _, hs, hf, hg⟩ := exists_smooth_same_square_distinct_polar
  have he : SchurSquare.profile g = SchurSquare.profile f := funext hs
  have hp : normalizedPolarMoment g = normalizedPolarMoment f := by
    rw [← hΦ g, he, hΦ f]
  rw [hp, hf] at hg
  exact lt_irrefl _ hg

/-- The same counterexample preserves the complete blind-node set, not merely a finite sample. -/
theorem exists_smooth_same_zeros_distinct_polar :
    ∃ f g : C_c(ℝ, ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (g : ℝ → ℝ) ∧
      0 < autocorr f 0 ∧ autocorr g 0 = autocorr f 0 ∧
      (∀ x, autocorr g x = 0 ↔ autocorr f x = 0) ∧
      normalizedPolarMoment f = 0 ∧ 0 < normalizedPolarMoment g := by
  obtain ⟨f, g, hf, hg, hR, hm, hs, hp, hq⟩ := exists_smooth_same_square_distinct_polar
  refine ⟨f, g, hf, hg, hR, hm, ?_, hp, hq⟩
  intro x
  rw [← SchurSquare.profile_eq_zero_iff, hs x, SchurSquare.profile_eq_zero_iff]

end GaloisForLFunctions.BiScaleUncertainty.SeparatedSquare
