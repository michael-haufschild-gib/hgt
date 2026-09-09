import GaloisForLFunctions.HTGeometry.GomesDilatonMeasureReconstruction

/-!
# Exact information loss under total-mass normalization

Continuing the reconstruction experiment from arXiv:2607.24901v1 section 4, normalize
actual polynomial-density measures by their total mass. Finite measures lose exactly
constant log-amplitude. Infinite-mass profiles all collapse to zero under this total
operation; they are not probability measures. The classification includes both cases.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Total mass normalization; an infinite-mass input produces the zero measure. -/
def gomesDilatonMassNormalized (H : ℝ[X]) : Measure ℝ :=
  (gomesDilatonMeasure H Set.univ)⁻¹ • gomesDilatonMeasure H

/-- Exact mass, including the infinite-input collapse. -/
theorem gomesDilatonMassNormalized_mass (H : ℝ[X]) :
    gomesDilatonMassNormalized H Set.univ =
      if gomesDilatonMeasure H Set.univ = ∞ then 0 else 1 := by
  classical
  unfold gomesDilatonMassNormalized
  rw [Measure.smul_apply, smul_eq_mul]
  split_ifs with h
  · simp only [h, ENNReal.inv_top, zero_mul]
  · exact ENNReal.inv_mul_cancel (gomesDilatonMeasure_mass_ne_zero H) h

/-- The normalized observation vanishes exactly when the input has infinite total mass. -/
theorem gomesDilatonMassNormalized_zero_iff (H : ℝ[X]) :
    gomesDilatonMassNormalized H = 0 ↔ gomesDilatonMeasure H Set.univ = ∞ := by
  constructor
  · intro h
    have hm := congrArg (fun μ : Measure ℝ => μ Set.univ) h
    rw [gomesDilatonMassNormalized_mass] at hm
    by_contra hn
    simp only [hn, ↓reduceIte] at hm
    exact one_ne_zero (show (1 : ℝ≥0∞) = 0 from hm)
  · intro h
    simp only [gomesDilatonMassNormalized, h, ENNReal.inv_top, zero_smul]

/-- Probability normalization succeeds precisely for finite input measures. -/
theorem gomesDilatonMassNormalized_probability_iff (H : ℝ[X]) :
    IsProbabilityMeasure (gomesDilatonMassNormalized H) ↔ IsFiniteMeasure (gomesDilatonMeasure H) := by
  rw [isFiniteMeasure_iff, lt_top_iff_ne_top]
  constructor
  · intro hp ht
    have hm : gomesDilatonMassNormalized H Set.univ = 1 := @measure_univ _ _ _ hp
    rw [(gomesDilatonMassNormalized_zero_iff H).mpr ht] at hm
    exact zero_ne_one hm
  · intro ht
    exact ⟨by rw [gomesDilatonMassNormalized_mass, if_neg ht]⟩

/-- Total normalization removes every constant log-amplitude, also in the infinite sector. -/
theorem gomesDilatonMassNormalized_constant (H : ℝ[X]) (c : ℝ) :
    gomesDilatonMassNormalized (H + C c) = gomesDilatonMassNormalized H := by
  let s := ENNReal.ofReal (Real.exp c)
  have hs0 : s ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos c)
  have hst : s ≠ ∞ := ENNReal.ofReal_ne_top
  unfold gomesDilatonMassNormalized
  rw [gomesDilatonMeasure_constant, Measure.smul_apply, smul_eq_mul, smul_smul]
  change ((s * gomesDilatonMeasure H Set.univ)⁻¹ * s) • gomesDilatonMeasure H = _
  rw [ENNReal.mul_inv (Or.inl hs0) (Or.inl hst)]
  have hc : s⁻¹ * (gomesDilatonMeasure H Set.univ)⁻¹ * s =
      (gomesDilatonMeasure H Set.univ)⁻¹ := by
    calc
      _ = (s⁻¹ * s) * (gomesDilatonMeasure H Set.univ)⁻¹ := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hs0 hst, one_mul]
  rw [hc]

/-- Restoring the measured total mass recovers the raw measure exactly in the finite sector. -/
theorem gomesDilatonMassNormalized_restore_iff (H : ℝ[X]) :
    gomesDilatonMeasure H Set.univ • gomesDilatonMassNormalized H = gomesDilatonMeasure H ↔
      IsFiniteMeasure (gomesDilatonMeasure H) := by
  rw [isFiniteMeasure_iff, lt_top_iff_ne_top]
  constructor
  · intro h ht
    rw [(gomesDilatonMassNormalized_zero_iff H).mpr ht, smul_zero] at h
    have hm := congrArg (fun μ : Measure ℝ => μ Set.univ) h
    exact gomesDilatonMeasure_mass_ne_zero H hm.symm
  · intro ht
    rw [gomesDilatonMassNormalized, smul_smul,
      ENNReal.mul_inv_cancel (gomesDilatonMeasure_mass_ne_zero H) ht, one_smul]

/-- Complete normalization ambiguity: constant shifts, plus collapse of all infinite-mass profiles. -/
theorem gomesDilatonMassNormalized_eq_iff (H K : ℝ[X]) :
    gomesDilatonMassNormalized H = gomesDilatonMassNormalized K ↔
      (∃ c : ℝ, H = K + C c) ∨
        (gomesDilatonMeasure H Set.univ = ∞ ∧ gomesDilatonMeasure K Set.univ = ∞) := by
  constructor
  · intro h
    by_cases ht : gomesDilatonMeasure H Set.univ = ∞
    · exact Or.inr ⟨ht, (gomesDilatonMassNormalized_zero_iff K).mp
        (h.symm.trans ((gomesDilatonMassNormalized_zero_iff H).mpr ht))⟩
    · have kt : gomesDilatonMeasure K Set.univ ≠ ∞ := by
        intro hk
        exact ht ((gomesDilatonMassNormalized_zero_iff H).mp
          (h.trans ((gomesDilatonMassNormalized_zero_iff K).mpr hk)))
      let r := gomesDilatonMeasure H Set.univ * (gomesDilatonMeasure K Set.univ)⁻¹
      have hr0 : r ≠ 0 := mul_ne_zero (gomesDilatonMeasure_mass_ne_zero H)
        (ENNReal.inv_ne_zero.mpr kt)
      have hrt : r ≠ ∞ := ENNReal.mul_ne_top ht
        (ENNReal.inv_ne_top.mpr (gomesDilatonMeasure_mass_ne_zero K))
      let s : Set.Ioi (0 : ℝ) := ⟨r.toReal, ENNReal.toReal_pos hr0 hrt⟩
      have he : gomesDilatonMeasure H = r • gomesDilatonMeasure K := by
        calc
          _ = gomesDilatonMeasure H Set.univ • gomesDilatonMassNormalized H := by
            rw [gomesDilatonMassNormalized, smul_smul,
              ENNReal.mul_inv_cancel (gomesDilatonMeasure_mass_ne_zero H) ht, one_smul]
          _ = gomesDilatonMeasure H Set.univ • gomesDilatonMassNormalized K := by rw [h]
          _ = _ := by rw [gomesDilatonMassNormalized, smul_smul]
      have hp : gomesDilatonMeasure H = ENNReal.ofReal (s : ℝ) • gomesDilatonMeasure K := by
        simpa only [s, ENNReal.ofReal_toReal hrt] using he
      exact Or.inl ⟨Real.log (s : ℝ), (gomesDilatonMeasure_positive_scale_iff H K s).mp hp⟩
  · rintro (⟨c, rfl⟩ | ⟨hh, hk⟩)
    · exact gomesDilatonMassNormalized_constant K c
    · rw [(gomesDilatonMassNormalized_zero_iff H).mpr hh,
        (gomesDilatonMassNormalized_zero_iff K).mpr hk]

/-- In operator language, normalized laws agree exactly for equal connections or joint collapse. -/
theorem gomesDilatonMassNormalized_connection_iff (H K : ℝ[X]) :
    gomesDilatonMassNormalized H = gomesDilatonMassNormalized K ↔
      dilatonSuperchargeCLM H = dilatonSuperchargeCLM K ∨
        (gomesDilatonMeasure H Set.univ = ∞ ∧ gomesDilatonMeasure K Set.univ = ∞) := by
  rw [gomesDilatonMassNormalized_eq_iff, gomesDilatonConnection_constant_iff]

/-- Normalized shape plus total mass retains everything except the joint infinite-mass collapse. -/
theorem gomesDilatonMassNormalized_mass_record_iff (H K : ℝ[X]) :
    (gomesDilatonMassNormalized H, gomesDilatonMeasure H Set.univ) =
      (gomesDilatonMassNormalized K, gomesDilatonMeasure K Set.univ) ↔
        H = K ∨ (gomesDilatonMeasure H Set.univ = ∞ ∧ gomesDilatonMeasure K Set.univ = ∞) := by
  constructor
  · intro h
    have hn : gomesDilatonMassNormalized H = gomesDilatonMassNormalized K := congrArg Prod.fst h
    have hm : gomesDilatonMeasure H Set.univ = gomesDilatonMeasure K Set.univ := congrArg Prod.snd h
    by_cases ht : gomesDilatonMeasure H Set.univ = ∞
    · exact Or.inr ⟨ht, hm.symm.trans ht⟩
    · have kt : gomesDilatonMeasure K Set.univ ≠ ∞ := by rwa [← hm]
      apply Or.inl
      apply gomesDilatonMeasure_injective
      calc
        _ = gomesDilatonMeasure H Set.univ • gomesDilatonMassNormalized H := by
          rw [gomesDilatonMassNormalized, smul_smul,
            ENNReal.mul_inv_cancel (gomesDilatonMeasure_mass_ne_zero H) ht, one_smul]
        _ = gomesDilatonMeasure K Set.univ • gomesDilatonMassNormalized K := by rw [hn, hm]
        _ = _ := by rw [gomesDilatonMassNormalized, smul_smul,
          ENNReal.mul_inv_cancel (gomesDilatonMeasure_mass_ne_zero K) kt, one_smul]
  · rintro (rfl | ⟨hh, hk⟩)
    · rfl
    · rw [(gomesDilatonMassNormalized_zero_iff H).mpr hh,
        (gomesDilatonMassNormalized_zero_iff K).mpr hk, hh, hk]

end GaloisForLFunctions.HTGeometry
