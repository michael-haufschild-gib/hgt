import GaloisForLFunctions.SignedArithmeticHodgeTheory.GeneratorOrbitCutoffsReduceTheDyadicClock
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilBoundedRemainder
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# Original Gamma pays all-level tails at every real translation

A high-generator vector reads only the other source's high-generator
projection. Applying the original-source tail estimate to both sources,
including every translate of the original profile, pays each mixed probe.
Three such payments control full correlation after removing the high tail.
No commutation with odd-prime translations or Gamma contraction of a
projected profile is assumed.
-/

noncomputable section
open MeasureTheory Set Filter RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "LineH" => Lp ℂ 2 (volume : Measure ℝ)
local notation "U" => wholeLineLogCellEmbedding

/-- The physical high-generator projection, with every translation level included. -/
def wholeLineGeneratorTail (A : ℕ) : LineH →L[ℂ] LineH :=
  U ∘L (ContinuousLinearMap.id ℂ CellH - logCellGeneratorHead A) ∘L wholeLineLogCellEmbedding.adjoint

theorem wholeLineGeneratorTail_apply (A : ℕ) (F : LineH) :
    wholeLineGeneratorTail A F =
      U (wholeLineLogCellEmbedding.adjoint F -
        logCellGeneratorHead A (wholeLineLogCellEmbedding.adjoint F)) := rfl

/-- A high-generator vector reads only the high-generator part of its second source. -/
theorem inner_wholeLineGeneratorTail_eq_tail (A : ℕ) (F G : LineH) :
    inner ℂ (wholeLineGeneratorTail A F) G =
      inner ℂ (wholeLineGeneratorTail A F) (wholeLineGeneratorTail A G) := by
  let x := wholeLineLogCellEmbedding.adjoint F
  let y := wholeLineLogCellEmbedding.adjoint G
  have hz : inner ℂ (x - logCellGeneratorHead A x) (logCellGeneratorHead A y) = 0 :=
    inner_eq_zero_symm.mp (inner_logCellGeneratorHead_tail A y x)
  have hleft : inner ℂ (U (x - logCellGeneratorHead A x)) G =
      inner ℂ (x - logCellGeneratorHead A x) y :=
    (wholeLineLogCellEmbedding.adjoint_inner_right _ _).symm
  have hright : inner ℂ (U (x - logCellGeneratorHead A x)) (U (y - logCellGeneratorHead A y)) =
      inner ℂ (x - logCellGeneratorHead A x) (y - logCellGeneratorHead A y) := by
    rw [← wholeLineLogCellEmbedding.adjoint_inner_right, wholeLineLogCellEmbedding_adjoint_self]
  change inner ℂ (U (x - logCellGeneratorHead A x)) G =
    inner ℂ (U (x - logCellGeneratorHead A x)) (U (y - logCellGeneratorHead A y))
  rw [hleft, hright, inner_sub_right, hz, sub_zero]

/-- The original profile, before projection, pays the physical high-tail square mass. -/
theorem norm_wholeLineGeneratorTail_source_sq_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    ‖wholeLineGeneratorTail A (realSourceLp f hv hc)‖ ^ 2 ≤
      32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  rw [wholeLineGeneratorTail_apply, norm_wholeLineLogCellEmbedding]
  exact norm_original_cell_coordinates_sub_head_sq_le f hv hc hA

/-- Two original Gamma budgets pay the all-level high-tail probe without any coarse norm factor. -/
theorem norm_inner_generatorTail_sources_le (f g : ℝ → ℝ)
    (hfv : BoundedVariationOn f univ) (hfc : HasCompactSupport f)
    (hgv : BoundedVariationOn g univ) (hgc : HasCompactSupport g) {A : ℕ} (hA : 1 ≤ A) :
    ‖inner ℂ (wholeLineGeneratorTail A (realSourceLp f hfv hfc)) (realSourceLp g hgv hgc)‖ ≤
      16 * (levyEnergy f + levyEnergy g) / (1 + Real.log (A : ℝ)) := by
  rw [inner_wholeLineGeneratorTail_eq_tail]
  have hf := norm_wholeLineGeneratorTail_source_sq_le f hfv hfc hA
  have hg := norm_wholeLineGeneratorTail_source_sq_le g hgv hgc hA
  have hi := norm_inner_le_norm (𝕜 := ℂ)
    (wholeLineGeneratorTail A (realSourceLp f hfv hfc))
    (wholeLineGeneratorTail A (realSourceLp g hgv hgc))
  have hsq := sq_nonneg (‖wholeLineGeneratorTail A (realSourceLp f hfv hfc)‖ -
    ‖wholeLineGeneratorTail A (realSourceLp g hgv hgc)‖)
  have he : 32 * levyEnergy f / (1 + Real.log (A : ℝ)) +
      32 * levyEnergy g / (1 + Real.log (A : ℝ)) =
      2 * (16 * (levyEnergy f + levyEnergy g) / (1 + Real.log (A : ℝ))) := by ring
  nlinarith only [hf, hg, hi, hsq, he]

private theorem translatedProfile_bv (f : ℝ → ℝ) (hv : BoundedVariationOn f univ) (t : ℝ) :
    BoundedVariationOn (fun x => f (x + t)) univ :=
  ne_top_of_le_ne_top hv (eVariationOn.comp_le_of_monotoneOn f (fun x => x + t)
    (fun _ _ _ _ h => add_le_add h le_rfl) (fun _ _ => mem_univ _))

private theorem translatedProfile_compact (f : ℝ → ℝ) (hc : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun x => f (x + t)) :=
  hc.comp_homeomorph (Homeomorph.addRight t)

/-- The actual whole-line unitary translates the original BV source pointwise. -/
theorem logTranslation_realSourceLp (f : ℝ → ℝ) (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) (t : ℝ) :
    logTranslationCLM t (realSourceLp f hv hc) = realSourceLp (fun x => f (x + t))
      (translatedProfile_bv f hv t) (translatedProfile_compact f hc t) := by
  apply Lp.ext
  have ht : (logTranslationCLM t (realSourceLp f hv hc) : ℝ → ℂ) =ᵐ[volume]
      fun x => (realSourceLp f hv hc : ℝ → ℂ) (x + t) :=
    Lp.coeFn_compMeasurePreserving _ (MellinL2.realTranslation_measurePreserving t)
  have hs := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp
    (realSourceLp_coeFn f hv hc)
  filter_upwards [ht, hs, realSourceLp_coeFn (fun x => f (x + t))
    (translatedProfile_bv f hv t) (translatedProfile_compact f hc t)] with x htx hsx hgx
  change (realSourceLp f hv hc : ℝ → ℂ) (x + t) = (f (x + t) : ℂ) at hsx
  exact (htx.trans hsx).trans hgx.symm

/-- Translation of the original source costs no additional Gamma in the high-tail probe. -/
theorem norm_inner_generatorTail_translated_source_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) (t : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    ‖inner ℂ (wholeLineGeneratorTail A (realSourceLp f hv hc))
      (logTranslationCLM t (realSourceLp f hv hc))‖ ≤
      32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  rw [logTranslation_realSourceLp]
  have h := norm_inner_generatorTail_sources_le f (fun x => f (x + t)) hv hc
    (translatedProfile_bv f hv t) (translatedProfile_compact f hc t) hA
  have hΓ : levyEnergy (fun x => f (x + t)) = levyEnergy f := by
    simpa only [sub_neg_eq_add] using
      SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := f) (-t)
  rw [hΓ] at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- The adjoint translation gives the same payment when the high tail is translated. -/
theorem norm_inner_translated_generatorTail_source_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) (t : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    ‖inner ℂ (logTranslationCLM t (wholeLineGeneratorTail A (realSourceLp f hv hc)))
      (realSourceLp f hv hc)‖ ≤ 32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  rw [inner_logTranslationCLM]
  exact norm_inner_generatorTail_translated_source_le f hv hc (-t) hA

/-- Physical translation correlation, with the existing whole-line unitary and its literal sign convention. -/
def wholeLineTranslationCorrelation (t : ℝ) (F : LineH) : ℝ :=
  (inner ℂ (logTranslationCLM t F) F).re

/-- A unitary physical correlation is bounded by original L² square mass. -/
theorem abs_wholeLineTranslationCorrelation_le (t : ℝ) (F : LineH) :
    |wholeLineTranslationCorrelation t F| ≤ ‖F‖ ^ 2 := by
  have hn : ‖logTranslationCLM t F‖ = ‖F‖ := (MellinL2.additiveTranslationUnitary t).norm_map F
  calc
    _ ≤ ‖inner ℂ (logTranslationCLM t F) F‖ := Complex.abs_re_le_norm _
    _ ≤ ‖logTranslationCLM t F‖ * ‖F‖ := norm_inner_le_norm _ _
    _ = _ := by rw [hn, pow_two]

/-- Removing all high generator labels has a uniform Gamma cost at every real lag. -/
theorem abs_allLevel_translation_head_error_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) (t : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    |wholeLineTranslationCorrelation t (realSourceLp f hv hc) -
      wholeLineTranslationCorrelation t
        (realSourceLp f hv hc - wholeLineGeneratorTail A (realSourceLp f hv hc))| ≤
      96 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  let F := realSourceLp f hv hc
  let r := wholeLineGeneratorTail A F
  let K := 32 * levyEnergy f / (1 + Real.log (A : ℝ))
  have h1 : ‖inner ℂ (logTranslationCLM t r) F‖ ≤ K :=
    norm_inner_translated_generatorTail_source_le f hv hc t hA
  have h2 : ‖inner ℂ (logTranslationCLM t F) r‖ ≤ K := by
    rw [norm_inner_symm]
    exact norm_inner_generatorTail_translated_source_le f hv hc t hA
  have h3 : ‖inner ℂ (logTranslationCLM t r) r‖ ≤ K := by
    have hn : ‖logTranslationCLM t r‖ = ‖r‖ := (MellinL2.additiveTranslationUnitary t).norm_map r
    calc
      _ ≤ ‖logTranslationCLM t r‖ * ‖r‖ := norm_inner_le_norm _ _
      _ = ‖r‖ ^ 2 := by rw [hn, pow_two]
      _ ≤ K := norm_wholeLineGeneratorTail_source_sq_le f hv hc hA
  have he : inner ℂ (logTranslationCLM t F) F -
      inner ℂ (logTranslationCLM t (F - r)) (F - r) =
      inner ℂ (logTranslationCLM t r) F + inner ℂ (logTranslationCLM t F) r -
        inner ℂ (logTranslationCLM t r) r := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  change |(inner ℂ (logTranslationCLM t F) F).re -
    (inner ℂ (logTranslationCLM t (F - r)) (F - r)).re| ≤ _
  rw [← Complex.sub_re, he]
  calc
    _ ≤ ‖inner ℂ (logTranslationCLM t r) F + inner ℂ (logTranslationCLM t F) r -
        inner ℂ (logTranslationCLM t r) r‖ := Complex.abs_re_le_norm _
    _ ≤ (‖inner ℂ (logTranslationCLM t r) F‖ + ‖inner ℂ (logTranslationCLM t F) r‖) +
        ‖inner ℂ (logTranslationCLM t r) r‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (K + K) + K := add_le_add (add_le_add h1 h2) h3
    _ = _ := by dsimp only [K]; ring

/-- The retained physical vector is precisely the full generator head for original finite cell sources. -/
theorem realSourceLp_sub_generatorTail_wholeCell (c : ℕ → ℝ) (X A : ℕ) :
    realSourceLp (wholeCellProfile c X) (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 -
      wholeLineGeneratorTail A (realSourceLp (wholeCellProfile c X)
        (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2) =
      U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))) := by
  rw [realSourceLp_wholeCellProfile, wholeLineGeneratorTail_apply,
    wholeLineLogCellEmbedding_adjoint_self, ← map_sub]
  congr 1
  abel

/-- The unitary correlation is the original whole-line profile integral. -/
theorem wholeLineTranslationCorrelation_realSource (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) (t : ℝ) :
    wholeLineTranslationCorrelation t (realSourceLp f hv hc) = ∫ x, f x * f (x + t) := by
  have ht : (logTranslationCLM t (realSourceLp f hv hc) : ℝ → ℂ) =ᵐ[volume]
      fun x => (realSourceLp f hv hc : ℝ → ℂ) (x + t) :=
    Lp.coeFn_compMeasurePreserving _ (MellinL2.realTranslation_measurePreserving t)
  have hs := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp
    (realSourceLp_coeFn f hv hc)
  have hi : inner ℂ (logTranslationCLM t (realSourceLp f hv hc)) (realSourceLp f hv hc) =
      ((∫ x, f x * f (x + t) : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, ((f x * f (x + t) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ht, hs, realSourceLp_coeFn f hv hc] with x htx hsx hfx
        change (realSourceLp f hv hc : ℝ → ℂ) (x + t) = (f (x + t) : ℂ) at hsx
        rw [htx, hsx, hfx, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
      _ = _ := integral_complex_ofReal
  rw [wholeLineTranslationCorrelation, hi, Complex.ofReal_re]

/-- All real lags of the original finite cell profile admit the same all-level generator approximation. -/
theorem abs_wholeCell_allLag_head_error_le (c : ℕ → ℝ) (X : ℕ) (t : ℝ)
    {A : ℕ} (hA : 1 ≤ A) :
    |(∫ x, wholeCellProfile c X x * wholeCellProfile c X (x + t)) -
      wholeLineTranslationCorrelation t
        (U (logCellGeneratorHead A (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
      96 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ)) := by
  have h := abs_allLevel_translation_head_error_le (wholeCellProfile c X)
    (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 t hA
  rw [wholeLineTranslationCorrelation_realSource, realSourceLp_sub_generatorTail_wholeCell] at h
  exact h

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.inner_wholeLineGeneratorTail_eq_tail
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.norm_inner_generatorTail_sources_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.norm_inner_generatorTail_translated_source_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_allLevel_translation_head_error_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_wholeCell_allLag_head_error_le
