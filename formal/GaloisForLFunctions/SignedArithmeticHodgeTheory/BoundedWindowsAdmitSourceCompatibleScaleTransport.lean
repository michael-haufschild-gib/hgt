import GaloisForLFunctions.SignedArithmeticHodgeTheory.TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound

/-!
# Scale transport on bounded source windows

The exact Weil isometry is bounded in the original graph norm when both the
source aperture and the translation range are fixed. The constant records the
theta mass weight on the enlarged aperture; it is not uniform under exhaustion.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar Zeta23

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics ArithmeticIndexDescent

/-- The translated support occupies the correspondingly enlarged source window. -/
theorem sourceTranslate_support_bound (R t : ℝ) (f : realTests)
    (hf : ∀ u, R < |u| → f.1 u = 0) :
    ∀ u, R + |t| < |u| → (sourceTranslate t f).1 u = 0 := by
  intro u hu
  apply hf (u - t)
  have htri : |u| ≤ |u - t| + |t| := by
    simpa only [sub_add_cancel] using abs_add_le (u - t) t
  linarith only [hu, htri]

theorem translatedSourceGraph_inverse (f : realTests) (t : ℝ) :
    translatedSourceGraph (sourceTranslate t f) (-t) = realTestGraphLift f := by
  unfold translatedSourceGraph
  congr 1
  apply Subtype.ext
  change scaleShift (-t) (scaleShift t f.1) = f.1
  rw [← scaleShift_add, neg_add_cancel, scaleShift_zero]

/-- Ordinary square mass has a global bound in the actual source graph. -/
theorem exists_sectionMass_le_graph_norm_sq :
    ∃ K : ℝ, 0 < K ∧ ∀ f : realTests,
      sectionMass f.1 ≤ K * ‖realTestGraphLift f‖ ^ 2 := by
  obtain ⟨K, hK, hweight⟩ := exists_exp_le_sourceGraphMassWeight 0 le_rfl
  refine ⟨K, hK, fun f => ?_⟩
  have hw : ∀ u, 1 ≤ K * sourceGraphMassWeight u := by
    intro u
    simpa only [zero_mul, Real.exp_zero] using hweight u
  calc
    sectionMass f.1 ≤ weightedSectionMass (fun u => K * sourceGraphMassWeight u) f :=
      sectionMass_le_weightedSectionMass (continuous_sourceGraphMassWeight.const_mul K) hw f
    _ = K * weightedSectionMass sourceGraphMassWeight f := by
      change (∫ u, f.1 u ^ 2 * (K * sourceGraphMassWeight u)) =
        K * ∫ u, f.1 u ^ 2 * sourceGraphMassWeight u
      calc
        _ = ∫ u, K * (f.1 u ^ 2 * sourceGraphMassWeight u) :=
          integral_congr_ae (Eventually.of_forall fun u => by ring)
        _ = _ := integral_const_mul _ _
    _ ≤ K * ‖realTestGraphLift f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (weightedMass_le_graph_norm_sq f) hK.le

/-- Fixed aperture and bounded shifts admit one graph bound for all source profiles. -/
theorem exists_boundedWindow_scaleTransport (R T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : realTests) (t : ℝ),
      (∀ u, R < |u| → f.1 u = 0) → |t| ≤ T →
      ‖translatedSourceGraph f t‖ ^ 2 ≤ C * ‖realTestGraphLift f‖ ^ 2 := by
  obtain ⟨K, hK, hmass⟩ := exists_sectionMass_le_graph_norm_sq
  let L := |R| + |T| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨v, _, hv⟩ := (isCompact_Icc (a := -L) (b := L)).exists_isMaxOn
    ⟨0, by constructor <;> linarith only [hL]⟩ continuous_sourceGraphMassWeight.continuousOn
  let M := sourceGraphMassWeight v
  have hM : 0 < M := sourceGraphMassWeight_pos v
  let C := weilBilinConst + sourceGraphMassPenalty * M * K
  have hpen : 0 < sourceGraphMassPenalty := sourceGraphMassPenalty_pos
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos weilBilinConst_pos (mul_pos (mul_pos hpen hM) hK)
  refine ⟨C, hC, fun f t hsupport ht => ?_⟩
  let g := sourceTranslate t f
  have hgweight : weightedSectionMass sourceGraphMassWeight g ≤ M * sectionMass g.1 := by
    apply weightedSectionMass_le_cellCharge continuous_sourceGraphMassWeight
    intro u hu
    have hr : |u - t| ≤ R := by
      apply le_of_not_gt
      intro h
      exact hu (hsupport (u - t) h)
    have htri : |u| ≤ |u - t| + |t| := by
      simpa only [sub_add_cancel] using abs_add_le (u - t) t
    have hsu : |u| ≤ L := by
      dsimp [L]
      linarith only [hr, ht, htri, le_abs_self R, le_abs_self T]
    exact hv (abs_le.mp hsu)
  have hsame : realWeilForm g g = realWeilForm f f :=
    weilPair_scaleShift_same t f.1 f.1
  have hW : realWeilForm f f ≤ weilBilinConst * ‖realTestGraphLift f‖ ^ 2 := by
    rw [← weilForm_realTestGraphLift, weilForm_eq_weilBilin, pow_two]
    exact (le_abs_self _).trans (abs_weilBilin_le _ _)
  have hg := norm_realTestGraphLift_sq_le_weil_add_weightedMass g
  rw [hsame] at hg
  have hgMass : sectionMass g.1 = sectionMass f.1 := sectionMass_sourceTranslate t f
  rw [hgMass] at hgweight
  calc
    ‖translatedSourceGraph f t‖ ^ 2 ≤
        realWeilForm f f + sourceGraphMassPenalty * weightedSectionMass sourceGraphMassWeight g := hg
    _ ≤ realWeilForm f f + sourceGraphMassPenalty * (M * sectionMass f.1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hgweight hpen.le)
    _ ≤ weilBilinConst * ‖realTestGraphLift f‖ ^ 2 +
        sourceGraphMassPenalty * (M * (K * ‖realTestGraphLift f‖ ^ 2)) :=
      add_le_add hW (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hmass f) hM.le) hpen.le)
    _ = C * ‖realTestGraphLift f‖ ^ 2 := by dsimp [C]; ring

/-- Scale transport is uniformly reversible on every fixed source window. -/
theorem exists_boundedWindow_two_sided_scaleTransport (R T : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : realTests) (t : ℝ),
      (∀ u, R < |u| → f.1 u = 0) → |t| ≤ T →
      ‖translatedSourceGraph f t‖ ^ 2 ≤ C * ‖realTestGraphLift f‖ ^ 2 ∧
        ‖realTestGraphLift f‖ ^ 2 ≤ C * ‖translatedSourceGraph f t‖ ^ 2 := by
  obtain ⟨C₁, _, h₁⟩ := exists_boundedWindow_scaleTransport R T
  obtain ⟨C₂, _, h₂⟩ := exists_boundedWindow_scaleTransport (R + |T|) T
  let C := max 1 (max C₁ C₂)
  have h₁C : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h₂C : C₂ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, le_max_left _ _, fun f t hf ht => ?_⟩
  have hg : ∀ u, R + |T| < |u| → (sourceTranslate t f).1 u = 0 := by
    intro u hu
    apply sourceTranslate_support_bound R t f hf u
    linarith only [hu, ht, le_abs_self T]
  have hinv := h₂ (sourceTranslate t f) (-t) hg (by simpa only [abs_neg] using ht)
  rw [translatedSourceGraph_inverse] at hinv
  constructor
  · exact (h₁ f t hf ht).trans (mul_le_mul_of_nonneg_right h₁C (sq_nonneg _))
  · exact hinv.trans (mul_le_mul_of_nonneg_right h₂C (sq_nonneg _))

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_boundedWindow_scaleTransport
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_boundedWindow_two_sided_scaleTransport
