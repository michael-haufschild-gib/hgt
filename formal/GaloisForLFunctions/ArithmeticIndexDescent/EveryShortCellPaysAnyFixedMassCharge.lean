import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionsHaveOnlyPresentationRadicals

/-!
# Arbitrarily strong source coercivity on a short cell

The arithmetic section estimate at a single site retains logarithmic gain as
the width shrinks. The two pole moments have bounded cost, so every fixed mass
charge is paid on all sufficiently short cells, uniformly over profiles and
translations. This is the one-cell consequence of the existing section law.
-/

open MeasureTheory Set RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

private theorem shortProfile_logarithmic_floor {f : ℝ → ℝ} {w : ℝ}
    (hf : ContDiff ℝ 2 f) (hs : ∀ u, u ∉ Icc 0 w → f u = 0)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hw : w ≤ spacingRatio * atomSpacing 1) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - spacingConstant - (Real.exp 1 + 1)) *
        sectionMass f ≤ weilPair f f := by
  have hsec : arithmeticSection 1 (fun _ => f) = f := by
    ext u
    simp only [arithmeticSection, Finset.Icc_self, Finset.sum_singleton,
      Nat.cast_one, Real.log_one, sub_zero]
  have hM := markovEnergy_arithmeticSection_ge (G := fun _ => f)
    (fun _ => hf) (fun _ => hs) (le_refl (1 : ℕ)) hw0 hw
  rw [hsec, Nat.cast_one, Real.log_one, sub_zero] at hM
  have hA := poleA_profile_sq_le hf.continuous hw0.le hs
  have hB := poleB_profile_sq_le hf.continuous hw0.le hs
  have hpol : -(w * (Real.exp w + 1) * sectionMass f) ≤ 2 * poleA f * poleB f := by
    nlinarith only [hA, hB, sq_nonneg (poleA f + poleB f)]
  have hcost : w * (Real.exp w + 1) ≤ Real.exp 1 + 1 := by
    simpa only [one_mul] using mul_le_mul hw1
      (add_le_add (Real.exp_le_exp.mpr hw1) (le_refl (1 : ℝ)))
      (by positivity : 0 ≤ Real.exp w + 1) (by norm_num : (0 : ℝ) ≤ 1)
  have hp := mul_le_mul_of_nonneg_right hcost (sectionMass_nonneg f)
  have hW := weilPair_eq_markovEnergy_add_poleProduct
    (show f ∈ realTests from ⟨hf, profile_hasCompactSupport hs⟩)
  change (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - spacingConstant) *
    sectionMass f ≤ markovEnergy (cx f) at hM
  linarith only [hM, hpol, hp, hW]

/-- A single arithmetic cell pays any prescribed square-mass charge. -/
theorem exists_shortProfile_weil_coercivity (L : ℝ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, u ∉ Icc 0 w → f u = 0) →
        L * sectionMass f ≤ weilPair f f := by
  let q := 2 * gammaHardyPhaseRate 0 - spacingConstant - (Real.exp 1 + 1) - L
  refine ⟨min 1 (min (spacingRatio * atomSpacing 1) (Real.exp q)), ?_, ?_⟩
  · exact lt_min zero_lt_one
      (lt_min (mul_pos spacingRatio_pos (atomSpacing_pos (le_refl 1))) (Real.exp_pos _))
  intro w hw0 hww f hf hs
  have hw1 : w ≤ 1 := (hww.trans_le (min_le_left _ _)).le
  have hw : w ≤ spacingRatio * atomSpacing 1 :=
    (hww.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hwe : w < Real.exp q := hww.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : Real.log w < q := by
    have hh := Real.log_lt_log hw0 hwe
    rwa [Real.log_exp] at hh
  have hc : L ≤ 2 * gammaHardyPhaseRate 0 + Real.log (1 / w) -
      spacingConstant - (Real.exp 1 + 1) := by
    rw [Real.log_div (by norm_num) hw0.ne', Real.log_one]
    dsimp [q] at hlog
    linarith only [hlog]
  exact (mul_le_mul_of_nonneg_right hc (sectionMass_nonneg f)).trans
    (shortProfile_logarithmic_floor hf hs hw0 hw1 hw)

/-- The same threshold works at every centre and for every compact real C² profile. -/
theorem exists_shortCell_weil_coercivity (L : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ b : ℝ, ∀ g : realTests,
      (∀ u, δ / 2 < |u - b| → g.1 u = 0) →
      L * sectionMass g.1 ≤ realWeilForm g g := by
  obtain ⟨δ₀, hδ₀, hbound⟩ := exists_shortProfile_weil_coercivity L
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδlt b g hs
  let a := δ / 2 - b
  have hf : ContDiff ℝ 2 (scaleShift a g.1) := (scaleShift_mem a g.2).1
  have hsupport : ∀ u, u ∉ Icc 0 δ → scaleShift a g.1 u = 0 := by
    intro u hu
    change g.1 (u - a) = 0
    apply hs
    by_cases h0 : 0 ≤ u
    · have hδu : δ < u := lt_of_not_ge fun h => hu ⟨h0, h⟩
      have hdist : δ / 2 < (u - a) - b := by dsimp [a]; linarith only [hδu]
      exact hdist.trans_le (le_abs_self _)
    · have hu0 : u < 0 := lt_of_not_ge h0
      have hdist : δ / 2 < -((u - a) - b) := by dsimp [a]; linarith only [hu0]
      exact hdist.trans_le (neg_le_abs _)
  have hh := hbound δ hδ hδlt (scaleShift a g.1) hf hsupport
  have hm : sectionMass (scaleShift a g.1) = sectionMass g.1 :=
    integral_sub_right_eq_self (fun u => g.1 u ^ 2) a
  rw [hm, weilPair_scaleShift_same] at hh
  exact hh

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_shortCell_weil_coercivity
