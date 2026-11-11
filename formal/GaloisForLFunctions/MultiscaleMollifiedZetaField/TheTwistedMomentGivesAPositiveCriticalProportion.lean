import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFixedDetectorKeepsTheMatchedBlockBounds
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheMatchedDetectorBoundsAreUniform
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShortLevinsonMollifierHasAPositiveScalarMargin
import GaloisForLFunctions.RHTower.LevinsonGateFromDyadicMeanSquare
import GaloisForLFunctions.RHTower.LevinsonOddFiberDensityGeneral

/-!
# A critical-zero proportion from the short twisted moment

One mollifier of length `floor(U^(13/50))` serves the entire dyadic gate.
The low head is negligible, intermediate blocks fit into the global
slack, and high blocks have scalar below `18/5`. At displacement `13/10`,
Levinson's positive margin gives an explicit positive odd-fibre proportion.
-/

open Complex Filter MeasureTheory Set Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The fixed upper-height coefficients satisfy the required estimate on every dyadic block. -/
theorem eventually_shortFixedDetector_all_blocks {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop, ∀ a v d : ℝ,
      20 ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
      13 / 10 ≤ d * Real.log U → d * Real.log (U - 1) ≤ 13 / 10 →
      shortFixedDetectorBlockEnergy U d a v ≤
        (18 / 5 + ε) * (v - a) + ε * (a + U / Real.log U) := by
  obtain ⟨C, hC, hmatched⟩ := exists_uniform_matchedDetectorBlockEnergy_bound
  let α : ℝ := ε / (2 * (18 / 5 + 1))
  let β : ℝ := ε / (2 * (1 + α))
  let δ : ℝ := ε / (2 * ((1 + α) * C + 1))
  have hα : 0 < α := by dsimp only [α]; positivity
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hαc : (1 + α) * (18 / 5 : ℝ) ≤ 18 / 5 + ε := by
    dsimp only [α]
    nlinarith only [hε]
  have hβeq : (1 + α) * β = ε / 2 := by
    dsimp only [β]
    field_simp [show 1 + α ≠ 0 by positivity] <;> ring
  have hδle : ((1 + α) * C) * δ ≤ ε / 2 := by
    have he : (2 * ((1 + α) * C + 1)) * δ = ε := by
      dsimp only [δ]
      field_simp [show (1 + α) * C + 1 ≠ 0 by positivity]
    nlinarith only [he, hδ]
  filter_upwards [hmatched, eventually_uniform_matchedDetectorBlockEnergy_high_bound hδ hβ,
    eventually_shortFixedDetectorBlockEnergy_stability hα (half_pos hε),
    eventually_shortFixedDetectorBlockEnergy_low_le hε, eventually_gt_atTop (1 : ℝ)]
    with U hmi hhi hsi hli hU
  intro a v d ha hav hv2 hvU hg0 hg1
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hUL : 0 ≤ U / Real.log U := by
    exact (div_pos (zero_lt_one.trans hU) (Real.log_pos hU)).le
  have hslack : ε * U / Real.log U ≤
      (18 / 5 + ε) * (v - a) + ε * (a + U / Real.log U) := by
    have h0 := mul_nonneg (show 0 ≤ 18 / 5 + ε by positivity) (sub_nonneg.mpr hav)
    have h1 := mul_nonneg hε.le ha0
    linarith only [h0, h1]
  by_cases hlow : a ≤ U ^ (53 / 100 : ℝ)
  · exact (hli a v d ha hav hv2 hlow hg0 hg1).trans hslack
  have hlarge : U ^ (53 / 100 : ℝ) ≤ a := (lt_of_not_ge hlow).le
  have hstable := hsi a v d ha hav hvU hg0 hg1
  by_cases hhigh : δ * U / Real.log U ≤ a
  · have hsharp := hhi a v d hlarge hav hv2 hvU hg0 hg1 hhigh
    have he := hstable.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hsharp (by positivity : 0 ≤ 1 + α)) _)
    have hc := mul_le_mul_of_nonneg_right hαc (sub_nonneg.mpr hav)
    have hba := congrArg (fun x : ℝ => x * a) hβeq
    have hsa := mul_nonneg hε.le ha0
    have hsU := mul_nonneg hε.le hUL
    nlinarith only [he, hc, hba, hsa, hsU]
  · have hcoarse := hmi a v d hlarge hav hv2 hvU hg0 hg1
    have hsmall : ((1 + α) * C) * a ≤ (ε / 2) * (U / Real.log U) := by
      calc
        _ ≤ ((1 + α) * C) * (δ * (U / Real.log U)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [mul_div_assoc] using (lt_of_not_ge hhigh).le
        _ = (((1 + α) * C) * δ) * (U / Real.log U) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hδle hUL
    have he := hstable.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hcoarse (by positivity : 0 ≤ 1 + α)) _)
    apply le_trans _ hslack
    nlinarith only [he, hsmall]

/-- The two-main-term twisted moment proves the literal dyadic detector law with one fixed mollifier. -/
theorem shortLevinson_dyadicDetectorMeanSquareLaw : DyadicDetectorMeanSquareLaw (13 / 10) (18 / 5) := by
  intro ε hε
  filter_upwards [eventually_shortFixedDetector_all_blocks hε,
    eventually_shortLevinsonCoefficients_admissible (13 / 10) (by norm_num)] with U hblock had
  obtain ⟨hN, hb1, hbn, hbreal, hM, hmass, hlog⟩ := had
  refine ⟨shortLevinsonCoefficientMass U, shortLevinsonCoefficients (13 / 10) U,
    shortLevinsonCutoff U, hN, hb1, hbn, hbreal, hM, hmass, hlog, ?_⟩
  intro σ hσlo hσhi hg0 hg1 a v ha hav hv2 hvU
  have hh := hblock a v (1 / 2 - σ) ha hav hv2 hvU hg0 hg1
  simpa only [shortFixedDetectorBlockEnergy,
    show (1 / 2 : ℝ) - (1 / 2 - σ) = σ by ring] using hh

/-- The short twisted moment supplies Levinson's reciprocal-log mean-square gate. -/
theorem shortLevinson_reciprocalLogMeanSquareGate :
    LevinsonReciprocalLogMeanSquareGate (13 / 10) (18 / 5) :=
  levinsonReciprocalLogMeanSquareGate_of_dyadicLaw (by norm_num)
    shortLevinson_dyadicDetectorMeanSquareLaw

/-- An explicit positive fraction of the zero census has odd multiplicity on the critical line. -/
theorem eventually_critical_odd_fiber_proportion_from_short_twisted_moment :
    ∀ᶠ U : ℝ in atTop,
      ((1 - Real.log (18 / 5 : ℝ) / (13 / 10)) / 4) * (xiPosZeroCount U : ℝ) ≤
        (xiOddFiberCount U : ℝ) := by
  have hmargin := levinsonShortScalar_positive_margin
  simpa only [zero_add] using eventually_oddFiber_ge_of_gate_of_Y_pos_general
    (κ₀ := 0) (by norm_num) (by norm_num : (0 : ℝ) < 13 / 10)
    (by norm_num : (1 : ℝ) ≤ 18 / 5)
    (show 0 < (1 - Real.log (18 / 5 : ℝ) / (13 / 10)) / 4 by positivity)
    (by linarith only [hmargin])
    (levinsonMeanSquareGateOfYPos_of_reciprocalLogGate shortLevinson_reciprocalLogMeanSquareGate)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
