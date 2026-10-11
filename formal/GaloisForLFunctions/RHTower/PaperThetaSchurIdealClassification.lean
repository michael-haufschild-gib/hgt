import GaloisForLFunctions.RHTower.PaperThetaSchurCompactGap

/-!
# Proven paper ideal cost of the full native theta mode operator

Compactness of the full quartic mode operator is exactly the existing GTA asymptotic
orientation criterion. The proven TraceCone ideal weight turns this into a zero/infinity
classification. Neither compactness nor RH is assumed in the classification theorems.
-/

namespace RHTower.HedenmalmThetaSource
noncomputable section
open GaloisForLFunctions.HTGeometry Filter Classical
open scoped Topology NNReal ENNReal

theorem paperThetaSchurModeOperator_compact_of_rh (S : PaperThetaSchurFamily)
    (hRH : RiemannHypothesis) : IsCompactOperator (paperThetaSchurModeOperator S) := by
  apply isCompactOperator_of_diag_tendsto_cofinite (HilbertSchmidt.lpBasis PaperThetaSchurMode)
    (paperThetaSchurModeOperator_basis S)
  apply Metric.tendsto_nhds.2
  intro ε hε
  have htotal := eventually_thetaSourceStageSchurPositiveQuarticCharge_lt_of_rh hRH hε
  filter_upwards [paperThetaSchur_stage_tendsto.eventually htotal] with p hp
  have hq := (paperThetaSchurModeCharge_le_total S p).trans_lt (hp (S p.1))
  simpa only [dist_zero_right, norm_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperThetaSchurModeCharge_nonneg S p)] using hq

/-- The full source mode operator is compact exactly at the GTA orientation endpoint. -/
theorem paperThetaSchurModeOperator_compact_iff (S : PaperThetaSchurFamily) :
    IsCompactOperator (paperThetaSchurModeOperator S) ↔ RiemannHypothesis := by
  constructor
  · intro hc
    by_contra hn
    obtain ⟨δ, hδ, hgap⟩ := paperThetaSchur_uniform_compact_gap_of_not_rh hn
    have hz := hgap S ⟨paperThetaSchurModeOperator S, hc⟩
    simp only [sub_self, norm_zero] at hz
    exact (not_lt_of_ge hz) hδ
  · exact paperThetaSchurModeOperator_compact_of_rh S

/-- The full-mode completion retains exactly the native uniform stage-charge criterion. -/
theorem paperThetaSchurModeOperator_compact_iff_uniformDecay (S : PaperThetaSchurFamily) :
    IsCompactOperator (paperThetaSchurModeOperator S) ↔
      ThetaSourceSchurPositiveQuarticChargeUniformDecay := by
  rw [paperThetaSchurModeOperator_compact_iff,
    riemannHypothesis_iff_thetaSourceSchurPositiveQuarticChargeUniformDecay]

/-- Proven upstream ideal weight applied to every original theta spectral mode. -/
theorem paperThetaSchurModeOperator_traceCost (S : PaperThetaSchurFamily) :
    compactOperatorTraceCost PaperThetaSchurSpace (paperThetaSchurModeOperator S) =
      if RiemannHypothesis then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperThetaSchurModeOperator_compact_iff]

theorem paperThetaSchurModeOperator_traceCost_zero_iff (S : PaperThetaSchurFamily) :
    compactOperatorTraceCost PaperThetaSchurSpace (paperThetaSchurModeOperator S) = 0 ↔
      RiemannHypothesis := by
  rw [compactOperatorTraceCost_eq_zero_iff, paperThetaSchurModeOperator_compact_iff]

theorem paperThetaSchurModeOperator_traceCost_top_iff (S : PaperThetaSchurFamily) :
    compactOperatorTraceCost PaperThetaSchurSpace (paperThetaSchurModeOperator S) = ∞ ↔
      ¬ RiemannHypothesis := by
  rw [compactOperatorTraceCost_eq_top_iff, paperThetaSchurModeOperator_compact_iff]

/-- Compact corrections may mix stages and modes; they still cannot change the paper cost. -/
theorem paperThetaSchurModeOperator_add_compact_traceCost (S : PaperThetaSchurFamily)
    (K : compactOperatorStarAlgebra PaperThetaSchurSpace) :
    compactOperatorTraceCost PaperThetaSchurSpace (paperThetaSchurModeOperator S + K.1) =
      if RiemannHypothesis then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperThetaSchurModeOperator_traceCost]

/-- The zero/infinity classification is independent of every Schur choice. -/
theorem paperThetaSchurModeOperator_traceCost_choice_independent
    (S T : PaperThetaSchurFamily) :
    compactOperatorTraceCost PaperThetaSchurSpace (paperThetaSchurModeOperator S) =
      compactOperatorTraceCost PaperThetaSchurSpace (paperThetaSchurModeOperator T) := by
  rw [paperThetaSchurModeOperator_traceCost, paperThetaSchurModeOperator_traceCost]

theorem paperThetaSchurModeOperator_essential_gap_iff (S : PaperThetaSchurFamily) :
    0 < compactIdealDistance (paperThetaSchurModeOperator S) ↔ ¬ RiemannHypothesis := by
  constructor
  · intro hp hRH
    have hz := compactIdealDistance_eq_zero_of_isCompactOperator _
      (paperThetaSchurModeOperator_compact_of_rh S hRH)
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · intro hn
    obtain ⟨δ, hδ, hgap⟩ := paperThetaSchur_uniform_compact_gap_of_not_rh hn
    exact hδ.trans_le (le_compactIdealDistance _ δ fun K hK => hgap S ⟨K, hK⟩)

/-- A concrete family is fixed unconditionally, so no Schur-selection premise remains. -/
theorem paperThetaCanonicalSchurModeOperator_classification :
    (IsCompactOperator (paperThetaSchurModeOperator paperThetaCanonicalSchurFamily) ↔
      RiemannHypothesis) ∧
    compactOperatorTraceCost PaperThetaSchurSpace
      (paperThetaSchurModeOperator paperThetaCanonicalSchurFamily) =
        if RiemannHypothesis then 0 else ∞ :=
  ⟨paperThetaSchurModeOperator_compact_iff _, paperThetaSchurModeOperator_traceCost _⟩

end
end RHTower.HedenmalmThetaSource
