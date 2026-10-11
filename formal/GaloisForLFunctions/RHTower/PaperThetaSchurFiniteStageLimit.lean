import GaloisForLFunctions.RHTower.PaperThetaSchurIdealClassification
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity

/-!
# Finite theta-stage cutoffs converge strongly, while norm convergence is exactly RH

Every finite stage cutoff has zero paper ideal cost. These actual finite-mode operators
converge on every vector to the full charge operator. Uniform operator-norm convergence is
equivalent to RH; if RH fails, one positive gap persists at every finite cutoff.
-/

namespace RHTower.HedenmalmThetaSource
noncomputable section
open GaloisForLFunctions.HTGeometry ContinuousLinearMap Filter Classical
open scoped Topology NNReal ENNReal

theorem paperThetaSchurEarlyModes_tendsto :
    Tendsto paperThetaSchurEarlyModes atTop atTop := by
  apply tendsto_atTop.2
  intro s
  apply s.eventually_all.2
  intro p _
  filter_upwards [eventually_ge_atTop (p.1 + 1)] with N hN
  exact (mem_paperThetaSchurEarlyModes N p).2 (by omega)

/-- The literal operator retaining every mode of every stage below `N`. -/
def paperThetaSchurFiniteStageOperator (S : PaperThetaSchurFamily) (N : ℕ) :
    PaperThetaSchurSpace →L[ℂ] PaperThetaSchurSpace :=
  hsTruncation (HilbertSchmidt.lpBasis PaperThetaSchurMode)
    (paperThetaSchurModeOperator S) (paperThetaSchurEarlyModes N)

theorem paperThetaSchurFiniteStageOperator_basis (S : PaperThetaSchurFamily)
    (N : ℕ) (p : PaperThetaSchurMode) :
    paperThetaSchurFiniteStageOperator S N (HilbertSchmidt.lpBasis PaperThetaSchurMode p) =
      if p.1 < N then (paperThetaSchurModeCharge S p : ℂ) •
        HilbertSchmidt.lpBasis PaperThetaSchurMode p else 0 := by
  simp only [paperThetaSchurFiniteStageOperator, hsTruncation_apply_basis,
    mem_paperThetaSchurEarlyModes, paperThetaSchurModeOperator_basis]

theorem paperThetaSchurFiniteStageOperator_compact (S : PaperThetaSchurFamily) (N : ℕ) :
    IsCompactOperator (paperThetaSchurFiniteStageOperator S N) :=
  isCompactOperator_hsTruncation _ _ _

/-- Every finite stage cutoff has zero ideal cost, without an arithmetic premise. -/
theorem paperThetaSchurFiniteStageOperator_traceCost (S : PaperThetaSchurFamily) (N : ℕ) :
    compactOperatorTraceCost PaperThetaSchurSpace (paperThetaSchurFiniteStageOperator S N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).2 (paperThetaSchurFiniteStageOperator_compact S N)

/-- All finite stage cutoffs converge on every full square-summable vector. -/
theorem paperThetaSchurFiniteStageOperator_strong_tendsto (S : PaperThetaSchurFamily)
    (v : PaperThetaSchurSpace) :
    Tendsto (fun N => paperThetaSchurFiniteStageOperator S N v) atTop
      (𝓝 (paperThetaSchurModeOperator S v)) := by
  have ht := (hasSum_inner_smul (HilbertSchmidt.lpBasis PaperThetaSchurMode)
    (paperThetaSchurModeOperator S) v).comp paperThetaSchurEarlyModes_tendsto
  simpa only [paperThetaSchurFiniteStageOperator, hsTruncation_apply, Function.comp_def] using ht

theorem paperThetaSchurFiniteStageOperator_norm_tendsto_of_rh (S : PaperThetaSchurFamily)
    (hRH : RiemannHypothesis) :
    Tendsto (paperThetaSchurFiniteStageOperator S) atTop (𝓝 (paperThetaSchurModeOperator S)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (eventually_thetaSourceStageSchurPositiveQuarticCharge_lt_of_rh hRH (half_pos hε))
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have htail : ∀ p : PaperThetaSchurMode, p ∉ paperThetaSchurEarlyModes N →
      ‖(paperThetaSchurModeCharge S p : ℂ)‖ ≤ ε / 2 := by
    intro p hp
    have hstage : N ≤ p.1 := by simpa using hp
    have hq := (paperThetaSchurModeCharge_le_total S p).trans_lt
      (hN₀ p.1 (hN.trans hstage) (S p.1))
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperThetaSchurModeCharge_nonneg S p)] using hq.le
  have hn := norm_sub_hsTruncation_diag_le (HilbertSchmidt.lpBasis PaperThetaSchurMode)
    (paperThetaSchurModeOperator_basis S) (paperThetaSchurEarlyModes N) (half_pos hε).le htail
  rw [dist_eq_norm, norm_sub_rev]
  exact hn.trans_lt (half_lt_self hε)

/-- Exact boundary between strong approximation and uniform operator approximation. -/
theorem paperThetaSchurFiniteStageOperator_norm_tendsto_iff (S : PaperThetaSchurFamily) :
    Tendsto (paperThetaSchurFiniteStageOperator S) atTop (𝓝 (paperThetaSchurModeOperator S)) ↔
      RiemannHypothesis := by
  constructor
  · intro ht
    apply (paperThetaSchurModeOperator_compact_iff S).1
    exact isClosed_setOf_isCompactOperator.mem_of_tendsto ht
      (Eventually.of_forall (paperThetaSchurFiniteStageOperator_compact S))
  · exact paperThetaSchurFiniteStageOperator_norm_tendsto_of_rh S

/-- When RH fails, every finite stage cutoff remains uniformly separated from the limit. -/
theorem paperThetaSchurFiniteStageOperator_uniform_gap_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : PaperThetaSchurFamily, ∀ N : ℕ,
      δ ≤ ‖paperThetaSchurModeOperator S - paperThetaSchurFiniteStageOperator S N‖ := by
  obtain ⟨δ, hδ, hgap⟩ := paperThetaSchur_uniform_compact_gap_of_not_rh hRH
  exact ⟨δ, hδ, fun S N => hgap S
    ⟨paperThetaSchurFiniteStageOperator S N, paperThetaSchurFiniteStageOperator_compact S N⟩⟩

end
end RHTower.HedenmalmThetaSource
