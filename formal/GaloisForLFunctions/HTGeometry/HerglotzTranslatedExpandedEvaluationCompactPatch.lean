import GaloisForLFunctions.HTGeometry.HerglotzJetMapSmoothness
import GaloisForLFunctions.HTGeometry.WeightedCauchyTranslatedExpandedEvaluationCompactPatch

/-!
# Compact-patch density for translated Herglotz jets

The weighted Cauchy compact-patch theorem supplies dense affine multiplicative gauges around every
bounded parameter.  The logarithmic gauge lift realizes each sufficiently small affine gauge
exactly inside the nonlinear exponential Herglotz chart.  This transfers literal expanded-matrix
rank avoidance, uniformly over a compact translated-node patch, to the original `L∞` parameter
space.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

/-- **Nonlinear Herglotz compact-patch density law.**  For every compact smooth collision-free
family of upper row-by-translate nodes, bounded Herglotz parameters whose literal expanded
differential evaluation matrix has full coefficient rank throughout the patch are dense. -/
theorem compact_herglotzExpandedEvaluation_avoidance_dense
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (degree : ℕ) (orders : ι → ℕ)
    (rowBase : row → ℂ) (hrowBase : Function.Injective rowBase)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (nodes : H → (row × ι → ℂ)) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (hnodes_inj : ∀ h ∈ K, Function.Injective (nodes h))
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense (compactConfigurationAvoidance
      (fun p : Lp ℝ ⊤ μ × H =>
        reshapeCombinedJetsFinCLM row ι orders
          (herglotzJetMap μ w (nodes p.2)
            (fun x : row × ι => orders x.2) p.1))
      (expandedDifferentialEvaluationRankDefect
        degree (Fintype.card (Σ i, Fin (orders i))) rowBase exponent) K) := by
  rw [Metric.dense_iff]
  intro u₀ ε hε
  let w₀ : ℝ → ℝ := fun t => Real.exp (u₀ t) * w t
  have hw₀ : Integrable w₀ μ := integrable_exp_Lp_top_mul μ u₀ w hw
  have hw₀pos : ∀ t, 0 < w₀ t := fun t => exp_mul_pos (fun t => u₀ t) hwpos t
  let base : H → (row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ) :=
    fun h => reshapeCombinedJetsFinCLM row ι orders
      (herglotzJetMap μ w (nodes h) (fun x : row × ι => orders x.2) u₀)
  have hbase : ContDiffOn ℝ ⊤ base U := by
    have hjets : ContDiffOn ℝ ⊤
        (fun h => herglotzJetMap μ w (nodes h)
          (fun x : row × ι => orders x.2) u₀) U :=
      (contDiffOn_herglotzJetMap_nodes μ w hw
        (fun x : row × ι => orders x.2) u₀).comp hnodes.contDiffOn
          (fun h hh x => by simpa [nevanlinnaUpperPacketSet] using hupper h hh x)
    exact (reshapeCombinedJetsFinCLM row ι orders).contDiff.comp_contDiffOn hjets
  obtain ⟨V, hVfg, hdenseGauge⟩ :=
    compact_weightedCauchyExpandedEvaluation_has_dense_finiteProbe
      μ hμ w₀ hw₀ hw₀pos degree orders rowBase hrowBase exponent hexponent hrows
      base nodes hnodes U K hU hK hKU hbase hupper hnodes_inj hdim
  let control := fun h =>
    weightedCauchyJetSmoothControl μ w₀ hw₀
      (fun x : row × ι => orders x.2) (nodes h)
  let direction := fun h =>
    (reshapeCombinedJetsFinCLM row ι orders).comp (control h)
  change Dense (compactConfigurationAvoidance
    (smoothAffineControlFamily base direction)
    (expandedDifferentialEvaluationRankDefect
      degree (Fintype.card (Σ i, Fin (orders i))) rowBase exponent) K) at hdenseGauge
  let δ : ℝ := min (1 / 2) (ε / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨h, hhball, hhgood⟩ :=
    Metric.dense_iff.mp hdenseGauge 0 δ hδ
  have hhδ : ‖h‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hhball
  have hhhalf : ‖h‖ ≤ 1 / 2 :=
    le_of_lt (lt_of_lt_of_le hhδ (min_le_left _ _))
  have hheps : ‖h‖ < ε / 2 :=
    lt_of_lt_of_le hhδ (min_le_right _ _)
  refine ⟨u₀ + logOneAddLp μ h hhhalf, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc
      ‖logOneAddLp μ h hhhalf‖ ≤ 2 * ‖h‖ := norm_logOneAddLp_le μ h hhhalf
      _ < ε := by linarith
  · intro q hq
    have hgood := hhgood q hq
    have hqUpper : ∀ x, 0 < (nodes q x).im := hupper q (hKU hq)
    have hjet := herglotzJetMap_gauged μ w hw (nodes q)
      (fun x => ne_of_gt (hqUpper x)) (fun x : row × ι => orders x.2) u₀ h hhhalf
    have hcontrol := weightedCauchyJetSmoothControl_eq_weightedJetControl
      μ w₀ hw₀ (fun x : row × ι => orders x.2) (nodes q) hqUpper
    change base q + direction q h ∉
      expandedDifferentialEvaluationRankDefect
        degree (Fintype.card (Σ i, Fin (orders i))) rowBase exponent at hgood
    change reshapeCombinedJetsFinCLM row ι orders
      (herglotzJetMap μ w (nodes q) (fun x : row × ι => orders x.2)
        (u₀ + logOneAddLp μ h hhhalf)) ∉
      expandedDifferentialEvaluationRankDefect
        degree (Fintype.card (Σ i, Fin (orders i))) rowBase exponent
    rw [hjet, map_add]
    simpa only [base, direction, control, ContinuousLinearMap.comp_apply, w₀, hcontrol]
      using hgood

end

end GaloisForLFunctions.HTGeometry
