import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatFiniteMeasureDescent
import GaloisForLFunctions.RHTower.CHMDBeurlingDenyNodalDecompositionAndParityBoundStateSpaces

/-!
# Flat descent converges in the complete arithmetic graph

Apply the infinitely flat scalar gradient step to the literal CHMD
source. Every iterate retains all archimedean and prime-power jumps.
Dominated convergence of the jumps upgrades source L² convergence to
strong convergence in the full graph. The limit is the negative part.
Finite source measure also gives uniform convergence in the mass norm
on its unit ball; no uniform graph-norm assertion is needed.
-/

open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDClosedJump _root_.RHTower.CHMDPolar
noncomputable section

/-- A unit flat-gradient step on the literal complete arithmetic graph. -/
def graphDescent (p : SourceGraph) : SourceGraph :=
  contract massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    descent_contraction descent_zero

theorem graphDescent_source (p : SourceGraph) :
    (graphDescent p).val.fst = descentLp p.val.fst := by
  apply Lp.ext
  exact (contract_source_ae massMeasure edgeMeasure left right nonsingular_left
    nonsingular_right p descent_contraction descent_zero).trans (descentLp_ae p.val.fst).symm

theorem graphDescent_iterate_source (p : SourceGraph) (n : ℕ) :
    (graphDescent^[n] p).val.fst = descentLp^[n] p.val.fst := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', graphDescent_source, ih,
      Function.iterate_succ_apply']

private theorem neg_negFun (t : ℝ) : -negFun t = min t 0 := by
  by_cases ht : t ≤ 0
  · rw [negFun, max_eq_left (neg_nonneg.mpr ht), neg_neg, min_eq_left ht]
  · rw [negFun, max_eq_right (neg_nonpos.mpr (le_of_not_ge ht)), neg_zero,
      min_eq_right (le_of_not_ge ht)]

theorem graph_negative_part_source (p : SourceGraph) :
    (-negGraph p).val.fst = negativePartLp p.val.fst := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_neg (negGraph p).val.fst, negGraph_fst_ae p,
    negativePartLp_ae p.val.fst] with x hn hp hmin
  change (-(negGraph p).val.fst) x = _
  rw [hn, hmin]
  change -((negGraph p).val.fst x) = _
  rw [hp, neg_negFun]

private theorem graphDescent_iterate_edge_ae (p : SourceGraph) (n : ℕ) :
    (graphDescent^[n] p).val.snd =ᵐ[edgeMeasure]
      fun e => descent^[n] (p.val.fst (left e)) - descent^[n] (p.val.fst (right e)) := by
  have hs : (graphDescent^[n] p).val.fst =ᵐ[massMeasure]
      fun x => descent^[n] (p.val.fst x) := by
    rw [graphDescent_iterate_source]
    exact descentLp_iterate_ae p.val.fst n
  filter_upwards [(graphDescent^[n] p).property, nonsingular_left.ae hs,
    nonsingular_right.ae hs] with e he hl hr
  rw [he, hl, hr]

private theorem graph_negative_part_edge_ae (p : SourceGraph) :
    (-negGraph p).val.snd =ᵐ[edgeMeasure]
      fun e => min (p.val.fst (left e)) 0 - min (p.val.fst (right e)) 0 := by
  have hs : (-negGraph p).val.fst =ᵐ[massMeasure] fun x => min (p.val.fst x) 0 := by
    rw [graph_negative_part_source]
    exact negativePartLp_ae p.val.fst
  filter_upwards [(-negGraph p).property, nonsingular_left.ae hs,
    nonsingular_right.ae hs] with e he hl hr
  rw [he, hl, hr]

private theorem difference_square_bound {a b c : ℝ} (ha : |a| ≤ |c|) (hb : |b| ≤ |c|) :
    (a - b) ^ 2 ≤ 4 * c ^ 2 := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  have h₁ : 0 ≤ 2 * |c| - (a - b) := by linarith only [ha₂, hb₁]
  have h₂ : 0 ≤ 2 * |c| + (a - b) := by linarith only [ha₁, hb₂]
  nlinarith only [mul_nonneg h₁ h₂, sq_abs c]

/-- The complete jump vector converges, including every prime-power edge. -/
theorem graphDescent_edge_tendsto (p : SourceGraph) :
    Tendsto (fun n : ℕ => (graphDescent^[n] p).val.snd) atTop
      (𝓝 (-negGraph p).val.snd) := by
  have h := toLp_tendsto_of_sq_dom
    (fun n => Lp.memLp (graphDescent^[n] p).val.snd) (Lp.memLp (-negGraph p).val.snd)
    ((Lp.memLp p.val.snd).integrable_sq.const_mul 4) ?_ ?_
  · simpa only [Lp.toLp_coeFn] using h
  · intro n
    filter_upwards [graphDescent_iterate_edge_ae p n, graph_negative_part_edge_ae p,
      p.property] with e hn hp he
    rw [hn, hp, he]
    have hT : LipschitzWith 1 (descent^[n]) := by
      simpa only [one_pow] using descent_contraction.iterate n
    apply difference_square_bound
    · simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
        hT.norm_sub_le (p.val.fst (left e)) (p.val.fst (right e))
    · simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul, id_eq] using
        (LipschitzWith.id.min_const (0 : ℝ)).norm_sub_le
          (p.val.fst (left e)) (p.val.fst (right e))
  · filter_upwards [ae_all_iff.mpr (fun n => graphDescent_iterate_edge_ae p n),
      graph_negative_part_edge_ae p] with e hn hp
    simp only [hn, hp]
    exact (descent_tendsto_negative_part _).sub (descent_tendsto_negative_part _)

/-- Flat descent converges strongly in the full arithmetic source graph to its negative part. -/
theorem graphDescent_tendsto (p : SourceGraph) :
    Tendsto (fun n : ℕ => graphDescent^[n] p) atTop (𝓝 (-negGraph p)) := by
  have hs : Tendsto (fun n : ℕ => (graphDescent^[n] p).val.fst) atTop
      (𝓝 (-negGraph p).val.fst) := by
    simpa only [graphDescent_iterate_source, graph_negative_part_source] using
      descentLp_tendsto_negativePart p.val.fst
  rw [tendsto_subtype_rng]
  exact (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp
    (hs.prodMk_nhds (graphDescent_edge_tendsto p))

/-- Strong graph convergence preserves the limit of the original signed energy. -/
theorem graphDescent_signed_energy_tendsto (p : SourceGraph) :
    Tendsto (fun n : ℕ => sourceEnergy (graphDescent^[n] p)) atTop
      (𝓝 (sourceEnergy (-negGraph p))) :=
  continuous_sourceEnergy.continuousAt.tendsto.comp (graphDescent_tendsto p)

/-- Finite arithmetic source measure makes mass convergence uniform over the mass unit ball. -/
theorem graphDescent_uniform_mass_unitBall {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ p : SourceGraph, ‖p.val.fst‖ ≤ 1 →
      ‖(graphDescent^[n + 1] p).val.fst - (-negGraph p).val.fst‖ < ε := by
  obtain ⟨N, hN⟩ := descentLp_uniform_on_finite_measure_unitBall (μ := massMeasure) hε
  refine ⟨N, fun n hn p hp => ?_⟩
  simpa only [graphDescent_iterate_source, graph_negative_part_source] using hN n hn p.val.fst hp

#print axioms graphDescent_tendsto
#print axioms graphDescent_signed_energy_tendsto
#print axioms graphDescent_uniform_mass_unitBall
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
