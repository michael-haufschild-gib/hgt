import GaloisForLFunctions.HTGeometry.EventNetworkFixedCarrier
import GaloisForLFunctions.HTGeometry.TraceClassQuantumCorner
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Hilbert direct-sum carrier for typed event networks

This module supplies the literal dependent `ℓ²` carrier underlying the operational fixed-carrier
construction.  Every event fibre embeds by a canonical linear isometry; its Hilbert adjoint is
coordinate compression.  Consequently, the corresponding concrete trace-class sandwiches split
exactly.  Complete positivity, trace contraction, and normality of those sandwiches are developed
at the next layer.
-/

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

noncomputable section

variable {ι : Type*} {K : ι → Type*} [DecidableEq ι]
  [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]

/-- Literal Hilbert direct sum of a dependent family of complex Hilbert event fibres. -/
abbrev eventNetworkHilbertCarrier (K : ι → Type*) [∀ i, NormedAddCommGroup (K i)]
    [∀ i, InnerProductSpace ℂ (K i)] :=
  lp K 2

omit [DecidableEq ι] in
/-- For a finite event family, fixed-carrier dimension is the sum of fibre dimensions. -/
theorem finrank_eventNetworkHilbertCarrier [Fintype ι]
    [∀ i, FiniteDimensional ℂ (K i)] :
    Module.finrank ℂ (eventNetworkHilbertCarrier K) =
      ∑ i, Module.finrank ℂ (K i) := by
  calc
    Module.finrank ℂ (eventNetworkHilbertCarrier K) =
        Module.finrank ℂ (PiLp 2 K) :=
      (lpPiLpₗᵢ K ℂ).toLinearEquiv.finrank_eq
    _ = Module.finrank ℂ (∀ i, K i) :=
      (WithLp.linearEquiv 2 ℂ (∀ i, K i)).finrank_eq
    _ = ∑ i, Module.finrank ℂ (K i) :=
      Module.finrank_pi_fintype ℂ

/-- Countable code for finite-support approximations to the fixed Hilbert carrier. -/
abbrev EventNetworkFiniteApproximation (ι : Type*) := List (ι × ℕ)

/-- Interpret a finite approximation code using fixed dense sequences in every event fibre. -/
noncomputable def eventNetworkFiniteApproximationToCarrier
    [∀ i, TopologicalSpace.SeparableSpace (K i)]
    (a : EventNetworkFiniteApproximation ι) : eventNetworkHilbertCarrier K :=
  (a.map fun q => lp.single (E := K) 2 q.1
    (TopologicalSpace.denseSeq (K q.1) q.2)).sum

/-- Finite-support dense-sequence approximations are dense in the dependent Hilbert direct sum. -/
theorem denseRange_eventNetworkFiniteApproximation
    [∀ i, TopologicalSpace.SeparableSpace (K i)] :
    DenseRange (eventNetworkFiniteApproximationToCarrier (K := K)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  have hsum := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f
  have hevent := (Metric.tendsto_nhds.mp hsum) (ε / 2) (half_pos hε)
  obtain ⟨s, hs⟩ := Filter.eventually_atTop.mp hevent
  have hs' := hs s le_rfl
  have hs_sub : dist
      (∑ i : s, lp.single (E := K) 2 (i : ι) (f i)) f < ε / 2 := by
    have heq : (∑ i : s, lp.single (E := K) 2 (i : ι) (f i)) =
        ∑ i ∈ s, lp.single (E := K) 2 i (f i) := by
      exact (Finset.sum_subtype s (fun _ => Iff.rfl) fun i =>
        lp.single (E := K) 2 i (f i)).symm
    rw [heq]
    exact hs'
  by_cases hsne : s.Nonempty
  · let δ : ℝ := (ε / 2) / s.card
    have hcard : 0 < (s.card : ℝ) := by exact_mod_cast s.card_pos.mpr hsne
    have hδ : 0 < δ := div_pos (half_pos hε) hcard
    have hdense (i : s) := Metric.denseRange_iff.mp
      (TopologicalSpace.denseRange_denseSeq (K i)) (f i) δ hδ
    choose c hc using hdense
    let a : EventNetworkFiniteApproximation ι :=
      s.attach.toList.map fun i : s => ((i : ι), c i)
    refine ⟨a, ?_⟩
    have hsource : dist f
        (∑ i : s, lp.single (E := K) 2 (i : ι) (f i)) < ε / 2 := by
      simpa only [dist_comm] using hs_sub
    have hcoord : dist
        (∑ i : s, lp.single (E := K) 2 (i : ι) (f i))
        (eventNetworkFiniteApproximationToCarrier (K := K) a) < ε / 2 := by
      have ha : eventNetworkFiniteApproximationToCarrier (K := K) a =
          ∑ i : s, lp.single (E := K) 2 (i : ι)
            (TopologicalSpace.denseSeq (K i) (c i)) := by
        simp [a, eventNetworkFiniteApproximationToCarrier]
      rw [ha, dist_eq_norm, ← Finset.sum_sub_distrib]
      calc
        ‖∑ i : s, (lp.single (E := K) 2 (i : ι) (f i) -
            lp.single (E := K) 2 (i : ι)
              (TopologicalSpace.denseSeq (K i) (c i)))‖ ≤
            ∑ i : s, ‖lp.single (E := K) 2 (i : ι) (f i) -
              lp.single (E := K) 2 (i : ι)
                (TopologicalSpace.denseSeq (K i) (c i))‖ :=
          norm_sum_le _ _
        _ = ∑ i : s, ‖f i - TopologicalSpace.denseSeq (K i) (c i)‖ := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [← lp.single_sub, lp.norm_single (by norm_num)]
        _ < ∑ _i : s, δ := by
          apply Finset.sum_lt_sum
          · intro i _hi
            exact (by simpa only [dist_eq_norm] using (hc i).le)
          · let i : s := ⟨Classical.choose hsne, Classical.choose_spec hsne⟩
            exact ⟨i, Finset.mem_univ _, by simpa only [dist_eq_norm] using hc i⟩
        _ = ε / 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          dsimp [δ]
          field_simp
    exact (dist_triangle f
      (∑ i : s, lp.single (E := K) 2 (i : ι) (f i))
      (eventNetworkFiniteApproximationToCarrier (K := K) a)).trans_lt
        ((add_lt_add hsource hcoord).trans_eq (by ring))
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
    let a : EventNetworkFiniteApproximation ι := []
    refine ⟨a, ?_⟩
    rw [hsempty] at hs'
    have hhalf := hs'.trans (half_lt_self hε)
    simpa [a, eventNetworkFiniteApproximationToCarrier, dist_comm] using hhalf

/-- A countable family of separable event fibres has a separable fixed Hilbert carrier. -/
theorem separableSpace_eventNetworkHilbertCarrier [Countable ι]
    [∀ i, TopologicalSpace.SeparableSpace (K i)] :
    TopologicalSpace.SeparableSpace (eventNetworkHilbertCarrier K) := by
  letI : Encodable ι := Encodable.ofCountable ι
  letI : Countable (EventNetworkFiniteApproximation ι) := by infer_instance
  exact TopologicalSpace.SeparableSpace.of_denseRange
    (eventNetworkFiniteApproximationToCarrier (K := K))
    denseRange_eventNetworkFiniteApproximation

/-- Canonical isometric inclusion of one event fibre into the fixed Hilbert direct sum. -/
def eventNetworkSummandIsometry (i : ι) :
    K i →ₗᵢ[ℂ] eventNetworkHilbertCarrier K where
  toFun := lp.single 2 i
  map_add' x y := by
    ext j
    simp [lp.single_apply]
  map_smul' c x := by
    ext j
    simp [lp.single_apply]
  norm_map' x := lp.norm_single (by norm_num) i x

@[simp]
theorem eventNetworkSummandIsometry_apply (i : ι) (x : K i) :
    eventNetworkSummandIsometry (K := K) i x = lp.single 2 i x := rfl

variable [∀ i, CompleteSpace (K i)]

/-- The adjoint of summand inclusion is literal coordinate compression. -/
theorem adjoint_eventNetworkSummandIsometry_apply (i : ι)
    (y : eventNetworkHilbertCarrier K) :
    adjoint (eventNetworkSummandIsometry (K := K) i).toContinuousLinearMap y = y i := by
  apply ext_inner_left ℂ
  intro x
  rw [adjoint_inner_right]
  change inner ℂ (lp.single 2 i x) y = inner ℂ x (y i)
  rw [lp.inner_single_left]

/-- Coordinate compression after summand inclusion is exactly the identity. -/
theorem eventNetworkSummand_adjoint_comp_id (i : ι) :
    adjoint (eventNetworkSummandIsometry (K := K) i).toContinuousLinearMap ∘L
      (eventNetworkSummandIsometry (K := K) i).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (K i) := by
  ext x
  simp

/-- Trace-class inclusion into one fixed Hilbert carrier. -/
def eventNetworkTraceClassInclusion (i : ι) :
    TraceClassOperator (K i) →ₗ[ℂ] TraceClassOperator (eventNetworkHilbertCarrier K) :=
  traceClassSandwich (eventNetworkSummandIsometry (K := K) i).toContinuousLinearMap

/-- Trace-class compression from the fixed carrier back to one event fibre. -/
def eventNetworkTraceClassCompression (i : ι) :
    TraceClassOperator (eventNetworkHilbertCarrier K) →ₗ[ℂ] TraceClassOperator (K i) :=
  traceClassSandwich (adjoint
    (eventNetworkSummandIsometry (K := K) i).toContinuousLinearMap)

/-- Literal trace-class corner split for every event fibre. -/
theorem eventNetworkTraceClassCompression_inclusion (i : ι)
    (ρ : TraceClassOperator (K i)) :
    eventNetworkTraceClassCompression (K := K) i
        (eventNetworkTraceClassInclusion (K := K) i ρ) = ρ := by
  exact traceClassSandwich_adjoint_apply
    (eventNetworkSummandIsometry (K := K) i).toContinuousLinearMap
    (eventNetworkSummand_adjoint_comp_id (K := K) i) ρ

/-- The trace-class compression/inclusion composite is the identity linear map. -/
theorem eventNetworkTraceClassCompression_comp_inclusion (i : ι) :
    (eventNetworkTraceClassCompression (K := K) i).comp
        (eventNetworkTraceClassInclusion (K := K) i) = LinearMap.id := by
  apply LinearMap.ext
  exact eventNetworkTraceClassCompression_inclusion (K := K) i

/-- Every event fibre is a literal normal completely-positive corner of the fixed carrier. -/
noncomputable def eventNetworkTraceClassCorner (i : ι) :
    TraceClassQuantumCorner (K i) (eventNetworkHilbertCarrier K) :=
  traceClassQuantumCornerOfIsometry
    (eventNetworkSummandIsometry (K := K) i).toContinuousLinearMap
    (eventNetworkSummandIsometry (K := K) i).norm_map
    (eventNetworkSummand_adjoint_comp_id (K := K) i)

/-- Literal fixed-carrier lift of a typed trace-class quantum operation. -/
noncomputable def eventNetworkCornerLift (i j : ι)
    (Φ : TraceClassQuantumOperation (K i) (K j)) :
    TraceClassQuantumOperation (eventNetworkHilbertCarrier K)
      (eventNetworkHilbertCarrier K) :=
  TraceClassQuantumOperation.cornerLift
    (eventNetworkTraceClassCorner (K := K) i)
    (eventNetworkTraceClassCorner (K := K) j) Φ

/-- The concrete lift is the advertised inclusion-operation-compression sandwich. -/
theorem eventNetworkCornerLift_apply (i j : ι)
    (Φ : TraceClassQuantumOperation (K i) (K j))
    (ρ : TraceClassOperator (eventNetworkHilbertCarrier K)) :
    (eventNetworkCornerLift (K := K) i j Φ).map ρ =
      eventNetworkTraceClassInclusion (K := K) j
        (Φ.map (eventNetworkTraceClassCompression (K := K) i ρ)) := rfl

/-- Fixed-carrier lifts remain completely positive at every finite level. -/
theorem eventNetworkCornerLift_completelyPositive (i j : ι)
    (Φ : TraceClassQuantumOperation (K i) (K j)) :
    IsCompletelyPositive
      (traceClassMatrixCone (eventNetworkHilbertCarrier K))
      (traceClassMatrixCone (eventNetworkHilbertCarrier K))
      (eventNetworkCornerLift (K := K) i j Φ).map :=
  (eventNetworkCornerLift (K := K) i j Φ).completelyPositive

/-- Fixed-carrier lifts are trace-nonincreasing on positive trace-class states. -/
theorem eventNetworkCornerLift_traceNonincreasing (i j : ι)
    (Φ : TraceClassQuantumOperation (K i) (K j))
    (ρ : TraceClassOperator (eventNetworkHilbertCarrier K))
    (hρ : traceClassPositive ρ) :
    traceClassTrace ((eventNetworkCornerLift (K := K) i j Φ).map ρ) ≤
      traceClassTrace ρ :=
  (eventNetworkCornerLift (K := K) i j Φ).traceNonincreasing ρ hρ

/-- The lift agrees exactly with the typed operation on valid source-corner states. -/
theorem eventNetworkCornerLift_include (i j : ι)
    (Φ : TraceClassQuantumOperation (K i) (K j))
    (ρ : TraceClassOperator (K i)) :
    (eventNetworkCornerLift (K := K) i j Φ).map
        (eventNetworkTraceClassInclusion (K := K) i ρ) =
      eventNetworkTraceClassInclusion (K := K) j (Φ.map ρ) :=
  TraceClassQuantumOperation.cornerLift_include
    (eventNetworkTraceClassCorner (K := K) i)
    (eventNetworkTraceClassCorner (K := K) j) Φ ρ

/-- Composable typed operations lift with exact fixed-carrier composition. -/
theorem eventNetworkCornerLift_comp (i j k : ι)
    (Φ : TraceClassQuantumOperation (K i) (K j))
    (Ψ : TraceClassQuantumOperation (K j) (K k)) :
    (eventNetworkCornerLift (K := K) j k Ψ).map.comp
        (eventNetworkCornerLift (K := K) i j Φ).map =
      (eventNetworkCornerLift (K := K) i k (Ψ.comp Φ)).map :=
  TraceClassQuantumOperation.cornerLift_comp
    (eventNetworkTraceClassCorner (K := K) i)
    (eventNetworkTraceClassCorner (K := K) j)
    (eventNetworkTraceClassCorner (K := K) k) Φ Ψ

/-- Trace-preserving typed operations preserve normalization on valid source-corner states. -/
theorem trace_eventNetworkCornerLift_include_eq_of_tracePreserving (i j : ι)
    (Φ : TraceClassQuantumOperation (K i) (K j)) (hΦ : Φ.tracePreserving)
    (ρ : TraceClassOperator (K i)) (hρ : traceClassPositive ρ) :
    traceClassTrace ((eventNetworkCornerLift (K := K) i j Φ).map
      (eventNetworkTraceClassInclusion (K := K) i ρ)) = traceClassTrace ρ :=
  TraceClassQuantumOperation.trace_cornerLift_include_eq_of_tracePreserving
    (eventNetworkTraceClassCorner (K := K) i)
    (eventNetworkTraceClassCorner (K := K) j) Φ hΦ ρ hρ

end

end GaloisForLFunctions.HTGeometry
