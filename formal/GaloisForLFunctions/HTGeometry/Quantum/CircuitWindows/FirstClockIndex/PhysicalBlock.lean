import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FirstClockIndex.BlockCover
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FirstClockIndex.EarlyVisits

/-! # A first affordable positive multiple from the identity on a sampled clock -/
open Set Filter MeasureTheory Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstClockIndex
noncomputable section
open SharpOccupation

private theorem null_frontier_finite_union {X I : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [Fintype I] (μ : Measure X) (A : I → Set X) (hc : ∀ i, IsClosed (A i))
    (hn : ∀ i, μ (frontier (A i)) = 0) : μ (frontier (⋃ i, A i)) = 0 := by
  apply measure_mono_null _ (measure_iUnion_null hn)
  rw [frontier,(isClosed_iUnion_of_finite hc).closure_eq]
  rintro z ⟨hz,hnot⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  refine mem_iUnion.mpr ⟨i,?_⟩
  rw [frontier,(hc i).closure_eq]
  exact ⟨hi,fun h => hnot (interior_mono (subset_iUnion A i) h)⟩

private theorem phase_multiple {I : Type*} [Fintype I] (ω : I → ℝ) (q : ℕ) (t : ℝ) :
    finiteClockPhasePoint ω ((q:ℝ)*t) = q • finiteClockPhasePoint ω t := by
  funext i
  change ((((q:ℝ)*t)*ω i/(2*Real.pi):ℝ):UnitAddCircle) = q • (((t*ω i/(2*Real.pi):ℝ)):UnitAddCircle)
  rw [←AddCircle.coe_nsmul,nsmul_eq_mul]
  congr 1
  ring

/-- For a fixed maximally projective generator, an upper bound on the
Haar probability of missing a block gives the same long-record bound
on periods with no affordable multiple through the end of that block. -/
theorem physical_block_bound {n Q R : ℕ} (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (hQ : 0 < Q) (hR : 0 < R)
    (x : ℝ) (hx : 0 < x) (hy : x+(R:ℝ)/Q ≤ 1/2) (a b : ℝ)
    (hb : let d := (2^n:ℕ)-1
          1/((R:ℝ)*x^d)+((1+(R:ℝ)/Q/x)^d-1) < b) :
    ∀ᶠ T : ℝ in atTop, ∀ s : ℕ,
      volume.real ((earlyVisit H s (Q+R) (zeroGateArcTolerance x))ᶜ ∩ Icc a T)/(T-a) < b := by
  classical
  let ref : Fin n → Bool := fun _ => false
  let I := {j : Fin n → Bool // j ≠ ref}
  let ω := projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) ref
  let q (i : Fin R) := Q+i.val
  let A (i : Fin R) := (fun θ : I → UnitAddCircle => q i • θ) ⁻¹' relativeEnclosingUnitArc ref x
  let B := (⋃ i, A i)ᶜ
  have hpos (i : Fin R) : 0 < q i := Nat.add_pos_left hQ _
  have hhalf : x ≤ 1/2 := (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg Q))).trans hy
  let r : Icc (0:ℝ) (1/2) := ⟨x,hx.le,hhalf⟩
  have hc (i) : IsClosed (A i) := (isClosed_relativeEnclosingUnitArc ref x).preimage (continuous_nsmul (q i))
  have hm : MeasurableSet B := (isClosed_iUnion_of_finite hc).measurableSet.compl
  have hn (i) : volume (frontier (A i)) = 0 := by
    let g (θ : I → UnitAddCircle) := q i • θ
    have hg : MeasurePreserving g volume volume :=
      measurePreserving_pi (fun _ : I => (volume : Measure UnitAddCircle))
        (fun _ : I => (volume : Measure UnitAddCircle)) (fun _ => multiple_preserves (hpos i))
    apply measure_mono_null ((continuous_nsmul (q i)).frontier_preimage_subset _)
    rw [hg.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet]
    exact volume_frontier_relativeEnclosingUnitArc ref x
  have hnull : volume (frontier B) = 0 := by
    rw [show frontier B = frontier (⋃ i, A i) from frontier_compl _]
    exact null_frontier_finite_union volume A hc hn
  have hsmall : volume.real B < b := by
    have sub (i : Fin R) : boxHit I (q i) x ⊆ A i := by
      intro θ hθ
      refine mem_iUnion.mpr ⟨ref,?_⟩
      intro j hj
      simp only [relativeUnitPhasePacket,dif_pos hj,dif_neg (not_not_intro rfl),sub_zero]
      exact hθ ⟨j,hj⟩ (mem_univ _)
    apply (measureReal_mono (μ := volume) (compl_subset_compl.mpr (iUnion_mono sub))).trans_lt
    have hcard : Fintype.card I = (2^n:ℕ)-1 := by
      simp [I,Fintype.card_subtype_compl]
    have h := block_miss (I := I) hQ hR hx hy
    rw [hcard] at h
    exact h.trans_lt hb
  have hind : RationallyIndependentFrequency ω :=
    maximallyProjectiveEnergy_projectiveFrequency_independent _ (maximallyProjectiveEnergy_neg hi) ref
  have hF : (finiteTorusHaarProbabilityMeasure I : Measure _) (frontier B)=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (clockPhaseWindowLaw_tendsto_haar ω hind) hF
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at h
  let S := finiteClockPhasePoint ω ⁻¹' B
  have hS : MeasurableSet S := hm.preimage (finiteClockPhasePoint_continuous ω).measurable
  have heq (T : ℝ) : (clockPhaseWindowLaw ω T : Measure _) B = (windowProbabilityMeasure T : Measure ℝ) S := by
    rw [clockPhaseWindowLaw,ProbabilityMeasure.toMeasure_map,Measure.map_apply (finiteClockPhasePoint_continuous ω).measurable hm]
  have hlim := (ENNReal.tendsto_toReal (measure_ne_top volume B)).comp (h.congr heq)
  have hwin := tendsto_occupation_from_start S hS a _ hlim
  filter_upwards [hwin.eventually_lt_const hsmall,eventually_gt_atTop a] with T hT ha s
  refine lt_of_le_of_lt (div_le_div_of_nonneg_right (measureReal_mono (inter_subset_inter_left _ ?_)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)) (sub_nonneg.mpr ha.le)) hT
  intro t ht
  change finiteClockPhasePoint ω t ∉ ⋃ i, A i
  intro hhit
  obtain ⟨i,hi'⟩ := mem_iUnion.mp hhit
  have hphase : finiteClockPhasePoint ω ((q i:ℝ)*t) ∈ relativeEnclosingUnitArc ref x := by
    rw [phase_multiple]; exact hi'
  obtain ⟨z,hz,C,hC,herr⟩ := (zeroGateApproximation_iff_clock_shortArc H ref ((q i:ℝ)*t) r).mpr hphase
  exact ht ⟨q i,hpos i,Nat.add_le_add_left i.isLt.le _,z,hz,C,hC.trans (Nat.zero_le s),herr⟩

#print axioms physical_block_bound
end
end GaloisForLFunctions.HTGeometry.FirstClockIndex
