import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.PinnedClock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar

/-! # Frequency of strict face interiors on a clock pinned to an endpoint -/
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section
open AdaptiveSampling
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
local instance : NullSingletonClass (volume : Measure UnitAddCircle) :=
  ⟨fun x => by rw [←Metric.closedBall_zero,AddCircle.volume_closedBall]; simp⟩

def openArc (r : ℝ) : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ioo 0 r

def openBox (I : Type*) (r : ℝ) : Set (I → UnitAddCircle) := Set.pi univ (fun _ => openArc r)

private theorem openBox_volume {I : Type*} [Fintype I] (r : Icc (0:ℝ) (1/2)) :
    volume (openBox I r) = ENNReal.ofReal (r:ℝ)^(Fintype.card I) ∧
      volume (frontier (openBox I r))=0 := by
  classical
  let C := Set.pi (univ : Set I) (fun _ => forwardUnitArc r)
  let O := openBox I r
  have ho : IsOpen O := isOpen_set_pi (finite_univ) (fun _ _ => QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)
  have hc : IsClosed C := isClosed_set_pi (fun _ _ => isClosed_forwardUnitArc _)
  have hsub : O ⊆ C := Set.pi_mono fun _ _ => image_mono Ioo_subset_Icc_self
  let ends : Set UnitAddCircle := {0,((r:ℝ):UnitAddCircle)}
  have hm : MeasurableSet ends := (measurableSet_singleton _).insert _
  have hn (i : I) : volume ((Function.eval i : (I → UnitAddCircle) → UnitAddCircle) ⁻¹' ends) = 0 := by
    have hmp := measurePreserving_eval (fun _ : I => (volume : Measure UnitAddCircle)) i
    rw [hmp.measure_preimage hm.nullMeasurableSet]
    exact ((finite_singleton _).insert _).measure_zero _
  have hedge : C \ O ⊆ ⋃ i : I, Function.eval i ⁻¹' ends := by
    intro z hz
    by_contra h
    apply hz.2
    intro i _
    have hnot : z i ∉ ends := fun hi => h (mem_iUnion.mpr ⟨i,hi⟩)
    obtain ⟨u,hu,he⟩ := hz.1 i (mem_univ i)
    refine ⟨u,⟨lt_of_le_of_ne hu.1 (fun he0 => hnot (Or.inl (by rw [←he,←he0,AddCircle.coe_zero]))),
      lt_of_le_of_ne hu.2 (fun her => hnot (Or.inr (by rw [←he,her])))⟩,he⟩
  have hnull := measure_mono_null hedge (measure_iUnion_null hn)
  have hae : O =ᵐ[volume] C := by
    filter_upwards [ae_iff.mpr hnull] with z hz
    exact propext ⟨fun h => hsub h,fun h => by_contra fun hn => hz ⟨h,hn⟩⟩
  have hvol : volume C=ENNReal.ofReal (r:ℝ)^Fintype.card I := by
    rw [show volume C = ∏ i : I, volume (forwardUnitArc r) from Measure.pi_pi _ _]
    simp only [volume_forwardUnitArc,Finset.prod_const,Finset.card_univ]
  refine ⟨(measure_congr hae).trans hvol,measure_mono_null ?_ hnull⟩
  rw [frontier,ho.interior_eq]
  exact sdiff_subset_sdiff_left (closure_minimal hsub hc)

/-- Number of successful tests among the first M ticks. -/
def countTicks (test : ℕ → Prop) (M : ℕ) : ℕ := by
  classical
  exact ((Finset.range M).filter test).card

private theorem prefix_real {X : Type*} [MeasurableSpace X] (v : ℕ → X) {S : Set X}
    (hS : MeasurableSet S) (N : ℕ) :
    (integerClockPrefixLaw v N : Measure X).real S = (countTicks (fun i => v i ∈ S) (N+1):ℝ)/(N+1) := by
  classical
  rw [Measure.real,integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map,Measure.map_apply (measurable_of_finite _) hS]
  change ((PMF.uniformOfFintype (Fin (N+1))).toMeasure {i : Fin (N+1) | v i.val ∈ S}).toReal = _
  rw [PMF.toMeasure_uniformOfFintype_apply (measurableSet_of_discrete _),Fintype.card_fin,
    ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast,Nat.cast_succ]
  congr 1
  change (Fintype.card {i : Fin (N+1) // v i.val ∈ S}:ℝ) = _
  rw [Fintype.card_subtype]
  unfold countTicks
  exact_mod_cast (Finset.card_nbij' (fun i _ => i.val) (fun j hj => ⟨j,Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩)
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,(Finset.mem_filter.mp hi).2⟩)
    (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩)
    (fun _ _ => rfl) (fun _ _ => rfl))

/-- On a prescribed winding clock all the unpinned coordinates fall in
the strict forward arc with frequency r to the number of those coordinates. -/
theorem pinned_box_frequency {I : Type*} [Fintype I] [DecidableEq I] (ω : I → ℝ)
    (hi : RationallyIndependentFrequency ω) (b : I) {τ : ℝ} (hτ : τ ≠ 0)
    (l : ℤ) (hl : τ*ω b=(l:ℝ)*(2*Real.pi)) (a : ℝ) (r : Icc (0:ℝ) (1/2)) :
    let J := {j : I // j ≠ b}
    let test := fun k : ℕ => finiteClockPhasePoint (fun j : J => ω j) (a+(k:ℝ)*τ) ∈ openBox J r
    Tendsto (fun N : ℕ => (countTicks test (N+1):ℝ)/(N+1)) atTop (𝓝 ((r:ℝ)^Fintype.card J)) := by
  intro J test
  let v := fun k : ℕ => finiteClockPhasePoint (fun j : J => ω j) (a+(k:ℝ)*τ)
  obtain ⟨hv,hf⟩ := openBox_volume (I := J) r
  have hnull : (finiteTorusHaarProbabilityMeasure J : Measure _) (frontier (openBox J r))=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (pinned_phase_law ω hi b hτ l hl a) hnull
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume,hv] at h
  have hh := (ENNReal.tendsto_toReal (by finiteness : ENNReal.ofReal (r:ℝ)^Fintype.card J ≠ ⊤)).comp h
  rw [ENNReal.toReal_pow,ENNReal.toReal_ofReal r.2.1] at hh
  have ho : IsOpen (openBox J r) := isOpen_set_pi finite_univ (fun _ _ => QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)
  exact hh.congr fun N => prefix_real v ho.measurableSet N

#print axioms pinned_box_frequency
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
