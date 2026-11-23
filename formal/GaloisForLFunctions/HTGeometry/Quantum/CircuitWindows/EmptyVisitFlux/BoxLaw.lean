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

def closedBox (I : Type*) (r : ℝ) : Set (I → UnitAddCircle) := Set.pi univ (fun _ => forwardUnitArc r)

private theorem box_volumes {I : Type*} [Fintype I] (r : Icc (0:ℝ) (1/2)) :
    volume (openBox I r) = ENNReal.ofReal (r:ℝ)^(Fintype.card I) ∧
      volume (frontier (openBox I r))=0 ∧
      volume (closedBox I r) = ENNReal.ofReal (r:ℝ)^(Fintype.card I) ∧
      volume (frontier (closedBox I r))=0 := by
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
    change (Measure.pi (fun _ : I => (volume : Measure UnitAddCircle))) _ = 0
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
      lt_of_le_of_ne hu.2 (fun her => hnot (Or.inr (by rw [←he,her]; exact mem_singleton _)))⟩,he⟩
  have hnull := measure_mono_null hedge (measure_iUnion_null hn)
  have hae : O =ᵐ[volume] C := by
    have hd : ∀ᵐ z ∂volume, z ∉ C \ O := by
      rw [ae_iff]
      simpa only [not_not,setOf_mem_eq] using hnull
    filter_upwards [hd] with z hz
    exact propext ⟨fun h => hsub h,fun h => by_contra fun hn => hz ⟨h,hn⟩⟩
  have hvol : volume C=ENNReal.ofReal (r:ℝ)^Fintype.card I := by
    rw [show volume C = ∏ i : I, volume (forwardUnitArc r) from Measure.pi_pi _ _]
    simp only [volume_forwardUnitArc,Finset.prod_const,Finset.card_univ]
  refine ⟨(measure_congr hae).trans hvol,measure_mono_null ?_ hnull,hvol,measure_mono_null ?_ hnull⟩
  · change closure O \ interior O ⊆ C \ O
    rw [ho.interior_eq]
    exact sdiff_subset_sdiff_left (closure_minimal hsub hc)
  · change closure C \ interior C ⊆ C \ O
    rw [hc.closure_eq]
    exact sdiff_subset_sdiff_right (ho.subset_interior_iff.mpr hsub)

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
  rw [PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet,Fintype.card_fin,
    ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast,Nat.cast_succ]
  congr 1
  change (Fintype.card {i : Fin (N+1) // v i.val ∈ S}:ℝ) = _
  rw [Fintype.card_subtype]
  unfold countTicks
  simp only [Finset.card_filter]
  exact congrArg (Nat.cast : ℕ → ℝ)
    (Fin.sum_univ_eq_sum_range (fun k : ℕ => if v k ∈ S then 1 else (0:ℕ)) (N+1))

private theorem pinned_test_frequency {I : Type*} [Fintype I] [DecidableEq I] (ω : I → ℝ)
    (hi : RationallyIndependentFrequency ω) (b : I) {τ : ℝ} (hτ : τ ≠ 0)
    (l : ℤ) (hl : τ*ω b=(l:ℝ)*(2*Real.pi)) (a : ℝ)
    (S : Set ({j : I // j ≠ b} → UnitAddCircle)) (hm : MeasurableSet S) (hf : volume (frontier S)=0) :
    let v := fun k : ℕ => finiteClockPhasePoint (fun j : {j : I // j ≠ b} => ω j) (a+(k:ℝ)*τ)
    Tendsto (fun N : ℕ => (countTicks (fun k => v k ∈ S) (N+1):ℝ)/(N+1)) atTop (𝓝 (volume.real S)) := by
  intro v
  let J := {j : I // j ≠ b}
  have hnull : (finiteTorusHaarProbabilityMeasure J : Measure _) (frontier S)=0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (pinned_phase_law ω hi b hτ l hl a) hnull
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at h
  have hh := (ENNReal.tendsto_toReal (measure_ne_top volume S)).comp h
  exact hh.congr fun N => prefix_real v hm N

/-- Each measurable continuity set is sampled at its Haar volume on the
clock pinned to the specified endpoint pair. -/
alias pinned_continuity_set_frequency := pinned_test_frequency

/-- On a prescribed winding clock the strict and the closed forward boxes
have the same frequency. Thus endpoint ties have zero tick density. -/
theorem pinned_box_frequencies {I : Type*} [Fintype I] [DecidableEq I] (ω : I → ℝ)
    (hi : RationallyIndependentFrequency ω) (b : I) {τ : ℝ} (hτ : τ ≠ 0)
    (l : ℤ) (hl : τ*ω b=(l:ℝ)*(2*Real.pi)) (a : ℝ) (r : Icc (0:ℝ) (1/2)) :
    let J := {j : I // j ≠ b}
    let v := fun k : ℕ => finiteClockPhasePoint (fun j : J => ω j) (a+(k:ℝ)*τ)
    ∀ S ∈ ({openBox J r,closedBox J r} : Set (Set (J → UnitAddCircle))),
      Tendsto (fun N : ℕ => (countTicks (fun k => v k ∈ S) (N+1):ℝ)/(N+1)) atTop (𝓝 ((r:ℝ)^Fintype.card J)) := by
  intro J v S hS
  obtain ⟨hv,hf,hv',hf'⟩ := box_volumes (I := J) r
  rcases hS with h | h
  · subst S
    have ho : IsOpen (openBox J r) := isOpen_set_pi finite_univ (fun _ _ => QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)
    simpa only [Measure.real,hv,ENNReal.toReal_pow,ENNReal.toReal_ofReal r.2.1] using
      pinned_test_frequency ω hi b hτ l hl a _ ho.measurableSet hf
  · change S=closedBox J r at h
    subst S
    have hc : IsClosed (closedBox J r) := isClosed_set_pi (fun _ _ => isClosed_forwardUnitArc _)
    simpa only [Measure.real,hv',ENNReal.toReal_pow,ENNReal.toReal_ofReal r.2.1] using
      pinned_test_frequency ω hi b hτ l hl a _ hc.measurableSet hf'

#print axioms pinned_box_frequencies
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
