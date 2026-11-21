import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Weyl
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhaseBoxes

/-! # Enclosing-arc probabilities on an affine lattice of observation times -/
open Filter MeasureTheory Set Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling
noncomputable section

/-- Distribution of physical observation times on a finite lattice prefix. -/
def timeLaw (a τ : ℝ) (N : ℕ) : Measure ℝ :=
  integerClockPrefixLaw (fun j : ℕ => a+(j:ℝ)*τ) N

instance (a τ : ℝ) (N : ℕ) : IsProbabilityMeasure (timeLaw a τ N) :=
  inferInstanceAs (IsProbabilityMeasure (integerClockPrefixLaw (fun j : ℕ => a+(j:ℝ)*τ) N : Measure ℝ))

private theorem prefix_preimage {I : Type*} [Fintype I] (ω : I → ℝ) (a τ : ℝ) (N : ℕ)
    {A : Set (I → UnitAddCircle)} (hA : MeasurableSet A) :
    timeLaw a τ N (finiteClockPhasePoint ω ⁻¹' A) =
      (integerClockPrefixLaw (fun j : ℕ => finiteClockPhasePoint ω (a+(j:ℝ)*τ)) N : Measure _) A := by
  simp only [timeLaw,integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (measurable_of_finite _) (hA.preimage (finiteClockPhasePoint_continuous ω).measurable),
    Measure.map_apply (measurable_of_finite _) hA]
  rfl

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Times at which the individually shifted phases fit in an arc of r turns. -/
def arcTimes [Nonempty I] (E ψ : I → ℝ) (r : ℝ) : Set ℝ :=
  {t | spectralEnclosingArcLength (fun j => t*E j+ψ j) ≤ 2*Real.pi*r}

omit [DecidableEq I] in
private theorem arc_restrict [Nonempty I] {J : Type*} [Fintype J] [Nonempty J]
    (f : J → I) (E ψ : I → ℝ) (r : ℝ) :
    arcTimes E ψ r ⊆ arcTimes (E ∘ f) (ψ ∘ f) r := by
  intro t ht
  let θ := fun j => t*E j+ψ j
  obtain ⟨c,hc⟩ := exists_spectralEnclosingArc_center θ
  exact ((spectralEnclosingArcLength_le_twice_radius (θ ∘ f) c _ (fun j => hc (f j))).trans_eq
    (by ring : 2*(spectralEnclosingArcLength θ/2) = spectralEnclosingArcLength θ)).trans ht

/-- A nonresonant relative spectrum gives the exact arc probability on every
affine lattice, for every translate of the phase target. -/
theorem arc_timeLaw [Nonempty I] (E ψ : I → ℝ) (i : I) (r : Icc (0:ℝ) (1/2))
    (a τ : ℝ) (hf : FreeAtStep (projectiveFrequency E i) τ) :
    Tendsto (fun N => (timeLaw a τ N).real (arcTimes E ψ r)) atTop
      (𝓝 (zeroGateArcDensity (Fintype.card I) r)) := by
  classical
  let ω := projectiveFrequency E i
  let b : {j // j ≠ i} → UnitAddCircle := fun j => (((ψ j-ψ i)/(2*Real.pi):ℝ):UnitAddCircle)
  let X := relativeEnclosingUnitArc i r
  let g (x : {j // j ≠ i} → UnitAddCircle) := x+b
  have hc : Continuous g := continuous_id.add continuous_const
  have hX := isClosed_relativeEnclosingUnitArc i (r:ℝ)
  have hp := measurePreserving_add_right (volume : Measure ({j // j ≠ i} → UnitAddCircle)) b
  have he : arcTimes E ψ r = finiteClockPhasePoint ω ⁻¹' (g ⁻¹' X) := by
    ext t
    let θ := fun j => t*E j+ψ j
    let y (j : I) := ((θ j/(2*Real.pi):ℝ):UnitAddCircle)
    have hv (j : I) : relativeUnitPhasePacket i (g (finiteClockPhasePoint ω t)) j = y j-y i := by
      by_cases h : j=i
      · subst j; simp [relativeUnitPhasePacket]
      · simp only [relativeUnitPhasePacket,dif_pos h]
        change ((t*(E j-E i)/(2*Real.pi):ℝ):UnitAddCircle) +
          (((ψ j-ψ i)/(2*Real.pi):ℝ):UnitAddCircle) = _ - _
        dsimp only [y,θ]
        rw [←AddCircle.coe_add,←AddCircle.coe_sub]
        congr 1
        ring
    change spectralEnclosingArcLength θ ≤ 2*Real.pi*(r:ℝ) ↔
      relativeUnitPhasePacket i (g (finiteClockPhasePoint ω t)) ∈ enclosingUnitArc r
    rw [←mem_enclosingUnitArc_iff_spectralEnclosingArcLength θ r]
    simp only [enclosingUnitArc,mem_iUnion,anchoredUnitArc,mem_setOf_eq,hv,sub_sub_sub_cancel_right,y]
  have hb : volume (frontier (g ⁻¹' X)) = 0 := by
    apply measure_mono_null (hc.frontier_preimage_subset X)
    rw [hp.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet]
    exact volume_frontier_relativeEnclosingUnitArc i r
  have hnull : (finiteTorusHaarProbabilityMeasure {j // j ≠ i} : Measure _) (frontier (g ⁻¹' X)) = 0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (affine_phaseLaw ω τ a hf) hnull
  have hvol : volume (g ⁻¹' X) = volume X := hp.measure_preimage hX.measurableSet.nullMeasurableSet
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume,hvol,volume_relativeEnclosingUnitArc i r] at h
  have eqm (N : ℕ) : (integerClockPrefixLaw (fun j : ℕ => finiteClockPhasePoint ω (a+(j:ℝ)*τ)) N :
      Measure _) (g ⁻¹' X) = timeLaw a τ N (arcTimes E ψ r) := by
    rw [he]
    exact (prefix_preimage ω a τ N (A := g ⁻¹' X) (hX.preimage hc).measurableSet).symm
  have hreal := (ENNReal.tendsto_toReal (by finiteness :
    (Fintype.card I : ℝ≥0∞) * ENNReal.ofReal (r:ℝ)^(Fintype.card I-1) ≠ ⊤)).comp (h.congr eqm)
  simpa only [Measure.real,Function.comp_def,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal r.2.1,zeroGateArcDensity] using hreal

omit [DecidableEq I] in
private theorem free_reindex {J : Type*} [Fintype J] (e : J ≃ I)
    (ω : I → ℝ) {τ : ℝ} (h : FreeAtStep ω τ) : FreeAtStep (ω ∘ e) τ := by
  intro m k hm
  have hd : finiteTorusCharacterDetuning m (ω ∘ e) = finiteTorusCharacterDetuning (m ∘ e.symm) ω := by
    simpa only [finiteTorusCharacterDetuning,Function.comp_apply,Equiv.symm_apply_apply] using
      e.sum_comp (fun i => ((m (e.symm i):ℤ):ℝ)*ω i)
  rw [hd] at hm
  have hh := h _ k hm
  funext j
  simpa only [Function.comp_apply,Equiv.symm_apply_apply,Pi.zero_apply] using congrFun hh (e j)

/-- Deleting b before or after passing to phases relative to i labels the
same surviving energy differences. -/
private def swapDeletion (i : I) (b : {j : I // j ≠ i}) :
    {j : {k : I // k ≠ b.val} // j ≠ (⟨i,b.property.symm⟩ : {k : I // k ≠ b.val})} ≃
      {j : {k : I // k ≠ i} // j ≠ b} where
  toFun j := ⟨⟨j.val.val,fun h => j.property (Subtype.ext h)⟩,fun h => j.val.property (congrArg Subtype.val h)⟩
  invFun j := ⟨⟨j.val.val,fun h => j.property (Subtype.ext h)⟩,fun h => j.val.property (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Arc event after removing energy b. The distinct reference i ensures
that the retained spectrum is nonempty. -/
def retainedArcTimes (i : I) (b : {j : I // j ≠ i}) (E ψ : I → ℝ) (r : ℝ) : Set ℝ :=
  letI : Nonempty {j : I // j ≠ b.val} := ⟨⟨i,b.property.symm⟩⟩
  arcTimes (fun j : {k : I // k ≠ b.val} => E j) (fun j => ψ j) r

/-- At every nonzero sampling period one can discard a single energy so
that the restricted arc event has its full Haar frequency. The same deletion
works for every time origin, phase translate and angular tolerance. -/
theorem exists_arc_majorant [Nonempty I] (E : I → ℝ) (hi : MaximallyProjectiveEnergy E)
    (i : I) [Nonempty {j : I // j ≠ i}] (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ b : {j : I // j ≠ i}, ∀ (ψ : I → ℝ) (r : Icc (0:ℝ) (1/2)) (a : ℝ),
      arcTimes E ψ r ⊆ retainedArcTimes i b E ψ r ∧
        Tendsto (fun N => (timeLaw a τ N).real (retainedArcTimes i b E ψ r)) atTop
          (𝓝 (zeroGateArcDensity (Fintype.card I-1) r)) := by
  classical
  obtain ⟨b,hb⟩ := exists_free_deletion _ (maximallyProjectiveEnergy_projectiveFrequency_independent E hi i) τ hτ
  let K := {k : I // k ≠ b.val}
  let ref : K := ⟨i,b.property.symm⟩
  letI : Nonempty K := ⟨ref⟩
  have hf : FreeAtStep (projectiveFrequency (fun j : K => E j) ref) τ := free_reindex (swapDeletion i b) _ hb
  have hcard : Fintype.card K = Fintype.card I-1 := by
    rw [Fintype.card_subtype_compl (fun j => j=b.val),Fintype.card_subtype_eq]
  refine ⟨b,fun ψ r a => ⟨arc_restrict (fun j : K => j.val) E ψ r,?_⟩⟩
  rw [←hcard]
  exact arc_timeLaw _ _ ref r a τ hf

#print axioms exists_arc_majorant
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling
