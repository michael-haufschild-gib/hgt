import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateReturnSpacing

/-! # Exact time occupation of a translated spectral phase tube -/
open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

abbrev Register (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Times when the spectral phases, relative to a fixed phase at each
eigenvector, fit in a single arc of length r turns. -/
def shiftedTimes {n : ℕ} (H : selfAdjoint (Register n)) (ψ : (Fin n → Bool) → ℝ) (r : ℝ) : Set ℝ :=
  {t | spectralEnclosingArcLength (fun j => -(t*H.2.isHermitian.eigenvalues j)-ψ j) ≤ 2*Real.pi*r}

/-- Translating the individual eigenphases preserves the exact short-arc
occupation from every fixed time origin. -/
theorem shiftedTimes_occupation {n : ℕ} (H : selfAdjoint (Register n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (ψ : (Fin n → Bool) → ℝ) (r : Icc (0:ℝ) (1/2)) (a : ℝ) :
    Tendsto (fun T => volume.real (shiftedTimes H ψ r ∩ Icc a T)/(T-a)) atTop
      (𝓝 (zeroGateArcDensity (2^n) r)) := by
  classical
  let i : Fin n → Bool := fun _ => false
  let E := H.2.isHermitian.eigenvalues
  let ω := projectiveFrequency (fun j => -E j) i
  let b : {j // j ≠ i} → UnitAddCircle := fun j => (((ψ i-ψ j)/(2*Real.pi):ℝ):UnitAddCircle)
  let X := relativeEnclosingUnitArc i r
  let g (x : {j // j ≠ i} → UnitAddCircle) := x+b
  have hcont : Continuous g := continuous_id.add continuous_const
  have hclosed : IsClosed X := isClosed_relativeEnclosingUnitArc i r
  have hmeas := measurePreserving_add_right (volume : Measure ({j // j ≠ i} → UnitAddCircle)) b
  have htarget : shiftedTimes H ψ r = (finiteClockPhasePoint ω) ⁻¹' (g ⁻¹' X) := by
    ext t
    let θ (j : Fin n → Bool) := -(t*E j)-ψ j
    let y (j : Fin n → Bool) := ((θ j/(2*Real.pi):ℝ):UnitAddCircle)
    have hval (j : Fin n → Bool) :
        relativeUnitPhasePacket i (g (finiteClockPhasePoint ω t)) j = y j-y i := by
      by_cases h : j=i
      · subst j; simp [relativeUnitPhasePacket]
      · simp only [relativeUnitPhasePacket,dif_pos h]
        change ((t*(-E j - -E i)/(2*Real.pi):ℝ):UnitAddCircle) + _ = _ - _
        change ((t*(-E j - -E i)/(2*Real.pi):ℝ):UnitAddCircle) +
          (((ψ i-ψ j)/(2*Real.pi):ℝ):UnitAddCircle) = _ - _
        dsimp only [y,θ]
        rw [←AddCircle.coe_add,←AddCircle.coe_sub]
        congr 1
        ring
    change spectralEnclosingArcLength θ ≤ 2*Real.pi*(r:ℝ) ↔
      relativeUnitPhasePacket i (g (finiteClockPhasePoint ω t)) ∈ enclosingUnitArc r
    rw [←mem_enclosingUnitArc_iff_spectralEnclosingArcLength θ r]
    simp only [enclosingUnitArc,mem_iUnion,anchoredUnitArc,mem_setOf_eq,hval,sub_sub_sub_cancel_right,y]
  have hω : RationallyIndependentFrequency ω :=
    maximallyProjectiveEnergy_projectiveFrequency_independent _ (maximallyProjectiveEnergy_neg hmax) i
  have hnull : volume (frontier (g ⁻¹' X)) = 0 := by
    apply measure_mono_null (hcont.frontier_preimage_subset X)
    rw [show volume (g ⁻¹' frontier X) = volume (frontier X) from
      hmeas.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet]
    exact volume_frontier_relativeEnclosingUnitArc i r
  have hF : (finiteTorusHaarProbabilityMeasure {j // j ≠ i} : Measure _) (frontier (g ⁻¹' X)) = 0 := by
    rwa [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (clockPhaseWindowLaw_tendsto_haar ω hω) hF
  have hmass : volume (g ⁻¹' X) = volume X :=
    hmeas.measure_preimage hclosed.measurableSet.nullMeasurableSet
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume,hmass,volume_relativeEnclosingUnitArc i r,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at h
  have htgt := hclosed.preimage hcont
  have hphys : MeasurableSet (shiftedTimes H ψ r) := by
    rw [htarget]
    exact htgt.measurableSet.preimage (finiteClockPhasePoint_continuous ω).measurable
  apply tendsto_occupation_from_start _ hphys
  have eqm (T : ℝ) : (clockPhaseWindowLaw ω T : Measure _) (g ⁻¹' X) =
      (windowProbabilityMeasure T : Measure ℝ) (shiftedTimes H ψ r) := by
    rw [clockPhaseWindowLaw,ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (finiteClockPhasePoint_continuous ω).measurable htgt.measurableSet,htarget]
  have h' := h.congr eqm
  have hfin : ((↑(2^n:ℕ):ℝ≥0∞)*ENNReal.ofReal (r:ℝ)^(2^n-1)) ≠ ⊤ := by finiteness
  have hreal := (ENNReal.tendsto_toReal hfin).comp h'
  change Tendsto (fun T => ((windowProbabilityMeasure T : Measure ℝ) (shiftedTimes H ψ r)).toReal) atTop
    (𝓝 (((↑(2^n:ℕ):ℝ≥0∞)*ENNReal.ofReal (r:ℝ)^(2^n-1)).toReal)) at hreal
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal r.2.1,zeroGateArcDensity] using hreal

#print axioms shiftedTimes_occupation
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
