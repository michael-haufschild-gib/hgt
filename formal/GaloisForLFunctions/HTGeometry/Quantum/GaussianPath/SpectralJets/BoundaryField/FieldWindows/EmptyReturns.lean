import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.FixedDate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateExactOccupation

/-! # Empty-circuit probability at one prescribed time with a shrinking terminal field -/
open Filter Topology MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private theorem arc_perm {I : Type} [Fintype I] [DecidableEq I] (f : I→ℝ) (e : Equiv.Perm I)
    (r : I) (t x : ℝ) :
    finiteClockPhasePoint (projectiveFrequency (f ∘ e) r) t ∈ relativeEnclosingUnitArc r x ↔
    finiteClockPhasePoint (projectiveFrequency f (e r)) t ∈ relativeEnclosingUnitArc (e r) x := by
  let phase (u : ℝ) := ((t*u/(2*Real.pi):ℝ):UnitAddCircle)
  have hv (g : I→ℝ) (a j : I) : relativeUnitPhasePacket a
      (finiteClockPhasePoint (projectiveFrequency g a) t) j=phase (g j)-phase (g a) := by
    rcases eq_or_ne j a with rfl | hj
    · simp [relativeUnitPhasePacket]
    · simp only [relativeUnitPhasePacket,dif_pos hj]
      dsimp only [phase]
      rw [←AddCircle.coe_sub]
      change ((t*(g j-g a)/(2*Real.pi):ℝ):UnitAddCircle)=_
      exact congrArg (fun v : ℝ => (v:UnitAddCircle)) (show t*(g j-g a)/(2*Real.pi)=_ by ring)
  simp only [relativeEnclosingUnitArc,mem_preimage,enclosingUnitArc,mem_iUnion,anchoredUnitArc,
    mem_setOf_eq,hv,sub_sub_sub_cancel_right,Function.comp_apply]
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨e j,fun l hl => ?_⟩
    simpa only [Equiv.apply_symm_apply] using hj (e.symm l) (fun he => hl ((e.symm_apply_eq).mp he))
  · rintro ⟨j,hj⟩
    refine ⟨e.symm j,fun l hl => ?_⟩
    simpa only [Equiv.apply_symm_apply] using hj (e l) (fun he => hl ((e.apply_eq_iff_eq_symm_apply).mp he))

private abbrev Reg (k : ℕ) := Matrix (Fin (k+3)→Bool) (Fin (k+3)→Bool) ℂ

/-- At a prescribed date T, uniformly sample only the terminal Z field in
[b,b+w]. Its empty-circuit probability tends to the exact arc-occupation
polynomial, even for w→0 if Tw→∞. -/
theorem gaussian_fixed_date_empty_returns :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ b ∉ B,
      ∀ (r : Icc (0:ℝ) 1) (w T : ℕ→ℝ), Tendsto w atTop (𝓝 0) →
      (∀ᶠ n in atTop, 0<w n) → Tendsto (fun n => T n*w n) atTop atTop →
      Tendsto (fun n => (unitIntervalProbabilityMeasure : Measure ℝ).real {s |
        let z := b+w n*s
        let H : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
        T n∈zeroGateReturnSet H r}) atTop (𝓝 (zeroGateArcOccupationPolynomial (2^(k+3)) r)) := by
  filter_upwards [gaussian_boundary_fixed_date_haar] with ω hω
  intro k
  obtain ⟨B,hB,hh⟩ := hω k
  refine ⟨B,hB,?_⟩
  intro b hb r w T hw hp ht
  let i : Fin (k+3)→Bool := fun _ => false
  let X := relativeEnclosingUnitArc i (r:ℝ)
  obtain ⟨hf,hμ⟩ := hh b hb i
  let E (z : ℝ) := (boundaryHermitian ω k z).eigenvalues
  let e := Fintype.equivFin (Fin (k+3)→Bool)
  let p (z : ℝ) := (e.trans (Tuple.sort (E z ∘ e.symm))).trans e.symm
  have hnull : (finiteTorusHaarProbabilityMeasure {j // j≠i} : Measure _) (frontier X)=0 := by
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    exact volume_frontier_relativeEnclosingUnitArc i r
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (hμ w T hw hp ht) hnull
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at h
  have hz := (ENNReal.tendsto_toReal (measure_ne_top _ X)).comp h
  change Tendsto (fun n => (fieldWindowLaw _ hf b (w n) (T n) : Measure _).real X) atTop (𝓝 (volume.real X)) at hz
  have hm : volume.real X=zeroGateArcOccupationPolynomial (2^(k+3)) r := zeroGateFullArcMass_eq_exactPolynomial _ r
  rw [hm] at hz
  apply hz.congr
  intro n
  rw [fieldWindowLaw_real _ _ _ _ _ (isClosed_relativeEnclosingUnitArc i r).measurableSet]
  congr 1
  ext s
  let z := b+w n*s
  let H : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
  change _ ↔ T n∈zeroGateReturnSet H r
  rw [zeroGateReturnSet_eq_preimage_full H (p z i) r]
  exact arc_perm (fun j => -E z j) (p z) i (T n) r

#print axioms gaussian_fixed_date_empty_returns
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
