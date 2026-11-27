import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.BudgetLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.CriticalHeights

/-! # The all-time gate budget as an atom of the Haar affordable fraction -/
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws SharpOccupation
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- The prefix needs at most s gates for its entire orbit at error ε. -/
def orbitBudget (n s : ℕ) (ε : ℝ) : Set (PrefixIndex n→ℝ) :=
  {x | ∀ t, pathGateDistance n s x t ≤ ε}

theorem isClosed_orbitBudget (n s : ℕ) (ε : ℝ) : IsClosed (orbitBudget n s ε) := by
  simp only [orbitBudget,setOf_forall]
  exact isClosed_iInter fun t => isClosed_le (continuous_distance_at_time n s t) continuous_const

theorem orbitBudget_iff_maximum_le {n s m : ℕ} (u : PathShell n) (ε : ℝ)
    (h : IsRecurrentOrbitCircuitMaximumAt ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ ε m) :
    (fun i => u (pathCoeffEquiv n i)) ∈ orbitBudget n s ε ↔ m ≤ s := by
  let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  have he (j : ℕ) (t : ℝ) : pathGateDistance n j (fun i => u (pathCoeffEquiv n i)) t≤ε ↔
      HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution H.val t) := by
    rw [hasProjectiveCircuitApproximation_iff_infDist,pathGateDistance,numberedGenerator_shell]
  constructor
  · intro hcap
    obtain ⟨t,ht⟩ := AccuracyScales.MaximumIntervals.required_at_some_date h
    exact ht s ((he s t).mp (hcap t))
  · intro hms t
    obtain ⟨z,hz,C,hC,hfit⟩ := h.1 t
    exact (he s t).mpr ⟨z,hz,C,hC.trans hms,hfit⟩

/-- On a full-rank physical orbit, an affordable fraction of one means
the budget covers every date. A missed phase has an open neighborhood. -/
theorem unit_fraction_iff_orbitBudget (k s : ℕ) (ε : ℝ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      affordablePhaseMass k s ε ω=1 ↔ x∈orbitBudget (k+1) s ε := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hw
  intro x
  let N := k+3
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let A := projectiveContinuousCircuitCaptureTarget e V s ε
  have hA := isClosed_projectiveContinuousCircuitCaptureTarget e V s ε
  have hi := maximallyProjectiveEnergy_equiv e.symm (hw k)
  have he : x∈orbitBudget (k+1) s ε ↔ ∀ z, z∈A := by
    refine Iff.trans (forall_congr' fun t => ?_) ((uniform_circuit_budget_iff_all_spectral_phases e H hi s ε).trans
      (forall_congr' fun z => (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε z).symm))
    rw [pathGateDistance,show numberedGenerator (k+1) x=H.val from numberedGenerator_shell u,
      hasProjectiveCircuitApproximation_iff_infDist]
  rw [he]
  change volume.real A=1 ↔ ∀ z, z∈A
  constructor
  · intro hp z
    by_contra hn
    have hpos := ENNReal.toReal_pos (hA.isOpen_compl.measure_pos volume ⟨z,hn⟩).ne' (measure_ne_top _ _)
    change 0<volume.real Aᶜ at hpos
    rw [measureReal_compl hA.measurableSet,probReal_univ,hp,sub_self] at hpos
    exact (lt_irrefl _ hpos)
  · intro hall
    rw [show A=univ from eq_univ_of_forall hall,probReal_univ]

#print axioms unit_fraction_iff_orbitBudget
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
