import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.JointRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.HaarRectangles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralTargets.NullBoundary
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateBudgetDistribution
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow

/-! # Joint gate-count occupation at incommensurate speeds on a single chain -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open SharpOccupation ResonantDraws
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- At incommensurate speeds every prescribed pattern of affordable and
unaffordable observations has its product Haar probability along one draw.
Each reading may have its own origin, tolerance and gate budget. -/
theorem gaussian_joint_affordable_fraction {I : Type} [Fintype I]
    (c : I→ℝ) (hc : RationallyIndependentFrequency c) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let n := k+1
      let u := pathPauliDisorderShell ω n
      let x := fun i => u (pathCoeffEquiv n i)
      ∀ (hit : I→Bool) (s : I→ℕ) (ε o : I→ℝ) (a : ℝ→ℝ),
        Tendsto (fun T => volume.real
          ({t | ∀ i, (pathGateDistance n (s i) x (o i+c i*t)≤ε i) ↔ hit i=true} ∩ Icc (a T) (a T+T))/T)
          atTop (𝓝 (∏ i, let p := affordablePhaseMass k (s i) (ε i) ω
            if hit i then p else 1-p)) := by
  classical
  filter_upwards [gaussian_joint_phase_rank c hc,gaussian_path_all_prefixes_maximally_projective] with ω hr hmax
  intro k n u x hit s ε o a
  let N := k+3
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E := fun j => H.2.isHermitian.eigenvalues (e.symm j)
  let f := RHTower.zeroProjectiveFrequency E
  let g := fun p : I×Fin (2^N-1) => c p.1*f p.2
  let z (i : I) := finiteClockPhasePoint f (o i)
  let A (i : I) := projectiveContinuousCircuitCaptureTarget e V (s i) (ε i)
  have hi : MaximallyProjectiveEnergy E := maximallyProjectiveEnergy_equiv e.symm (hmax k)
  let B (i : I) := if hit i then A i else (A i)ᶜ
  have hA i : MeasurableSet (A i) := (isClosed_projectiveContinuousCircuitCaptureTarget e V (s i) (ε i)).measurableSet
  have hn i : volume (frontier (A i))=0 := PhaseBoundary.spectral_target_null e V E hi (s i) (ε i)
  have hB i : MeasurableSet (B i) := by
    cases h : hit i <;> simp only [B,h,Bool.false_eq_true,if_false,if_true]
    · exact (hA i).compl
    · exact hA i
  have hnull i : volume (frontier (B i))=0 := by
    cases h : hit i <;> simpa only [B,h,Bool.false_eq_true,if_false,if_true,frontier_compl] using hn i
  obtain ⟨hm,hb,hprod⟩ := phaseRectangle_spec B z hB hnull
  have h := PhaseBoundary.uniform_phase_fraction g (hr k) _ hm hb a
  rw [hprod] at h
  have he : finiteClockPhasePoint g ⁻¹' phaseRectangle B z =
      {t | ∀ i, (pathGateDistance n (s i) x (o i+c i*t)≤ε i) ↔ hit i=true} := by
    ext t
    apply forall_congr'
    intro i
    have hrow : (fun j => finiteClockPhasePoint g t (i,j)) = finiteClockPhasePoint f (c i*t) := by
      funext j
      change ((t*(c i*f j)/(2*Real.pi):ℝ):UnitAddCircle) = (((c i*t)*f j/(2*Real.pi):ℝ):UnitAddCircle)
      rw [←mul_assoc,mul_comm t]
    change z i+(fun j => finiteClockPhasePoint g t (i,j)) ∈ B i ↔ _
    rw [hrow,show z i=finiteClockPhasePoint f (o i) from rfl,←finiteClockPhasePoint_add]
    have hphys := physical_circuit_approximation_iff_spectral_capture e H (s i) (ε i) (o i+c i*t)
    rw [hasProjectiveCircuitApproximation_iff_infDist] at hphys
    have hfit : pathGateDistance n (s i) x (o i+c i*t) ≤ ε i ↔
        finiteClockPhasePoint f (o i+c i*t) ∈ A i := by
      rw [pathGateDistance,show numberedGenerator n x=H.val from numberedGenerator_shell u]
      exact hphys
    cases hi : hit i <;> simp only [B,hi,Bool.false_eq_true,if_false,if_true,mem_compl_iff,
      iff_false,iff_true,←hfit]
  rw [he] at h
  convert h using 2
  apply Finset.prod_congr rfl
  intro i _
  change (if hit i then volume.real (A i) else 1-volume.real (A i))=volume.real (B i)
  cases hi : hit i <;> simp only [B,hi,Bool.false_eq_true,if_false,if_true,
    measureReal_compl (hA i),probReal_univ]

#print axioms gaussian_joint_affordable_fraction
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
