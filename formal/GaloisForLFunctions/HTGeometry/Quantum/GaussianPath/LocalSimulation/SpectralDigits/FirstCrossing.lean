import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralDigits.PhysicalCost
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.ThreeGateUpper
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth

/-! # Hard spectral digits at the first robust physical crossing -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralDigits
open SpectralGapMass.PhysicalTimes ClockSpectrum FirstGate.Boundary
open _root_.RHTower.PrimeCirclePeriodization
noncomputable section

/-- One of eight fixed functions of the energy and elapsed time. Its
two eigenvalues and selected eigenspaces are prescribed by the digit index. -/
def physicalDigit {n : ℕ} (u : PathShell n) (t : ℝ) (j : Fin 8) :=
  digitMatrix (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvectorUnitary (physicalTurns u t) j

theorem hard_physical_digit {n s : ℕ} (u : PathShell n) (t : ℝ)
    (h : ¬HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution (pathHamiltonian u) t)) :
    ∃ j : Fin 8, ¬HasProjectiveCircuitApproximation (n+2) (1/100) (s/8) (physicalDigit u t j) := by
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let V := hH.eigenvectorUnitary
  have he (i) : Complex.exp (-(Complex.I*((t:ℂ)*hH.eigenvalues i)))=expTurns (physicalTurns u t i) := by
    rw [physicalTurns,expTurns_turns,fourier_phase]
    dsimp only [hH]
    congr 1
    push_cast
    ring
  have hU : unitaryEvolution (pathHamiltonian u) t=spectralFunction V (fun i => expTurns (physicalTurns u t i)) := by
    rw [unitaryEvolution_spectral hH]
    simp only [he]
    rfl
  rw [hU] at h
  exact exists_hard_digit V _ (fun i => ⟨(turns_mem _).1.le,(turns_mem _).2⟩) s h

/-- At the first crossing a specified digit already excludes budget P/8.
At every point of its full local travel interval, some digit excludes P/16. -/
theorem gaussian_first_crossing_hard_digit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Matrix (Fin N→Bool) (Fin N→Bool) ℂ) :=
        ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ : ℝ, LocalPatches.localCrossingWidth N < σ ∧ orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (∃ j : Fin 8, ¬HasProjectiveCircuitApproximation N (1/100) (P/8) (physicalDigit x σ j)) ∧
        ∀ t : ℝ, |σ-t| ≤ LocalPatches.localCrossingWidth N →
          ∃ j : Fin 8, ¬HasProjectiveCircuitApproximation N (1/100) (P/16) (physicalDigit x t j) := by
  filter_upwards [LocalPatches.gaussian_first_crossing_local_width,LocalPatches.gaussian_local_robust_travel_time]
    with ω hω hw
  filter_upwards [hω,hw] with k hn htravel
  intro N x H P
  obtain ⟨σ,hσ,he,hprior,_⟩ := hn
  refine ⟨σ,hσ,he,hprior,hard_physical_digit x σ ?_,?_⟩
  · intro h
    have hh := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp h
    change orbitCircuitDistance H P σ ≤ 1/10 at hh
    rw [he] at hh
    norm_num at hh
  · intro t ht
    have hh : ¬HasProjectiveCircuitApproximation N (1/10) (P/2) (unitaryEvolution H.val t) :=
      fun h => (htravel σ t he.ge (P/2) le_rfl h).not_ge ht
    simpa only [Nat.div_div_eq_div_mul] using hard_physical_digit x t hh

#print axioms gaussian_first_crossing_hard_digit
end
end GaloisForLFunctions.HTGeometry.SpectralDigits
