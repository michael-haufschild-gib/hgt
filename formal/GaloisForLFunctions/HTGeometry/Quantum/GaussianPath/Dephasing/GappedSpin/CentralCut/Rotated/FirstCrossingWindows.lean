import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.PhysicalSector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.WindowOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.IncrementClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.OccupationBand

/-! # Plateau windows around the original crossing and typical dates on one frozen trajectory -/
open Set Filter Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes AccuracyScales.TenthPlateau SharpOccupation WeakBonds.NearDiagonal
open private crossingTimes crossing_least from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin
noncomputable section

private theorem distance_at_positive_crossing {n P : ℕ} (u : PathShell n)
    (hpos : 0 < crossingOrigin n P (9/80) (fun i => u (pathCoeffEquiv n i))) :
    let x := fun i => u (pathCoeffEquiv n i)
    let H : selfAdjoint (SharpOccupation.Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    9/80 ≤ orbitCircuitDistance H P (crossingOrigin n P (9/80) x) := by
  intro x H
  have hn : (crossingTimes n P (9/80) x).Nonempty := by
    by_contra he
    have h := not_nonempty_iff_eq_empty.mp he
    change 0 < sInf (crossingTimes n P (9/80) x) at hpos
    rw [h,Real.sInf_empty] at hpos
    exact lt_irrefl _ hpos
  have he := (crossing_least hn).1.2
  change 9/80 ≤ pathGateDistance n P (fun i => u (pathCoeffEquiv n i)) _ at he
  rw [pathGateDistance,numberedGenerator_shell] at he
  exact he

/-- On the same Gaussian draw, the full symmetric window about the
original first crossing contains no half-budget fit. The fraction of
centers whose radius-T window contains such a fit is exponentially
small in dimension, even for length-dependent record origins. -/
theorem first_crossing_and_moving_windows :
    ∃ C > (0:ℝ), ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ T ≥ (1:ℝ), ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let x := fun i => u (pathCoeffEquiv n i)
          let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
          let σ := crossingOrigin n P (9/80) x
          let F := nearbyVisit H (P/2) T
          x ∈ allCoordStrongEvent n (1/100) ∧ T < σ ∧ (∀ s ≤ P/2, T < crossingWait n P s x) ∧
          σ ∉ F ∧ (∃ m : ℕ, P < m ∧ m ≤ (2*K+1)*2^K ∧ IsRecurrentOrbitCircuitMaximumAt H (1/10) m) ∧
          ∀ a : ℝ→ℝ, ∀ᶠ L : ℝ in atTop, volume.real (F ∩ Icc (a L) (a L+L))/L < b^(2^K:ℕ) := by
  obtain ⟨C,hC,hbox⟩ := physical_joint_sector
  obtain ⟨b,hb,hwin⟩ := cheap_window_occupation
  obtain ⟨_,_,hband⟩ := capped_path_occupation
  refine ⟨C,hC,b,hb,?_⟩
  filter_upwards [hbox,hwin,hband,delay_of_cheap] with k hk hw hm hd
  intro n K P T hT
  obtain ⟨B,E,hB,hE,hprob,hprop⟩ := hk T hT
  refine ⟨E,hE,hprob,?_⟩
  filter_upwards [hw,hd,gaussian_path_all_prefixes_maximally_projective] with ω hω hclock hspec
  intro he u x H σ F
  obtain ⟨hstrong,hglobal,hinc⟩ := hprop ω he
  have hT₀ := zero_lt_one.trans_le hT
  obtain ⟨ho,hr⟩ := hclock T hT₀ B hB hinc
  obtain ⟨m,hmin,hmax,hrec,_⟩ := hm u (hspec k) (2*K+1) (by omega) hglobal
  refine ⟨hstrong,ho,hr,?_,⟨m,hmin,hmax,hrec⟩,hω T B hB hinc⟩
  intro hbad
  have hfit := nearbyVisit_subset H hB hinc hbad
  have hlo := distance_at_positive_crossing u (hT₀.trans ho)
  have hhi : orbitCircuitDistance H P σ ≤ 11/100 :=
    (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hfit
  change 9/80 ≤ orbitCircuitDistance H P σ at hlo
  linarith only [hlo,hhi]

#print axioms first_crossing_and_moving_windows
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
