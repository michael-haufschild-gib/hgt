import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.PhysicalReturns
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.MaximumClearance

/-! # A finite observation deadline for the exact maximum at a prescribed error -/
open Filter Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
open SharpOccupation AccuracyScales.MaximumIntervals
open PrescribedTimes.ResonantDraws.FirstPassageSelection (predecessor_clearance)
noncomputable section

/-- Positive clearance of the predecessor determines how closely to repeat
a worst date. A zero maximum is already observed at the record origin. -/
def maximumResolution {N : ℕ} (H : selfAdjoint (Register N)) (m : ℕ) (ε : ℝ) : ℝ :=
  if m=0 then 1 else min 1 ((criticalHeight H (m-1)-ε)/2)

private theorem maximum_windows_of_scalar {N m : ℕ} {ε : ℝ} (H : selfAdjoint (Register N))
    (hm : IsRecurrentOrbitCircuitMaximumAt H ε m) (G : ℝ → ℝ)
    (hclock : ∀ r ∈ Ioc (0:ℝ) π, ∀ a : ℝ, ∃ w ∈ Icc a (a+G r),
      HasProjectiveCircuitApproximation N r 0 (unitaryEvolution H.val w)) :
    let ρ := maximumResolution H m ε
    0 < ρ ∧ ∀ a : ℝ, ∃ z ∈ Icc a (a+G ρ), ∀ t : ℝ,
      circuitHamiltonianSpectralWidth H*|t-z| ≤ ρ → ∀ s,
        HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val t) ↔ m ≤ s := by
  let ρ := maximumResolution H m ε
  have hcap (z : ℝ) (s : ℕ) (hs : m ≤ s) :
      HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val z) := by
    obtain ⟨c,hc,C,hC,hh⟩ := hm.1 z
    exact ⟨c,hc,C,hC.trans hs,hh⟩
  change 0 < ρ ∧ _
  by_cases hzero : m=0
  · have hρ : ρ=1 := if_pos hzero
    have hr : 0 < ρ := hρ.symm ▸ (zero_lt_one : (0:ℝ)<1)
    refine ⟨hr,?_⟩
    intro a
    obtain ⟨z,hz,_⟩ := hclock ρ ⟨hr,by rw [hρ]; linarith only [pi_gt_three]⟩ a
    exact ⟨z,hz,fun t _ s => ⟨fun _ => hzero.symm ▸ Nat.zero_le s,hcap t s⟩⟩
  let c := criticalHeight H (m-1)
  have hc : ε < c := predecessor_clearance hm hzero
  have hρ : ρ=min 1 ((c-ε)/2) := if_neg hzero
  have hr : 0 < ρ := hρ.symm ▸ lt_min zero_lt_one (half_pos (sub_pos.mpr hc))
  have hπ : ρ ≤ π := hρ.le.trans ((min_le_left ..).trans (by linarith only [pi_gt_three]))
  have hv₀ : ε+3*ρ/2 < c := by linarith only [hρ.le.trans (min_le_right 1 ((c-ε)/2)),hc]
  obtain ⟨_,⟨v,rfl⟩,hv⟩ := exists_lt_of_lt_csSup (range_nonempty (orbitCircuitDistance H (m-1))) hv₀
  refine ⟨hr,?_⟩
  intro a
  obtain ⟨w,hw,hfit⟩ := hclock ρ ⟨hr,hπ⟩ (a-v)
  refine ⟨v+w,⟨by linarith only [hw.1],by linarith only [hw.2]⟩,fun t ht s => ⟨?_,hcap t s⟩⟩
  rintro ⟨z,hz,C,hC,hh⟩
  by_contra! hs
  have he : HasProjectiveCircuitApproximation N ε (m-1) (unitaryEvolution H.val t) :=
    ⟨z,hz,C,hC.trans (by omega),hh⟩
  have hpre : orbitCircuitDistance H (m-1) t ≤ ε :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mp he
  have hshift := (abs_le.mp (TrajectoryProfiles.scalar_shift_all_distances H hfit (m-1) v)).1
  obtain ⟨L,hL,hlip⟩ := orbitCircuitDistance_lipschitz_spectralWidth H (m-1)
  have hd := hlip.dist_le_mul t (v+w)
  simp only [Real.dist_eq,hL] at hd
  linarith only [hv,hshift,(abs_le.mp hd).1,ht,hpre]

/-- From every origin, including the first robust crossing after identity,
a whole interval attains the same-error all-time maximum. The interval
width uses the spectral bandwidth and the clearance at the prescribed error. -/
theorem gaussian_exact_maximum_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ ε > (0:ℝ), ∃ m, IsRecurrentOrbitCircuitMaximumAt H ε m ∧
        let ρ := maximumResolution H m ε
        0 < ρ ∧ ∀ a : ℝ, ∃ z ∈ Icc a (a+phaseHorizon k ρ), ∀ t : ℝ,
          circuitHamiltonianSpectralWidth H*|t-z| ≤ ρ → ∀ s,
            HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val t) ↔ m ≤ s := by
  filter_upwards [gaussian_all_precision_scalar_windows] with ω hw
  filter_upwards [hw] with k hk
  intro N u H ε hε
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at (by dsimp only [N]; omega : 2 ≤ N) H
    (hasPauliWeightAtMost_pathHamiltonian u _) ε hε
  exact ⟨m,hm,maximum_windows_of_scalar H hm (phaseHorizon k) hk⟩

#print axioms gaussian_exact_maximum_clock
end
end GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
