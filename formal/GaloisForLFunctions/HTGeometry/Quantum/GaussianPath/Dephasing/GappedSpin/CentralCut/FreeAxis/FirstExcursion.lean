import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.DisjointSectors
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.FirstCrossingWindows

/-! # First crossings and return windows in the positive bounded-coupling sector -/
open Set Filter Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
open PrescribedTimes SharpOccupation WeakBonds.NearDiagonal
open private distance_at_positive_crossing from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.FirstCrossingWindows
noncomputable section

/-- With sixth-power survival probability, the whole window around the
original crossing excludes half-budget fits. The actual same-error
maximum is bounded by three times Hilbert dimension on this same draw. -/
theorem positive_first_excursions :
    ∃ C > (0:ℝ), ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ T ≥ (1:ℝ), ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^6*pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let x := fun i => u (pathCoeffEquiv n i)
          let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
          let σ := crossingOrigin n P (9/80) x
          let F := nearbyVisit H (P/2) T
          (∀ i, x i∈Icc (1/20:ℝ) 4) ∧ T < σ ∧ (∀ s ≤ P/2, T < crossingWait n P s x) ∧
          σ ∉ F ∧ (∃ m : ℕ, P < m ∧ m ≤ 3*2^K ∧ m/(384*(K+1)) ≤ P/2 ∧
            IsRecurrentOrbitCircuitMaximumAt H (1/10) m) ∧
          ∀ a : ℝ→ℝ, ∀ᶠ L : ℝ in atTop, volume.real (F ∩ Icc (a L) (a L+L))/L < b^(2^K:ℕ) := by
  obtain ⟨C,hC,hbox⟩ := positive_sixth_power_sector
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
  obtain ⟨m,hmin,hmax,hrec,_⟩ := hm u (hspec k) 3 (by decide) hglobal
  have hrel : m/(384*(K+1)) ≤ P/2 := by
    let s := m/(384*(K+1))
    have hs : (s*2*(64*(K+1)))*3 ≤ 2^K*3 := calc
      _ = s*(384*(K+1)) := by ring
      _ ≤ m := Nat.div_mul_le_self ..
      _ ≤ _ := hmax.trans_eq (Nat.mul_comm ..)
    have hp : s*2 ≤ P := (Nat.le_div_iff_mul_le (by positivity : 0<64*(K+1))).mpr
      (Nat.le_of_mul_le_mul_right hs (by decide : 0<3))
    exact (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hp
  refine ⟨fun i => hstrong (pathCoeffEquiv n i),ho,hr,?_,⟨m,hmin,hmax,hrel,hrec⟩,hω T B hB hinc⟩
  intro hbad
  have hfit := nearbyVisit_subset H hB hinc hbad
  have hlo := distance_at_positive_crossing u (hT₀.trans ho)
  have hhi : orbitCircuitDistance H P σ ≤ 11/100 :=
    (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hfit
  change 9/80 ≤ orbitCircuitDistance H P σ at hlo
  linarith only [hlo,hhi]

#print axioms positive_first_excursions
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
