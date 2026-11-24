import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.GapClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Classes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PhaseCenters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.GaussianForest
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.FirstVisit

/-! # Precision needed before a circuit can fit in any basis -/

open Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
open Winding.CollisionRank
noncomputable section

/-- Each accurate assignment to m centers forces D−m independent gaps
to return. The bound holds simultaneously over all assignments and times. -/
theorem gaussian_center_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ), ∀ n m : ℕ, 0<n → m+(n+1) ≤ 2^N → ∀ lo < (n:ℝ),
        ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ≥ a, ∀ f : (Fin N→Bool) → ℂ, (Finset.univ.image f).card ≤ m →
          (∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i t-f i‖ < 2*ε) → lo < log t/log (1/ε) := by
  classical
  filter_upwards [gaussian_forest_ratios,gaussian_path_all_prefixes_maximally_projective] with ω hF hE k
  intro N H a ha n m hn hsize lo hlo
  let I := Fin N → Bool
  let E := H.2.isHermitian.eigenvalues
  let G (l r : Fin (n+1) → I) := fun i => E (l i)-E (r i)
  let valid (l r : Fin (n+1) → I) := Function.Injective l ∧ ∀ i j, r i≠l j
  have bound (l r : Fin (n+1) → I) : ∀ᶠ ε in 𝓝[>] (0:ℝ), valid l r →
      ∀ t ≥ a, ContinuousReturn (G l r) ε t → lo < log t/log (1/ε) := by
    by_cases h : valid l r
    · have hg : G l r 0≠0 := fun he => h.2 0 0 ((hE k).injective (sub_eq_zero.mp he)).symm
      have hy := hF k n l r hn h.1 h.2
      have hh := optimal_gap_window hn (G l r) hg hy ha zero_lt_one hlo (lt_add_one (n:ℝ))
      filter_upwards [hh] with ε hε _
      simpa only [one_mul] using hε.1
    · exact .of_forall fun _ hv => (h hv).elim
  filter_upwards [eventually_all.mpr (fun l => eventually_all.mpr (bound l)),self_mem_nhdsWithin]
    with ε hall (he : 0<ε)
  intro t hat f hcard hnear
  have hD : Fintype.card I=2^N := by simp [I]
  obtain ⟨l,r,hi,hd,hf⟩ := extract_class_forest f (n+1) (by rw [hD]; omega)
  apply hall l r ⟨hi,hd⟩ t hat
  intro j
  apply gap_of_shared_center E (l j) (r j) t (hnear (l j))
  rw [hf j]
  exact hnear (r j)

/-- A circuit with s gates has at most 4ˢ spectral centers, so its
first fit even in a free basis has lower precision exponent D−4ˢ−1. -/
theorem gaussian_free_basis_gate_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ), ∀ n s : ℕ, 0<n → 4^s+(n+1) ≤ 2^N → ∀ lo < (n:ℝ),
        ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ≥ a, t ∈ SpectralApproximation.affordableDates H s ε →
          lo < log t/log (1/ε) := by
  filter_upwards [gaussian_center_floor] with ω h k
  intro N H a ha n s hn hsize lo hlo
  filter_upwards [h k a ha n (4^s) hn hsize lo hlo,self_mem_nhdsWithin] with ε hh (he : 0<ε)
  rintro t hat ⟨V,z,_,C,hC,hfit⟩
  obtain ⟨f,hcard,hnear⟩ := centers_of_fit H t V C z he hfit
  exact hh t hat f (hcard.trans (Nat.pow_le_pow_right (by decide) hC)) hnear

#print axioms gaussian_free_basis_gate_floor
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
