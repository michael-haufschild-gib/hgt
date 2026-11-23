import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.CriticalHeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TrajectoryProfiles.ReplayDensity

/-! # A measured family of centers for intervals near the orbit maximum -/
open Filter Set MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator ENNReal
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
open SharpOccupation
noncomputable section

/-- At every translated scalar visit the fine-error cost reaches at least
the coarse-error maximum. The increment circuit bounds the gate deficit
throughout its neighborhood. These centers have the scalar visit density. -/
theorem centers_of_maximum_clearance {N m L : ℕ} (H : selfAdjoint (Register N))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {e η δ T : ℝ}
    (hη : 0 < η) (hsmall : η < sqrt 2) (hpay : 2*η ≤ δ)
    (hm : IsRecurrentOrbitCircuitMaximumAt H (e+δ) m)
    (hsim : ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation N η L (unitaryEvolution H.val t)) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      (∀ a : ℝ, Tendsto (fun b : ℝ => volume.real (S ∩ Icc a b)/(b-a))
        atTop (𝓝 (((2^N:ℕ):ℝ)*(physicalArc η)^(2^N-1:ℕ)))) ∧
      ∀ z ∈ S, (∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val z) → m ≤ j) ∧
        ∀ t : ℝ, |t| ≤ T → ∀ j, HasProjectiveCircuitApproximation N e j
          (unitaryEvolution H.val (z+t)) → m ≤ j+L := by
  obtain ⟨v,hv⟩ := required_at_some_date hm
  obtain ⟨hS,hfreq⟩ := TrajectoryProfiles.translated_scalar_fraction H hi hη hsmall v
  refine ⟨_,hS,hfreq,?_⟩
  intro z hz
  have hback := (show HasProjectiveCircuitApproximation N η 0 (unitaryEvolution H.val (z-v)) from hz).neg_time H
  have need (j : ℕ) (hfit : HasProjectiveCircuitApproximation N (e+η) j (unitaryEvolution H.val z)) : m ≤ j := by
    have hh := affordable_add_time H hfit hback
    rw [show z+ -(z-v)=v by ring,Nat.add_zero] at hh
    obtain ⟨w,hw,C,hC,he⟩ := hh
    exact hv _ ⟨w,hw,C,hC,he.trans (by linarith only [hpay])⟩
  constructor
  · rintro j ⟨w,hw,C,hC,he⟩
    exact need _ ⟨w,hw,C,hC,he.trans (le_add_of_nonneg_right hη.le)⟩
  · intro t ht j hfit
    have hh := affordable_add_time H hfit (hsim (-t) (by rwa [abs_neg]))
    rw [show z+t+ -t=z by ring] at hh
    exact need _ hh

#print axioms centers_of_maximum_clearance
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
