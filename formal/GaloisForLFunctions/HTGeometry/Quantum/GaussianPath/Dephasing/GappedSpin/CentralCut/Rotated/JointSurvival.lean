import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.Frame
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.IncrementMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.BoxTransfer

/-! # First-excursion tails with every physical Pauli coupling strong -/

open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes AccuracyScales.TenthPlateau
noncomputable section

/-- In a fixed laboratory frame all coefficients can have magnitude
at least 1/100 while both the original robust crossing and every
half-budget first wait exceed T. The Gaussian cost is uniform in K. -/
theorem all_strong_first_excursion :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∀ T ≥ (1:ℝ), exp (-C*(K:ℝ)^2) ≤ T^7*μ.real {x |
        x ∈ allCoordStrongEvent n (1/100) ∧ T < crossingOrigin n P (9/80) x ∧
        ∀ s ≤ P/2, T < crossingWait n P s x} := by
  obtain ⟨C,hC,hbox⟩ := gaussian_central_increment_box
  refine ⟨C,hC,?_⟩
  filter_upwards [hbox,transfer_increment_sector] with k hb hpass
  intro n K P μ T hT
  obtain ⟨B,E,hB,hE,hfloor,hinc⟩ := hb T hT
  obtain ⟨F,hF,hm,hrot⟩ := rotated_sector hE
  have hQ : MeasurableSet (allCoordStrongEvent n (1/100)) := by
    simp only [allCoordStrongEvent,setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i).abs
  rw [←hm] at hfloor
  apply hfloor.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hT) _)
  apply hpass F _ hF hQ T (zero_lt_one.trans_le hT) B hB
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hrot x hx
  obtain ⟨hd,ho,hcheap⟩ := hinc y hy
  exact ⟨rotated_coordinates_strong hd ho,fun t ht => rotated_increment_fit (hcheap t ht)⟩

#print axioms all_strong_first_excursion
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
