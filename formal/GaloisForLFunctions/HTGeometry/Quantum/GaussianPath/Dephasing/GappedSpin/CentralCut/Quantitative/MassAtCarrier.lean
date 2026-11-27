import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.TransverseWidths

/-! # Cost of the bulk and transverse widths of a gapped-spin box -/
open Set MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section

/-- The uniform bulk radius appears only to the number of physical
coordinates. Fourteen shrinking entries cost at most T⁷. -/
theorem gapped_box_mass {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    (S : Finset ι) (hS : S.card ≤ 14) (a : ι→ℝ) (hz : ∀ i∈S, a i=0)
    {H r : ℝ} (hH : 0 ≤ H) (ha : ∀ i, |a i| ≤ 2+(if i=i₀ then H else 0))
    (hr : 0 < r) (hr₁ : r ≤ 1) (T : ℝ) (hT : 1 ≤ T) :
    let M := Fintype.card ι
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    ∃ E : Set (ι→ℝ), MeasurableSet E ∧
      (2*(sqrt (2*π))⁻¹*r)^M * exp (-(9*(M:ℝ)+(H+3)^2)/2) ≤
        ((1800:ℝ)^14*T^7)*μ.real E ∧
      ∀ x∈E, (∀ i, |x i-a i| ≤ r) ∧ ∀ i∈S, |x i| ≤ 1/(1800*sqrt T) := by
  intro M μ
  obtain ⟨E,hE,hp,hw⟩ := gapped_box_relative_widths i₀ S hS a hz hH ha hr hr₁ T hT
  refine ⟨E,hE,hp,?_⟩
  intro x hx
  obtain ⟨hbox,hcut⟩ := hw x hx
  exact ⟨hbox,fun i hi => (hcut i hi).trans (div_le_div_of_nonneg_right hr₁ (by positivity))⟩

#print axioms gapped_box_mass
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
