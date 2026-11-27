import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.JointMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.Frame

/-! # A Gaussian first-excursion sector on the original disorder space -/
open Set Filter Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes AccuracyScales.TenthPlateau
noncomputable section

/-- The common set carries both the all-time budget and the smaller
increment budget after rotation to the physical Pauli coordinates. -/
theorem physical_joint_sector :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ T ≥ (1:ℝ), ∃ B : ℕ, ∃ E : Set PathPauliDisorder, 2*B ≤ P ∧ MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*pathPauliDisorderLaw.real E ∧ ∀ ω ∈ E,
          let u := pathPauliDisorderShell ω n
          let x := fun i => u (pathCoeffEquiv n i)
          x ∈ allCoordStrongEvent n (1/100) ∧
          (∀ t : ℝ, HasProjectiveCircuitApproximation K (1/10) (2^K*(2*K+1))
            (unitaryEvolution (pathHamiltonian u) t)) ∧
          ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation K (1/100) B
            (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨C,hC,hbox⟩ := gaussian_joint_central_box
  refine ⟨C,hC,?_⟩
  filter_upwards [hbox] with k hraw
  intro n K P T hT
  obtain ⟨B,A,hB,hA,hm,hw⟩ := hraw T hT
  obtain ⟨F,hF,hprob,hrot⟩ := rotated_sector hA
  let Y := fun (ω : PathPauliDisorder) l => pathPauliDisorderShell ω n l
  have hY := measurePreserving_pathDisorder_labels n
  have hmass : pathPauliDisorderLaw.real (Y ⁻¹' F) =
      (Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)).real A :=
    (congrArg ENNReal.toReal (hY.measure_preimage hF.nullMeasurableSet)).trans hprob
  refine ⟨B,Y ⁻¹' F,hB,hF.preimage hY.measurable,by rw [hmass]; exact hm,?_⟩
  intro ω he u x
  obtain ⟨y,hy,hmap⟩ := hrot (Y ω) he
  change pythShellMap n y=u.ofLp at hmap
  obtain ⟨hd,ho,hglobal,hinc⟩ := hw y hy
  have hstrong := rotated_coordinates_strong hd ho
  rw [hmap] at hstrong
  refine ⟨hstrong,fun t => ?_,fun t ht => ?_⟩
  · have h := rotated_increment_fit (hglobal t); rwa [hmap] at h
  · have h := rotated_increment_fit (hinc t ht); rwa [hmap] at h

#print axioms physical_joint_sector
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
