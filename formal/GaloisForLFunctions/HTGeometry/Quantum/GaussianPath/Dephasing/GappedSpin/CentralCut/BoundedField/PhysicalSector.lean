import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.BoundedField.GaussianSector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.Frame

/-! # A bounded strong-coupling sector in the laboratory frame -/
open Set Filter Real MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes AccuracyScales.TenthPlateau
noncomputable section

private theorem rotated_upper {n : ℕ} (x : PathLabel n→ℝ) (hx : ∀ l, |x l|≤3)
    (l : PathLabel n) : |pythShellMap n x l| ≤ 27 := by
  have hR (i j : Fin 3) : |pythRotMat i j| ≤ 1 := by
    fin_cases i <;> fin_cases j <;> norm_num [pythRotMat]
  have hs (f : Fin 3→ℝ) (c : ℝ) (h : ∀ i, |f i|≤c) : |∑ i, f i|≤3*c := by
    rw [Fin.sum_univ_three]
    linarith only [abs_add_le (f 0+f 1) (f 2),abs_add_le (f 0) (f 1),h 0,h 1,h 2]
  rcases l with ⟨i,a⟩|⟨e,a,b⟩
  · apply (hs _ 3 ?_).trans (by norm_num)
    intro j
    rw [abs_mul]
    exact (mul_le_mul (hR a j) (hx _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  · apply (hs _ (3*3) ?_).trans_eq (by norm_num)
    intro j
    apply hs _ 3
    intro k
    rw [abs_mul,abs_mul]
    have h := mul_le_one₀ (hR a j) (abs_nonneg _) (hR b k)
    exact (mul_le_mul h (hx _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- All physical coordinates have absolute value between 1/100 and 27.
The same draw gives the linear-in-dimension cap at every date and the
smaller budget throughout its prescribed increment window. -/
theorem bounded_physical_sector :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ T ≥ (1:ℝ), ∃ B : ℕ, ∃ E : Set PathPauliDisorder, 2*B ≤ P ∧ MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*pathPauliDisorderLaw.real E ∧ ∀ ω ∈ E,
          let u := pathPauliDisorderShell ω n
          let x := fun i => u (pathCoeffEquiv n i)
          x ∈ allCoordStrongEvent n (1/100) ∧ (∀ i, |x i|≤27) ∧
          (∀ t : ℝ, HasProjectiveCircuitApproximation K (1/10) (2^K*3)
            (unitaryEvolution (pathHamiltonian u) t)) ∧
          ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation K (1/100) B
            (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨C,hC,hbox⟩ := bounded_gaussian_sector
  refine ⟨C,hC,?_⟩
  filter_upwards [hbox] with k hk
  intro n K P T hT
  obtain ⟨B,A,hB,hA,hm,_,hw⟩ := hk T hT
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
  obtain ⟨hbound,hd,ho,hglobal,hinc⟩ := hw y hy
  have hstrong := rotated_coordinates_strong hd ho
  rw [hmap] at hstrong
  refine ⟨hstrong,fun i => ?_,fun t => ?_,fun t ht => ?_⟩
  · have h := rotated_upper y hbound (pathCoeffEquiv n i)
    rwa [hmap] at h
  · have h := rotated_increment_fit (hglobal t); rwa [hmap] at h
  · have h := rotated_increment_fit (hinc t ht); rwa [hmap] at h

#print axioms bounded_physical_sector
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
