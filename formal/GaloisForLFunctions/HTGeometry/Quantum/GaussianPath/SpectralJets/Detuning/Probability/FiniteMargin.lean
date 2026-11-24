import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.OrderPrice

/-! # Lower tails for balanced spectral frequencies at prescribed confidence -/
open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Frequency floor when both polynomial sublevel events are given mass η. -/
def confidenceMargin (k count : ℕ) (T η : ℝ) : ℝ :=
  let D : ℕ := 2^(k+3)
  let L : ℕ := D-2
  let B := prefixDetectorDegree k
  ((η/(1+2*(B:ℝ)))^B/(1+|pathResponseCap (k+3) L T*(D:ℝ)|))*
    (η/(1+(modeStripPrice D L count:ℝ)))^L

/-- Some retained nonzero balanced combination of sorted energies has
absolute detuning strictly below the given threshold. -/
def smallBalancedMode (N : ℕ) (S : Finset (Fin (2^N) → ℤ)) (δ : ℝ) : Set (Coordinates N → ℝ) :=
  {x | ∃ m ∈ S, m ≠ 0 ∧ ∑ j, m j = 0 ∧
    |∑ j, (m j:ℝ)*sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x j| < δ}

/-- Within the prescribed coupling box, failure costs at most 2η. The same
detector controls all modes, so the size of the mode set enters only in
the explicit frequency margin. -/
theorem gaussian_box_margin (k : ℕ) (S : Finset (Fin (2^(k+3)) → ℤ))
    {T η : ℝ} (hT : 0≤T) (hη : 0<η) (hη' : η≤1) :
    let N := k+3
    let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
    μ ({x | ∀ i, |x i| ≤ T} ∩ smallBalancedMode N S (confidenceMargin k S.card T η)) ≤
      ENNReal.ofReal η + ENNReal.ofReal η := by
  obtain ⟨rows,hw,hn⟩ := exists_pathDetector_ne_zero k
  exact box_margin_of_detector (k+3) (2^(k+3)-2) rows hw hn S hT hη hη'

/-- Removing the box adds its Gaussian tail to the two sublevel bounds. -/
theorem gaussian_confidence_margin (k : ℕ) (S : Finset (Fin (2^(k+3)) → ℤ))
    {T η : ℝ} (hT : 0≤T) (hη : 0<η) (hη' : η≤1) :
    let N := k+3
    let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
    μ (smallBalancedMode N S (confidenceMargin k S.card T η)) ≤
      μ {x | ¬∀ i, |x i| ≤ T} + ENNReal.ofReal η + ENNReal.ofReal η := by
  intro N μ
  let K : Set (Coordinates N → ℝ) := {x | ∀ i, |x i|≤T}
  let A := smallBalancedMode N S (confidenceMargin k S.card T η)
  have hs : A ⊆ Kᶜ ∪ (K ∩ A) := fun x hx => (em (x∈K)).elim
    (fun h => Or.inr ⟨h,hx⟩) Or.inl
  rw [add_assoc]
  exact (measure_mono hs).trans ((measure_union_le ..).trans
    (add_le_add (le_refl (μ Kᶜ)) (gaussian_box_margin k S hT hη hη')))

#print axioms gaussian_confidence_margin
end
end GaloisForLFunctions.HTGeometry.SpectralJets
