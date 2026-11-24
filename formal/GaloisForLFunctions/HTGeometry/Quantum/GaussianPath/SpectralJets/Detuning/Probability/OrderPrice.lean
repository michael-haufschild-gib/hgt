import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PrefixModes

/-! # Gaussian detuning on a coupling box at a specified derivative order -/
open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- The degree cost is shared by all frequencies. The word length sets the
additional cost of ruling out the finite list of small frequencies. -/
def floorAtOrder (N L count : ℕ) (T η : ℝ) : ℝ :=
  let D := 2^N
  let B := D*(2*(1+2*L*D))
  ((η/(1+2*(B:ℝ)))^B/(1+|pathResponseCap N L T*(D:ℝ)|))*
    (η/(1+(modeStripPrice D L count:ℝ)))^L

private theorem ratio_price {η c : ℝ} (hη : 0<η) (hη' : η≤1) (hc : 0≤c) :
    0<η/(1+c) ∧ η/(1+c)≤1 ∧ c*(η/(1+c))≤η := by
  have hd : 0<1+c := by positivity
  refine ⟨div_pos hη hd,(div_le_one hd).mpr (hη'.trans (le_add_of_nonneg_right hc)),?_⟩
  rw [←mul_div_assoc,div_le_iff₀ hd]
  linarith only [hη]

/-- On the part of the box where the detector has a prescribed floor, the
exceptional mass costs only the small-frequency estimate of order L. -/
theorem box_detuning_above_detector (N L : ℕ) (rows : Fin (2^N)→Option (List (Coordinates N)))
    (hw : ∀ i w, w∈rows i → w.length≤L) (S : Finset (Fin (2^N)→ℤ))
    {T κ r : ℝ} (hT : 0≤T) (hκ : 0<κ) (hκ' : κ≤1) (hr : 0<r) (hr' : r≤1) :
    let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
    let a := κ/(1+|pathResponseCap N L T*(2^N:ℕ)|)
    μ {x | (∀ i, |x i|≤T) ∧ κ≤‖eval₂Hom GaussianInt.toComplex (fun i => (x i:ℂ))
      (pathDetector N L rows)‖ ∧ ∃ m∈S, m≠0 ∧ ∑ j, m j=0 ∧
      |∑ j, (m j:ℝ)*sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x j|<a*r^L} ≤
      ENNReal.ofReal ((modeStripPrice (2^N) L S.card:ℝ)*r) := by
  intro μ a
  have ha : 0<a := div_pos hκ (by positivity)
  apply (measure_mono ?_).trans (gaussian_finite_witnesses N L S rows hw ha hr hr')
  rintro x ⟨hx,hdet,m,hm,hn,hbal,hsmall⟩
  have hpack := modes_at_box_scale N L rows hw x hT hx (detect_at_sample N L rows hw x hκ hdet)
  obtain ⟨hs,hresp⟩ := sorted_response_of_packet N rows x _ _ hpack
  obtain ⟨i,w,hi,hh⟩ := hresp m hn hbal
  refine mem_iUnion₂.mpr ⟨m,hm,mem_iUnion₂.mpr ⟨i,Finset.mem_univ _,hs,?_,?_⟩⟩
  · simpa only [sortedMode_nil] using hsmall
  · simpa only [hi,Option.getD_some] using response_amplitude_le hκ' hh

/-- Any nonzero integral detector supplies a simultaneous detuning floor,
with Gaussian failure mass at most twice the confidence parameter. -/
theorem box_margin_of_detector (N L : ℕ) (rows : Fin (2^N)→Option (List (Coordinates N)))
    (hw : ∀ i w, w∈rows i → w.length≤L) (hn : map GaussianInt.toComplex (pathDetector N L rows)≠0)
    (S : Finset (Fin (2^N)→ℤ)) {T η : ℝ} (hT : 0≤T) (hη : 0<η) (hη' : η≤1) :
    let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
    μ ({x | ∀ i, |x i|≤T} ∩ ({x | ∃ m ∈ S, m ≠ 0 ∧ ∑ j, m j = 0 ∧
       |∑ j, (m j:ℝ)*sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x j| < floorAtOrder N L S.card T η} : Set (Coordinates N → ℝ))) ≤ ENNReal.ofReal η+ENNReal.ofReal η := by
  intro μ
  let D := 2^N
  let B := D*(2*(1+2*L*D))
  let δ := η/(1+2*(B:ℝ))
  let r := η/(1+(modeStripPrice D L S.card:ℝ))
  let C := pathResponseCap N L T
  let a := δ^B/(1+|C*(D:ℝ)|)
  have hd := ratio_price hη hη' (by positivity : 0≤2*(B:ℝ))
  have hr := ratio_price hη hη' (Nat.cast_nonneg (modeStripPrice D L S.card))
  let J : Set (Coordinates N → ℝ) := {x | ‖eval₂Hom GaussianInt.toComplex
    (fun i => (x i : ℂ)) (pathDetector N L rows)‖ < δ^B}
  have hJ : μ J ≤ ENNReal.ofReal η :=
    (pathDetector_lower_tail_of_nonzero N L rows hw hn hd.1 hd.2.1).trans (ENNReal.ofReal_le_ofReal hd.2.2)
  let E := {x : Coordinates N → ℝ | (∀ i, |x i|≤T) ∧ δ^B≤‖eval₂Hom GaussianInt.toComplex
    (fun i => (x i:ℂ)) (pathDetector N L rows)‖ ∧ ∃ m∈S, m≠0 ∧ ∑ j, m j=0 ∧
    |∑ j, (m j:ℝ)*sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x j|<a*r^L}
  have hE : μ E ≤ ENNReal.ofReal η :=
    (box_detuning_above_detector N L rows hw S hT (pow_pos hd.1 B)
      (pow_le_one₀ hd.1.le hd.2.1) hr.1 hr.2.1).trans (ENNReal.ofReal_le_ofReal hr.2.2)
  apply (measure_mono ?_).trans ((measure_union_le J E).trans (add_le_add hJ hE))
  rintro x ⟨hx,hm⟩
  by_cases hj : x∈J
  · exact Or.inl hj
  · exact Or.inr ⟨hx,le_of_not_gt hj,hm⟩

end
end GaloisForLFunctions.HTGeometry.SpectralJets
