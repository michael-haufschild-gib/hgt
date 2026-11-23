import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PrefixModes

/-! # Lower tails for balanced spectral frequencies at prescribed confidence -/
open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Frequency floor when both polynomial sublevel events are given mass η. -/
def confidenceMargin (k count : ℕ) (T η : ℝ) : ℝ :=
  let D := 2^(k+3)
  let L := D-2
  let B := prefixDetectorDegree k
  ((η/(1+2*(B:ℝ)))^B/(1+|pathResponseCap (k+3) L T*(D:ℝ)|))*
    (η/(1+(modeStripPrice D L count:ℝ)))^L

/-- Some retained nonzero balanced combination of sorted energies has
absolute detuning strictly below the given threshold. -/
def smallBalancedMode (N : ℕ) (S : Finset (Fin (2^N) → ℤ)) (δ : ℝ) : Set (Coordinates N → ℝ) :=
  {x | ∃ m ∈ S, m ≠ 0 ∧ ∑ j, m j = 0 ∧
    |∑ j, (m j:ℝ)*sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x j| < δ}

private theorem ratio_price {η c : ℝ} (hη : 0<η) (hη' : η≤1) (hc : 0≤c) :
    0<η/(1+c) ∧ η/(1+c)≤1 ∧ c*(η/(1+c))≤η := by
  have hd : 0<1+c := by positivity
  refine ⟨div_pos hη hd,(div_le_one hd).mpr (hη'.trans (le_add_of_nonneg_right hc)),?_⟩
  rw [←mul_div_assoc,div_le_iff₀ hd]
  linarith only [hη]

/-- Outside the prescribed box tail, failure costs at most 2η. The same
detector controls all modes, so the size of the mode set enters only in
the explicit frequency margin. -/
theorem gaussian_confidence_margin (k : ℕ) (S : Finset (Fin (2^(k+3)) → ℤ))
    {T η : ℝ} (hT : 0≤T) (hη : 0<η) (hη' : η≤1) :
    let N := k+3
    let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
    μ (smallBalancedMode N S (confidenceMargin k S.card T η)) ≤
      μ {x | ¬∀ i, |x i| ≤ T} + ENNReal.ofReal η + ENNReal.ofReal η := by
  intro N μ
  let D := 2^N
  let L := D-2
  let B := prefixDetectorDegree k
  obtain ⟨rows,hw,_,_,htail⟩ := gaussian_path_nonvanishing_detector_lower_tail k
  let δ := η/(1+2*(B:ℝ))
  let r := η/(1+(modeStripPrice D L S.card:ℝ))
  let C := pathResponseCap N L T
  let a := δ^B/(1+|C*(D:ℝ)|)
  have hd := ratio_price hη hη' (by positivity : 0≤2*(B:ℝ))
  have hr := ratio_price hη hη' (Nat.cast_nonneg (modeStripPrice D L S.card))
  have ha : 0<a := div_pos (pow_pos hd.1 _) (by positivity)
  let K : Set (Coordinates N → ℝ) := {x | ¬∀ i, |x i| ≤ T}
  let J : Set (Coordinates N → ℝ) := {x | ‖eval₂Hom GaussianInt.toComplex
    (fun i => (x i : ℂ)) (pathDetector N L rows)‖ < δ^B}
  let W := finiteWitnesses N L S rows a r
  have hJ : μ J ≤ ENNReal.ofReal η :=
    (htail δ hd.1 hd.2.1).trans (ENNReal.ofReal_le_ofReal hd.2.2)
  have hW : μ W ≤ ENNReal.ofReal η :=
    (gaussian_finite_witnesses N L S rows hw ha hr.1 hr.2.1).trans (ENNReal.ofReal_le_ofReal hr.2.2)
  have hsub : smallBalancedMode N S (confidenceMargin k S.card T η) ⊆ (K ∪ J) ∪ W := by
    rintro x ⟨m,hm,hn,hbal,hsmall⟩
    by_cases hx : ∀ i, |x i| ≤ T
    · by_cases hj : x ∈ J
      · exact Or.inl (Or.inr hj)
      · have hdet := detect_at_sample N L rows hw x (pow_pos hd.1 B) (le_of_not_gt hj)
        have hpack := modes_at_box_scale N L rows hw x hT hx hdet
        obtain ⟨hs,hresp⟩ := sorted_response_of_packet N rows x C _ hpack
        obtain ⟨i,w,hi,hh⟩ := hresp m hn hbal
        refine Or.inr (mem_iUnion₂.mpr ⟨m,hm,mem_iUnion₂.mpr ⟨i,Finset.mem_univ _,hs,?_,?_⟩⟩)
        · simpa only [sortedMode_nil] using hsmall
        · simpa only [hi,Option.getD_some] using response_amplitude_le (pow_le_one₀ hd.1.le hd.2.1) hh
    · exact Or.inl (Or.inl hx)
  exact (measure_mono hsub).trans ((measure_union_le ..).trans
    (add_le_add ((measure_union_le ..).trans (add_le_add_left hJ _)) hW))

#print axioms gaussian_confidence_margin
end
end GaloisForLFunctions.HTGeometry.SpectralJets
