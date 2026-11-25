import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.Geometry

/-! # The compact set of admissible ordered prime spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Set Topology _root_.RHTower GaloisForLFunctions.HTGeometry

/-- Sorted energy vectors, including coincidences and both edges of the band. -/
def orderedBand (c d : ℝ) (k : ℕ) : Set (Fin k → ℝ) :=
  {v | Monotone v ∧ ∀ i, v i ∈ Icc c d}

theorem orderedBand_compact (c d : ℝ) (k : ℕ) : IsCompact (orderedBand c d k) := by
  let B : Set (Fin k → ℝ) := univ.pi fun _ => Icc c d
  have he : sortedTuple '' B = orderedBand c d k := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨monotone_sortedTuple w,fun i => hw (Tuple.sort w i) (mem_univ _)⟩
    · intro hv
      refine ⟨v,fun i _ => hv.2 i,?_⟩
      unfold sortedTuple
      rw [(Tuple.sort_eq_refl_iff_monotone (f := v)).mpr hv.1]
      rfl
  rw [← he]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (continuous_sort k)

theorem constant_mem {c d x : ℝ} (hx : x ∈ Icc c d) (k : ℕ) :
    (fun _ : Fin k => x) ∈ orderedBand c d k := ⟨monotone_const,fun _ => hx⟩

theorem spectrum_mem_band {c d : ℝ} (h : Ioi (0:ℝ)) {k : ℕ} (R : BreadthSubset k ↥(added c d h)) :
    spectrum h R ∈ orderedBand c d k :=
  ⟨monotone_sortedTuple _, fun i => ⟨(Endpoints.spectrum_mem h R i).1.le,(Endpoints.spectrum_mem h R i).2⟩⟩

/-- Largest observable value on the admissible band. -/
def peak {k : ℕ} (c d : ℝ) (F : (Fin k → ℝ) → ℝ) := sSup (F '' orderedBand c d k)

theorem peak_attained {c d : ℝ} (hcd : c ≤ d) {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    (hF : ContinuousOn F (orderedBand c d k)) :
    ∃ v ∈ orderedBand c d k, F v = peak c d F ∧ ∀ w ∈ orderedBand c d k, F w ≤ F v := by
  obtain ⟨v,hv,hmax⟩ := (orderedBand_compact c d k).exists_isMaxOn
    ⟨_,constant_mem (x := c) ⟨le_rfl,hcd⟩ k⟩ hF
  have hg : IsGreatest (F '' orderedBand c d k) (F v) := ⟨mem_image_of_mem _ hv,by
    rintro _ ⟨w,hw,rfl⟩
    exact hmax hw⟩
  exact ⟨v,hv,hg.csSup_eq.symm,fun _ hw => hmax hw⟩

#print axioms orderedBand_compact
#print axioms spectrum_mem_band
#print axioms peak_attained

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
