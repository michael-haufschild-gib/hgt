import GaloisForLFunctions.RHTower.FullProjectiveChoiFirstReturnLaw

open Set MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Complete padded-circuit specialization. Reindexing loses no word and
pays the exact dictionary cardinality `|gate|^(s+1)`. -/
theorem exists_fullProjectiveChoiTensor_paddedCircuitFirstReturnDichotomy
    {n : ℕ} {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {g eta epsw : ℝ} (hg : 0 < g) (heta : 0 < eta) (hepsw : 0 < epsw)
    (N : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (hsmall : 2 * zeroAnchoredChoiAngularRadius (n + 1) epsw ≤ Real.pi) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : PaddedCircuitWord gate s →
          EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
        (identity : PaddedCircuitWord gate s),
        target identity = projectiveChoiDensityFlow
          (projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)) 0 →
        ∀ epsn T : ℝ, 0 ≤ epsn → epsn < epsw → 0 < T →
          epsw / fullProjectiveDensitySpeed g y ≤ T →
          2 * (epsw / fullProjectiveDensitySpeed g y) +
                (epsw - epsn) / fullProjectiveDensitySpeed g y ≤
              fullProjectiveTensorPhysicalOccupationBudget n N
                (Fintype.card gate ^ (s + 1)) g eta epsw T C ∨
            ¬ ∃ t ∈ Set.Icc
                (epsw / fullProjectiveDensitySpeed g y +
                  (epsw - epsn) / fullProjectiveDensitySpeed g y) T,
              ∃ w, dist
                (projectiveChoiDensityFlow
                  (projectiveFrequencyEnergy
                    (clockScaledFullProjectiveFrequency g y)) t)
                (target w) ≤ epsn := by
  let word := PaddedCircuitWord gate s
  let e : word ≃ Fin (Fintype.card word) := Fintype.equivFin word
  obtain ⟨C, hC, hfin⟩ :=
    exists_fullProjectiveChoiTensor_firstReturnDichotomy
      hy hg heta hepsw N (Fintype.card word) hsmall
  refine ⟨C, hC, ?_⟩
  intro target identity hidentity epsn T hepsn hgap hT honset
  let targetFin : Fin (Fintype.card word) →
      EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)) :=
    fun i => target (e.symm i)
  have htarget0 : targetFin (e identity) =
      projectiveChoiDensityFlow
        (projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)) 0 := by
    simpa only [targetFin, e, Equiv.symm_apply_apply] using hidentity
  have hresult := hfin targetFin (e identity) htarget0 epsn T hepsn hgap hT honset
  rcases hresult with hbudget | hreturn
  · left
    simpa only [word, card_paddedCircuitWord] using hbudget
  · right
    rintro ⟨t, ht, w, hw⟩
    apply hreturn
    refine ⟨t, ht, e w, ?_⟩
    simpa only [targetFin, Equiv.symm_apply_apply] using hw

end RHTower
