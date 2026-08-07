import GaloisForLFunctions.HTGeometry.ClockCharacterSigmaMobius

/-!
# Two differential generators of one scalar field differ by a Möbius transformation

If `u` and `w` generate the same differential field over a base of constants and `u` is
hypertranscendental, then the scalar differential order of `w` over `u` and of `u` over `w`
compose to the order of `u` over itself, which is zero.  Both orders therefore vanish, so each
generator is an ordinary rational function of the other, and degree-one Lüroth turns the pair of
mutual rational expressions into a fractional-linear relation with constant coefficients.

No automorphism of an ambient field is involved: the statement is about two elements of one
differential field that generate the same differential subfield.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {C E : Type*} [Field C] [Field E] [CharZero E]
  [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]

omit [CharZero E] [Differential C] [DifferentialAlgebra C E] in
/-- A hypertranscendental element is not a base constant. -/
theorem notMem_bot_of_hypertranscendentalOver {u : E} (hu : HypertranscendentalOver C u) :
    u ∉ (⊥ : IntermediateField C E) := by
  intro hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  have htr : Transcendental C u := by
    simpa using hypertranscendentalOver_jet_transcendental hu 0
  exact htr (hc ▸ isAlgebraic_algebraMap c)

/-- **Mutual differential generation is scalar differential order zero.** -/
theorem hasScalarDifferentialOrder_zero_of_mutual {u w : E}
    (hu : HypertranscendentalOver C u) (hw : HypertranscendentalOver C w)
    (hwmem : w ∈ differentialAdjoin C ({u} : Set E))
    (humem : u ∈ differentialAdjoin C ({w} : Set E)) :
    HasScalarDifferentialOrder C u w 0 := by
  have hu0 : u ∉ (⊥ : IntermediateField C E) := notMem_bot_of_hypertranscendentalOver hu
  have hw0 : w ∉ (⊥ : IntermediateField C E) := notMem_bot_of_hypertranscendentalOver hw
  obtain ⟨r, hr, -⟩ := existsUnique_hasScalarDifferentialOrder hwmem hw0
  obtain ⟨m, hm, -⟩ := existsUnique_hasScalarDifferentialOrder humem hu0
  have hsum : HasScalarDifferentialOrder C u u (m + r) :=
    HasScalarDifferentialOrder.comp hu hr hm
  have huzero : HasScalarDifferentialOrder C u u 0 := by
    rw [hasScalarDifferentialOrder_zero_iff]
    exact ⟨IntermediateField.subset_adjoin C ({u} : Set E) (Set.mem_singleton u), hu0⟩
  have hmr : m + r = 0 := hsum.order_eq huzero
  have hr0 : r = 0 := by omega
  exact hr0 ▸ hr

/-- **Two differential generators of the same scalar field are fractional-linear in each other.** -/
theorem mutual_generator_mobius {u w : E}
    (hu : HypertranscendentalOver C u) (hw : HypertranscendentalOver C w)
    (hwmem : w ∈ differentialAdjoin C ({u} : Set E))
    (humem : u ∈ differentialAdjoin C ({w} : Set E)) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      w * (algebraMap C E c * u + algebraMap C E d)
        = algebraMap C E a * u + algebraMap C E b := by
  have hwu : w ∈ IntermediateField.adjoin C ({u} : Set E) :=
    (hasScalarDifferentialOrder_zero_iff.mp
      (hasScalarDifferentialOrder_zero_of_mutual hu hw hwmem humem)).1
  have huw : u ∈ IntermediateField.adjoin C ({w} : Set E) :=
    (hasScalarDifferentialOrder_zero_iff.mp
      (hasScalarDifferentialOrder_zero_of_mutual hw hu humem hwmem)).1
  have htu : Transcendental C u := by
    simpa using hypertranscendentalOver_jet_transcendental hu 0
  exact adjoin_generator_mobius htu hwu huw

omit [CharZero E] [Differential C] [Differential E] [DifferentialAlgebra C E] in
/-- The denominator of a nondegenerate fractional-linear expression in a transcendental element
never vanishes. -/
theorem mobius_denominator_ne_zero {u : E} (htu : Transcendental C u) {a b c d : C}
    (hdet : a * d - b * c ≠ 0) :
    algebraMap C E c * u + algebraMap C E d ≠ 0 := by
  intro h0
  by_cases hc : c = 0
  · have hd : d = 0 := by
      rw [hc] at h0
      simpa using (algebraMap C E).injective (by simpa using h0)
    exact hdet (by rw [hc, hd]; ring)
  · refine htu ?_
    refine ⟨Polynomial.C c * Polynomial.X + Polynomial.C d, ?_, ?_⟩
    · intro hpoly
      exact hc (by simpa using congrArg (fun p => Polynomial.coeff p 1) hpoly)
    · simpa using h0

omit [CharZero E] [Differential C] [DifferentialAlgebra C E] in
/-- A hypertranscendental element has nonvanishing derivative. -/
theorem deriv_ne_zero_of_hypertranscendentalOver {u : E} (hu : HypertranscendentalOver C u) :
    u′ ≠ 0 := by
  intro h0
  have hjet : Transcendental C (differentialJet 1 u) :=
    hypertranscendentalOver_jet_transcendental hu 1
  rw [show differentialJet 1 u = u′ from by simp [differentialJet_succ], h0] at hjet
  exact hjet isAlgebraic_zero

omit [CharZero E] [Differential C] [Differential E] [DifferentialAlgebra C E] in
/-- A nondegenerate coefficient matrix stays nondegenerate in the extension. -/
theorem mobius_det_ne_zero_algebraMap {a b c d : C} (hdet : a * d - b * c ≠ 0) :
    algebraMap C E a * algebraMap C E d - algebraMap C E b * algebraMap C E c ≠ 0 := by
  have hne : algebraMap C E (a * d - b * c) ≠ 0 := by
    simpa using fun h => hdet ((algebraMap C E).injective (by simpa using h))
  simpa using hne

end

end GaloisForLFunctions.HTGeometry
