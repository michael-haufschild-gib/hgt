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
/-- **The coefficient matrix of a fractional-linear relation at a transcendental element is
determined up to a scalar.**  Two nondegenerate coefficient quadruples producing the same value are
proportional, so the transition is a well-defined element of the projective linear group. -/
theorem mobius_coefficients_unique {u w : E} (htu : Transcendental C u)
    {a b c d a' b' c' d' : C}
    (hdet : a * d - b * c ≠ 0) (hdet' : a' * d' - b' * c' ≠ 0)
    (h : w * (algebraMap C E c * u + algebraMap C E d)
      = algebraMap C E a * u + algebraMap C E b)
    (h' : w * (algebraMap C E c' * u + algebraMap C E d')
      = algebraMap C E a' * u + algebraMap C E b') :
    ∃ t : C, t ≠ 0 ∧ a' = t * a ∧ b' = t * b ∧ c' = t * c ∧ d' = t * d := by
  classical
  have hpoly : algebraMap C E (a * c' - a' * c) * u ^ 2
      + algebraMap C E (a * d' + b * c' - a' * d - b' * c) * u
      + algebraMap C E (b * d' - b' * d) = 0 := by
    simp only [map_sub, map_add, map_mul]
    linear_combination (algebraMap C E c * u + algebraMap C E d) * h'
      - (algebraMap C E c' * u + algebraMap C E d') * h
  have hP : (Polynomial.C (a * c' - a' * c) * Polynomial.X ^ 2
      + Polynomial.C (a * d' + b * c' - a' * d - b' * c) * Polynomial.X
      + Polynomial.C (b * d' - b' * d) : Polynomial C) = 0 := by
    by_contra hne
    exact htu ⟨_, hne, by simpa using hpoly⟩
  have e2 : a * c' = a' * c := by
    have hc := congrArg (fun p : Polynomial C => Polynomial.coeff p 2) hP
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    norm_num at hc
    linear_combination hc
  have e1 : a * d' + b * c' = a' * d + b' * c := by
    have hc := congrArg (fun p : Polynomial C => Polynomial.coeff p 1) hP
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    norm_num at hc
    linear_combination hc
  have e0 : b * d' = b' * d := by
    have hc := congrArg (fun p : Polynomial C => Polynomial.coeff p 0) hP
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    norm_num at hc
    linear_combination hc
  have hcd : ¬ (c = 0 ∧ d = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hdet (by ring)
  by_cases ha : a = 0
  · have hbc : b * c ≠ 0 := by
      intro hz
      exact hdet (by rw [ha]; linear_combination -hz)
    have hb : b ≠ 0 := left_ne_zero_of_mul hbc
    have hc : c ≠ 0 := right_ne_zero_of_mul hbc
    have ha' : a' = 0 := by
      have hz : a' * c = 0 := by rw [ha] at e2; linear_combination -e2
      exact (mul_eq_zero.mp hz).resolve_right hc
    rw [ha, ha'] at e1
    refine ⟨b' / b, ?_, ?_, ?_, ?_, ?_⟩
    · intro ht0
      have hb'0 : b' = 0 := (div_eq_zero_iff.mp ht0).resolve_right hb
      exact hdet' (by rw [ha', hb'0]; ring)
    · rw [ha', ha]; ring
    · field_simp
    · field_simp
      linear_combination e1
    · field_simp
      linear_combination e0
  · have hta : a' = a' / a * a := by field_simp
    have htc : c' = a' / a * c := by
      field_simp
      linear_combination e2
    have hA : a * (d' - a' / a * d) = (b' - a' / a * b) * c := by
      field_simp
      linear_combination a * e1 - b * e2
    have hB : b * (d' - a' / a * d) = (b' - a' / a * b) * d := by
      field_simp
      linear_combination a * e0
    have hd0 : d' - a' / a * d = 0 := by
      have hkey : (a * d - b * c) * (d' - a' / a * d) = 0 := by
        linear_combination d * hA - c * hB
      exact (mul_eq_zero.mp hkey).resolve_left hdet
    have hb0 : b' - a' / a * b = 0 := by
      have hc0 : (b' - a' / a * b) * c = 0 := by rw [← hA, hd0]; ring
      have hdd0 : (b' - a' / a * b) * d = 0 := by rw [← hB, hd0]; ring
      by_contra hne
      exact hcd ⟨(mul_eq_zero.mp hc0).resolve_left hne,
        (mul_eq_zero.mp hdd0).resolve_left hne⟩
    refine ⟨a' / a, ?_, hta, ?_, htc, ?_⟩
    · intro ht0
      have ha'0 : a' = 0 := by rw [hta, ht0]; ring
      have hb'0 : b' = 0 := by rw [ht0] at hb0; linear_combination hb0
      exact hdet' (by rw [ha'0, hb'0]; ring)
    · linear_combination hb0
    · linear_combination hd0

omit [CharZero E] [Differential C] [Differential E] [DifferentialAlgebra C E] in
/-- A nondegenerate coefficient matrix stays nondegenerate in the extension. -/
theorem mobius_det_ne_zero_algebraMap {a b c d : C} (hdet : a * d - b * c ≠ 0) :
    algebraMap C E a * algebraMap C E d - algebraMap C E b * algebraMap C E c ≠ 0 := by
  have hne : algebraMap C E (a * d - b * c) ≠ 0 := by
    simpa using fun h => hdet ((algebraMap C E).injective (by simpa using h))
  simpa using hne

end

end GaloisForLFunctions.HTGeometry
