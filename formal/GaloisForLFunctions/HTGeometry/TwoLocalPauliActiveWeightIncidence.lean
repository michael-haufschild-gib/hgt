import GaloisForLFunctions.HTGeometry.TwoLocalPauliBoundaryIncidence

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev PauliActiveFanPair
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :=
  Σ i : {i : Fin n // i ∈ pauliSupport P.1},
    {j : Fin n // j ≠ i.1}

def activeFanPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P) : Fin n → Option (Fin 3) :=
  pairLabel z.1.1 z.2.1
    (pauliAxisPrev (matchingPauliAxis (P.1 z.1.1)))
    (matchingPauliAxis (P.1 z.2.1))

theorem pauliWeight_activeFanPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P) :
    pauliWeight (activeFanPauliAnticommutingLabel P z) = 2 := by
  rw [pauliWeight_eq_card_pauliSupport]
  change (labelSupport (activeFanPauliAnticommutingLabel P z)).card = 2
  exact card_labelSupport_pairLabel (Ne.symm z.2.2) _ _

theorem activeFanPauliAnticommutingLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P) :
    activeFanPauliAnticommutingLabel P z ∈ nonidentityPauliWords n q := by
  rw [mem_nonidentityPauliWords,
    pauliWeight_activeFanPauliAnticommutingLabel]
  omega

theorem finitePauliConjugationSign_activeFanPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P) :
    finitePauliConjugationSign
        (activeFanPauliAnticommutingLabel P z) P.1 = -1 := by
  rw [activeFanPauliAnticommutingLabel,
    finitePauliConjugationSign_pairLabel P.1 (Ne.symm z.2.2)]
  have hi : P.1 z.1.1 ≠ none := mem_pauliSupport.mp z.1.2
  cases hpi : P.1 z.1.1 with
  | none => exact (hi hpi).elim
  | some a =>
      have hmul :
          boolPauliConjugationSign (some (pauliAxisPrev a)) (some a) *
              boolPauliConjugationSign
                (some (matchingPauliAxis (P.1 z.2.1))) (P.1 z.2.1) = -1 := by
        rw [boolPauliConjugationSign_prev_source_eq_neg_one,
          boolPauliConjugationSign_matchingPauliAxis]
        norm_num
      simpa [hpi, matchingPauliAxis] using hmul

theorem activeFanPauliAnticommutingLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (activeFanPauliAnticommutingLabel P) := by
  rintro ⟨zi, zj⟩ ⟨wi, wj⟩ hzw
  have hi : zi.1 = wi.1 := by
    by_contra hne
    by_cases hiwj : zi.1 = wj.1
    · have hvalue := congrFun hzw zi.1
      have hactive : P.1 zi.1 ≠ none := mem_pauliSupport.mp zi.2
      cases hpi : P.1 zi.1 with
      | none => exact (hactive hpi).elim
      | some a =>
          have hpwj : P.1 wj.1 = some a := by
            rw [← hiwj]
            exact hpi
          have hprev : pauliAxisPrev a ≠ a := pauliAxisPrev_ne a
          simp [activeFanPauliAnticommutingLabel, pairLabel,
            hiwj, wj.2, hpwj, matchingPauliAxis] at hvalue
          exact hprev hvalue
    · have hvalue := congrFun hzw zi.1
      simp [activeFanPauliAnticommutingLabel, pairLabel,
        hne, hiwj] at hvalue
  have hisub : zi = wi := Subtype.ext hi
  subst wi
  have hj : zj.1 = wj.1 := by
    by_contra hne
    have hzji : zj.1 ≠ zi.1 := zj.2
    have hvalue := congrFun hzw zj.1
    simp [activeFanPauliAnticommutingLabel, pairLabel,
      hzji, hne] at hvalue
  have hjsub : zj = wj := Subtype.ext hj
  subst wj
  rfl

theorem card_sites_ne_site {n : ℕ} (i : Fin n) :
    Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
  rw [Fintype.card_subtype_compl]
  simp

theorem card_pauliActiveFanPair
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Fintype.card (PauliActiveFanPair P) =
      pauliWeight P.1 * (n - 1) := by
  rw [Fintype.card_sigma]
  simp_rw [card_sites_ne_site]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_coe,
    ← pauliWeight_eq_card_pauliSupport]
  simp

theorem card_filter_twoLocalPauli_anticommuting_ge_activeWeight
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n)) :
    pauliWeight P.1 * (n - 1) ≤
      ((nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1).card := by
  rw [← card_pauliActiveFanPair P]
  let f : PauliActiveFanPair P →
      {Q // Q ∈ (nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1} :=
    fun z => ⟨activeFanPauliAnticommutingLabel P z,
      Finset.mem_filter.mpr
        ⟨activeFanPauliAnticommutingLabel_mem hq P z,
          finitePauliConjugationSign_activeFanPauliAnticommutingLabel P z⟩⟩
  have hf : Function.Injective f := by
    intro z w h
    apply activeFanPauliAnticommutingLabel_injective P
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_coe] at hcard

end

end GaloisForLFunctions.HTGeometry
