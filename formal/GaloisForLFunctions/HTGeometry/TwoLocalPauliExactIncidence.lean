import GaloisForLFunctions.HTGeometry.TwoLocalPauliEnhancedActiveIncidence

/-!
# Exact ordinary two-local Pauli incidence

For a nonzero Pauli target of weight `w`, the number of nonidentity Pauli
words of weight at most two that anticommute with it is exactly
`2w(3n-2w)`.  The proof classifies every filtered word by its unique locally
odd target site and reconstructs the explicit full fan.  Thus the prior fan
lower bound is exhaustive, not merely an injected subfamily.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def pauliOddSites
    {n : ℕ} (Q P : Fin n → Option (Fin 3)) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    boolPauliConjugationSign (Q i) (P i) = -1

theorem boolPauliConjugationSign_eq_one_or_neg_one
    (q p : Option (Fin 3)) :
    boolPauliConjugationSign q p = 1 ∨
      boolPauliConjugationSign q p = -1 := by
  unfold boolPauliConjugationSign
  split <;> simp

theorem pauliOddSites_subset_labelSupport_left
    {n : ℕ} (Q P : Fin n → Option (Fin 3)) :
    pauliOddSites Q P ⊆ labelSupport Q := by
  intro i hi
  simp only [pauliOddSites, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [mem_labelSupport]
  intro hnone
  simp [hnone, boolPauliConjugationSign] at hi
  norm_num at hi

theorem pauliOddSites_subset_labelSupport_right
    {n : ℕ} (Q P : Fin n → Option (Fin 3)) :
    pauliOddSites Q P ⊆ pauliSupport P := by
  intro i hi
  simp only [pauliOddSites, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [mem_pauliSupport]
  intro hnone
  simp [hnone, boolPauliConjugationSign] at hi
  norm_num at hi

/-- Global anticommutation is parity of locally odd occupied sites. -/
theorem finitePauliConjugationSign_eq_neg_one_pow_oddSites_card
    {n : ℕ} (Q P : Fin n → Option (Fin 3)) :
    finitePauliConjugationSign Q P =
      (-1 : ℂ) ^ (pauliOddSites Q P).card := by
  rw [finitePauliConjugationSign]
  calc
    (∏ i, boolPauliConjugationSign (Q i) (P i)) =
        (∏ i ∈ pauliOddSites Q P,
          boolPauliConjugationSign (Q i) (P i)) := by
      symm
      apply Finset.prod_subset (Finset.filter_subset _ _)
      intro i _hi hnot
      have hne : boolPauliConjugationSign (Q i) (P i) ≠ -1 := by
        simpa [pauliOddSites] using hnot
      rcases boolPauliConjugationSign_eq_one_or_neg_one (Q i) (P i) with h | h
      · exact h
      · exact (hne h).elim
    _ = (∏ _i ∈ pauliOddSites Q P, (-1 : ℂ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      simpa [pauliOddSites] using hi
    _ = (-1 : ℂ) ^ (pauliOddSites Q P).card :=
      Finset.prod_const (-1)

/-- A weight-at-most-two word with odd global sign has one and only one
locally odd site. -/
theorem card_pauliOddSites_eq_one_of_sign_neg_one_of_weight_le_two
    {n : ℕ} {Q P : Fin n → Option (Fin 3)}
    (hsign : finitePauliConjugationSign Q P = -1)
    (hweight : pauliWeight Q ≤ 2) :
    (pauliOddSites Q P).card = 1 := by
  have hcard : (pauliOddSites Q P).card ≤ 2 := by
    calc
      (pauliOddSites Q P).card ≤ (labelSupport Q).card :=
        Finset.card_le_card (pauliOddSites_subset_labelSupport_left Q P)
      _ = pauliWeight Q := (pauliWeight_eq_card_pauliSupport Q).symm
      _ ≤ 2 := hweight
  rw [finitePauliConjugationSign_eq_neg_one_pow_oddSites_card] at hsign
  interval_cases h : (pauliOddSites Q P).card
  · norm_num [h] at hsign
  · rfl
  · norm_num [h] at hsign

theorem exists_bool_pauliAlternateAxis_eq_of_ne
    {a b : Fin 3} (hba : b ≠ a) :
    ∃ z : Bool, pauliAlternateAxis z a = b := by
  fin_cases a <;> fin_cases b <;>
    simp_all [pauliAlternateAxis, pauliAxisNext, pauliAxisPrev]

theorem eq_singlePauliAxisLabel_of_support_eq_singleton
    {n : ℕ} (Q : Fin n → Option (Fin 3)) (i : Fin n) (a : Fin 3)
    (hsupport : pauliSupport Q = {i}) (hvalue : Q i = some a) :
    Q = singlePauliAxisLabel i a := by
  funext j
  by_cases hji : j = i
  · subst j
    simpa [singlePauliAxisLabel] using hvalue
  · have hjnone : Q j = none := by
      by_contra hj
      have hjmem : j ∈ pauliSupport Q := mem_pauliSupport.mpr hj
      rw [hsupport] at hjmem
      exact hji (Finset.mem_singleton.mp hjmem)
    simp [singlePauliAxisLabel, hji, hjnone]

theorem eq_pairLabel_of_support_eq_pair
    {n : ℕ} (Q : Fin n → Option (Fin 3))
    (i j : Fin n) (a b : Fin 3)
    (hsupport : pauliSupport Q = {i, j})
    (hivalue : Q i = some a) (hjvalue : Q j = some b) :
    Q = pairLabel i j a b := by
  funext k
  by_cases hki : k = i
  · subst k
    simpa [pairLabel] using hivalue
  · by_cases hkj : k = j
    · subst k
      simpa [pairLabel, hki] using hjvalue
    · have hknone : Q k = none := by
        by_contra hk
        have hkmem : k ∈ pauliSupport Q := mem_pauliSupport.mpr hk
        rw [hsupport] at hkmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkmem
        exact hkmem.elim hki hkj
      simp [pairLabel, hki, hkj, hknone]

/-- Every anticommuting word of weight at most two occurs in the explicit
full fan.  Source labels are reconstructed without quotienting or counting
by an upper estimate. -/
theorem exists_exactTwoLocalPauliAnticommutingLabel_eq
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    {Q : Fin n → Option (Fin 3)}
    (hQ : Q ∈ (nonidentityPauliWords n 2).filter fun R =>
      finitePauliConjugationSign R P.1 = -1) :
    ∃ z : PauliExactTwoLocalAnticommutingFan P,
      exactTwoLocalPauliAnticommutingLabel P z = Q := by
  rw [Finset.mem_filter] at hQ
  have hword := mem_nonidentityPauliWords.mp hQ.1
  have hoddCard : (pauliOddSites Q P.1).card = 1 :=
    card_pauliOddSites_eq_one_of_sign_neg_one_of_weight_le_two hQ.2 hword.2
  obtain ⟨i, hodd⟩ := Finset.card_eq_one.mp hoddCard
  have hiOdd : i ∈ pauliOddSites Q P.1 := by simp [hodd]
  have hiQSupport : i ∈ pauliSupport Q :=
    pauliOddSites_subset_labelSupport_left Q P.1 hiOdd
  have hiPSupport : i ∈ pauliSupport P.1 :=
    pauliOddSites_subset_labelSupport_right Q P.1 hiOdd
  have hiLocal : boolPauliConjugationSign (Q i) (P.1 i) = -1 := by
    simpa [pauliOddSites] using hiOdd
  have hiQne : Q i ≠ none := mem_pauliSupport.mp hiQSupport
  have hiPne : P.1 i ≠ none := mem_pauliSupport.mp hiPSupport
  cases hQi : Q i with
  | none => exact (hiQne hQi).elim
  | some qi =>
    cases hPi : P.1 i with
    | none => exact (hiPne hPi).elim
    | some pi =>
      have hqipi : qi ≠ pi := by
        intro h
        subst qi
        simp [hQi, hPi, boolPauliConjugationSign] at hiLocal
        norm_num at hiLocal
      obtain ⟨zbool, hzbool⟩ :=
        exists_bool_pauliAlternateAxis_eq_of_ne hqipi
      have hsupportCard : (pauliSupport Q).card = 1 ∨
          (pauliSupport Q).card = 2 := by
        rw [← pauliWeight_eq_card_pauliSupport]
        omega
      rcases hsupportCard with hsupportOne | hsupportTwo
      · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hsupportOne
        have hik : i = k := by
          have := hiQSupport
          rw [hk] at this
          simpa using this
        subst k
        have hQsingle := eq_singlePauliAxisLabel_of_support_eq_singleton
          Q i qi hk hQi
        refine ⟨Sum.inl (Sum.inl (⟨i, hiPSupport⟩, zbool)), ?_⟩
        simpa [exactTwoLocalPauliAnticommutingLabel,
          enhancedActivePauliAnticommutingLabel,
          activeOneSitePauliAnticommutingLabel, hPi, matchingPauliAxis,
          hzbool] using hQsingle.symm
      · have heraseCard : ((pauliSupport Q).erase i).card = 1 := by
          rw [Finset.card_erase_of_mem hiQSupport, hsupportTwo]
        obtain ⟨j, hjErase⟩ := Finset.card_eq_one.mp heraseCard
        have hjEraseMem : j ∈ (pauliSupport Q).erase i := by simp [hjErase]
        have hji : j ≠ i := (Finset.mem_erase.mp hjEraseMem).1
        have hjQSupport : j ∈ pauliSupport Q :=
          (Finset.mem_erase.mp hjEraseMem).2
        have hsupportPair : pauliSupport Q = {i, j} := by
          calc
            pauliSupport Q = insert i ((pauliSupport Q).erase i) :=
              (Finset.insert_erase hiQSupport).symm
            _ = {i, j} := by rw [hjErase]
        have hjQne : Q j ≠ none := mem_pauliSupport.mp hjQSupport
        cases hQj : Q j with
        | none => exact (hjQne hQj).elim
        | some qj =>
          have hQpair := eq_pairLabel_of_support_eq_pair
            Q i j qi qj hsupportPair hQi hQj
          let zi : PauliActiveSite P := ⟨i, hiPSupport⟩
          let zj : {k : Fin n // k ≠ zi.1} :=
            ⟨j, by simpa [zi] using hji⟩
          let zij : PauliActiveFanPair P := ⟨zi, zj⟩
          by_cases hjP : j ∈ pauliSupport P.1
          · have hjPne : P.1 j ≠ none := mem_pauliSupport.mp hjP
            cases hPj : P.1 j with
            | none => exact (hjPne hPj).elim
            | some pj =>
              have hjNotOdd : j ∉ pauliOddSites Q P.1 := by
                rw [hodd]
                simp [hji]
              have hjLocalNe :
                  boolPauliConjugationSign (Q j) (P.1 j) ≠ -1 := by
                simpa [pauliOddSites] using hjNotOdd
              have hqjpj : qj = pj := by
                by_contra hne
                apply hjLocalNe
                simp [hQj, hPj, boolPauliConjugationSign, hne]
              refine ⟨Sum.inl (Sum.inr (zij, zbool)), ?_⟩
              simpa [exactTwoLocalPauliAnticommutingLabel,
                enhancedActivePauliAnticommutingLabel,
                activeTwoSitePauliAnticommutingLabel,
                zij, zi, zj, hPi, hPj, matchingPauliAxis, hzbool,
                hqjpj] using hQpair.symm
          · have hPj : P.1 j = none := by
              by_contra hne
              exact hjP (mem_pauliSupport.mpr hne)
            by_cases hqjzero : qj = 0
            · refine ⟨Sum.inl (Sum.inr (zij, zbool)), ?_⟩
              simpa [exactTwoLocalPauliAnticommutingLabel,
                enhancedActivePauliAnticommutingLabel,
                activeTwoSitePauliAnticommutingLabel,
                zij, zi, zj, hPi, hPj, matchingPauliAxis, hzbool,
                hqjzero] using hQpair.symm
            · obtain ⟨qjPred, hqjPred⟩ := Fin.exists_succ_eq_of_ne_zero hqjzero
              let zjInactive : {k : Fin n // k ∉ pauliSupport P.1} := ⟨j, hjP⟩
              let zBoundary : PauliSupportBoundaryPair P := ⟨zi, zjInactive⟩
              refine ⟨Sum.inr ((zBoundary, zbool), qjPred), ?_⟩
              simpa [exactTwoLocalPauliAnticommutingLabel,
                boundaryExtraPauliAnticommutingLabel,
                zBoundary, zi, zjInactive, hPi, matchingPauliAxis,
                hzbool, hqjPred] using hQpair.symm

/-- **Exact ordinary two-local Pauli incidence law.**  A nonzero Pauli target
of weight `w` anticommutes with exactly `2w(3n-2w)` nonidentity Pauli words of
weight at most two. -/
theorem card_filter_twoLocalPauli_anticommuting_eq_fullWeightPolynomial
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    ((nonidentityPauliWords n 2).filter fun Q =>
      finitePauliConjugationSign Q P.1 = -1).card =
        2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) := by
  apply Nat.le_antisymm
  · rw [← card_pauliExactTwoLocalAnticommutingFan P]
    let f : PauliExactTwoLocalAnticommutingFan P →
        {Q // Q ∈ (nonidentityPauliWords n 2).filter fun R =>
          finitePauliConjugationSign R P.1 = -1} :=
      fun z => ⟨exactTwoLocalPauliAnticommutingLabel P z,
        Finset.mem_filter.mpr
          ⟨exactTwoLocalPauliAnticommutingLabel_mem (by omega) P z,
            finitePauliConjugationSign_exactTwoLocalPauliAnticommutingLabel P z⟩⟩
    have hf : Function.Surjective f := by
      intro Q
      obtain ⟨z, hz⟩ := exists_exactTwoLocalPauliAnticommutingLabel_eq P Q.2
      refine ⟨z, ?_⟩
      exact Subtype.ext hz
    have hcard := Fintype.card_le_of_surjective f hf
    rw [Fintype.card_coe] at hcard
    exact hcard
  · exact card_filter_twoLocalPauli_anticommuting_ge_fullWeightPolynomial P

/-- Weight-one targets attain the universal worst-sector value `6n-4`.
Consequently no lower bound depending only on this two-local incidence count
can have a superlinear worst-target exponent. -/
theorem card_filter_twoLocalPauli_anticommuting_eq_sixNSubFour_of_weight_one
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (hweight : pauliWeight P.1 = 1) :
    ((nonidentityPauliWords n 2).filter fun Q =>
      finitePauliConjugationSign Q P.1 = -1).card = 6 * n - 4 := by
  rw [card_filter_twoLocalPauli_anticommuting_eq_fullWeightPolynomial,
    hweight]
  have hn : 1 ≤ n := by
    rw [pauliWeight_eq_card_pauliSupport] at hweight
    have hle := Finset.card_le_card
      (show pauliSupport P.1 ⊆ (Finset.univ : Finset (Fin n)) from
        Finset.subset_univ _)
    simpa [hweight] using hle
  omega

end

end GaloisForLFunctions.HTGeometry
