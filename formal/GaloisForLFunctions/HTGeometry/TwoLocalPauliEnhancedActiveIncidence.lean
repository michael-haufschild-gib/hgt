import GaloisForLFunctions.HTGeometry.TwoLocalPauliActiveWeightIncidence
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def pauliAlternateAxis (b : Bool) (a : Fin 3) : Fin 3 :=
  if b then pauliAxisPrev a else pauliAxisNext a

theorem pauliAlternateAxis_ne (b : Bool) (a : Fin 3) :
    pauliAlternateAxis b a ≠ a := by
  cases b <;> simp [pauliAlternateAxis, pauliAxisNext_ne, pauliAxisPrev_ne]

theorem pauliAlternateAxis_bool_injective (a : Fin 3) :
    Function.Injective (fun b : Bool => pauliAlternateAxis b a) := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact False.elim (pauliAxisPrev_ne_next a h.symm)
  · exact False.elim (pauliAxisPrev_ne_next a h)
  · rfl

theorem boolPauliConjugationSign_alternate_source_eq_neg_one
    (b : Bool) (a : Fin 3) :
    boolPauliConjugationSign (some (pauliAlternateAxis b a)) (some a) = -1 := by
  cases b <;> fin_cases a <;>
    norm_num [pauliAlternateAxis, boolPauliConjugationSign,
      pauliAxisNext, pauliAxisPrev] <;> simp_all

abbrev PauliActiveSite
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :=
  {i : Fin n // i ∈ pauliSupport P.1}

def activeOneSitePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveSite P × Bool) : Fin n → Option (Fin 3) :=
  singlePauliAxisLabel z.1.1
    (pauliAlternateAxis z.2 (matchingPauliAxis (P.1 z.1.1)))

theorem pauliWeight_activeOneSitePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveSite P × Bool) :
    pauliWeight (activeOneSitePauliAnticommutingLabel P z) = 1 := by
  rw [pauliWeight]
  have hfilter :
      Finset.univ.filter
        (fun s => activeOneSitePauliAnticommutingLabel P z s ≠ none) =
          {z.1.1} := by
    ext s
    by_cases hs : s = z.1.1 <;>
      simp [activeOneSitePauliAnticommutingLabel, singlePauliAxisLabel, hs]
  rw [hfilter, Finset.card_singleton]

theorem activeOneSitePauliAnticommutingLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveSite P × Bool) :
    activeOneSitePauliAnticommutingLabel P z ∈
      nonidentityPauliWords n q := by
  rw [mem_nonidentityPauliWords,
    pauliWeight_activeOneSitePauliAnticommutingLabel]
  omega

theorem finitePauliConjugationSign_activeOneSitePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveSite P × Bool) :
    finitePauliConjugationSign
        (activeOneSitePauliAnticommutingLabel P z) P.1 = -1 := by
  rw [activeOneSitePauliAnticommutingLabel,
    finitePauliConjugationSign_singlePauliAxisLabel]
  have hi : P.1 z.1.1 ≠ none := mem_pauliSupport.mp z.1.2
  cases hpi : P.1 z.1.1 with
  | none => exact (hi hpi).elim
  | some a =>
      simpa [hpi, matchingPauliAxis] using
        boolPauliConjugationSign_alternate_source_eq_neg_one z.2 a

theorem activeOneSitePauliAnticommutingLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (activeOneSitePauliAnticommutingLabel P) := by
  rintro ⟨zi, zb⟩ ⟨wi, wb⟩ hzw
  have hi : zi.1 = wi.1 := by
    by_contra hne
    have hvalue := congrFun hzw zi.1
    simp [activeOneSitePauliAnticommutingLabel, singlePauliAxisLabel, hne] at hvalue
  have hisub : zi = wi := Subtype.ext hi
  subst wi
  have hb : zb = wb := by
    apply pauliAlternateAxis_bool_injective
    have hvalue := congrFun hzw zi.1
    simpa [activeOneSitePauliAnticommutingLabel, singlePauliAxisLabel] using hvalue
  subst wb
  rfl

def activeTwoSitePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P × Bool) : Fin n → Option (Fin 3) :=
  pairLabel z.1.1.1 z.1.2.1
    (pauliAlternateAxis z.2 (matchingPauliAxis (P.1 z.1.1.1)))
    (matchingPauliAxis (P.1 z.1.2.1))

theorem pauliWeight_activeTwoSitePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P × Bool) :
    pauliWeight (activeTwoSitePauliAnticommutingLabel P z) = 2 := by
  rw [pauliWeight_eq_card_pauliSupport]
  change (labelSupport (activeTwoSitePauliAnticommutingLabel P z)).card = 2
  exact card_labelSupport_pairLabel (Ne.symm z.1.2.2) _ _

theorem activeTwoSitePauliAnticommutingLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P × Bool) :
    activeTwoSitePauliAnticommutingLabel P z ∈
      nonidentityPauliWords n q := by
  rw [mem_nonidentityPauliWords,
    pauliWeight_activeTwoSitePauliAnticommutingLabel]
  omega

theorem finitePauliConjugationSign_activeTwoSitePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P × Bool) :
    finitePauliConjugationSign
        (activeTwoSitePauliAnticommutingLabel P z) P.1 = -1 := by
  rw [activeTwoSitePauliAnticommutingLabel,
    finitePauliConjugationSign_pairLabel P.1 (Ne.symm z.1.2.2)]
  have hi : P.1 z.1.1.1 ≠ none := mem_pauliSupport.mp z.1.1.2
  cases hpi : P.1 z.1.1.1 with
  | none => exact (hi hpi).elim
  | some a =>
      rw [boolPauliConjugationSign_matchingPauliAxis]
      simp only [matchingPauliAxis]
      rw [boolPauliConjugationSign_alternate_source_eq_neg_one]
      norm_num

theorem activeTwoSitePauliAnticommutingLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (activeTwoSitePauliAnticommutingLabel P) := by
  rintro ⟨⟨zi, zj⟩, zb⟩ ⟨⟨wi, wj⟩, wb⟩ hzw
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
          have halt : pauliAlternateAxis zb a ≠ a := pauliAlternateAxis_ne zb a
          simp [activeTwoSitePauliAnticommutingLabel, pairLabel,
            hiwj, wj.2, hpwj, matchingPauliAxis] at hvalue
          exact halt hvalue
    · have hvalue := congrFun hzw zi.1
      simp [activeTwoSitePauliAnticommutingLabel, pairLabel,
        hne, hiwj] at hvalue
  have hisub : zi = wi := Subtype.ext hi
  subst wi
  have hj : zj.1 = wj.1 := by
    by_contra hne
    have hzji : zj.1 ≠ zi.1 := zj.2
    have hvalue := congrFun hzw zj.1
    simp [activeTwoSitePauliAnticommutingLabel, pairLabel,
      hzji, hne] at hvalue
  have hjsub : zj = wj := Subtype.ext hj
  subst wj
  have hb : zb = wb := by
    apply pauliAlternateAxis_bool_injective
    have hvalue := congrFun hzw zi.1
    simpa [activeTwoSitePauliAnticommutingLabel, pairLabel,
      matchingPauliAxis] using hvalue
  subst wb
  rfl

abbrev PauliEnhancedActiveFan
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :=
  (PauliActiveSite P × Bool) ⊕ (PauliActiveFanPair P × Bool)

def enhancedActivePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    PauliEnhancedActiveFan P → Fin n → Option (Fin 3)
  | Sum.inl z => activeOneSitePauliAnticommutingLabel P z
  | Sum.inr z => activeTwoSitePauliAnticommutingLabel P z

theorem enhancedActivePauliAnticommutingLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (z : PauliEnhancedActiveFan P) :
    enhancedActivePauliAnticommutingLabel P z ∈
      nonidentityPauliWords n q := by
  cases z with
  | inl z => exact activeOneSitePauliAnticommutingLabel_mem hq P z
  | inr z => exact activeTwoSitePauliAnticommutingLabel_mem hq P z

theorem finitePauliConjugationSign_enhancedActivePauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliEnhancedActiveFan P) :
    finitePauliConjugationSign
        (enhancedActivePauliAnticommutingLabel P z) P.1 = -1 := by
  cases z with
  | inl z => exact finitePauliConjugationSign_activeOneSitePauliAnticommutingLabel P z
  | inr z => exact finitePauliConjugationSign_activeTwoSitePauliAnticommutingLabel P z

theorem enhancedActivePauliAnticommutingLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (enhancedActivePauliAnticommutingLabel P) := by
  intro z w hzw
  cases z with
  | inl z =>
      cases w with
      | inl w =>
          exact congrArg Sum.inl
            (activeOneSitePauliAnticommutingLabel_injective P hzw)
      | inr w =>
          have hw := congrArg pauliWeight hzw
          change pauliWeight (activeOneSitePauliAnticommutingLabel P z) =
            pauliWeight (activeTwoSitePauliAnticommutingLabel P w) at hw
          rw [pauliWeight_activeOneSitePauliAnticommutingLabel,
            pauliWeight_activeTwoSitePauliAnticommutingLabel] at hw
          omega
  | inr z =>
      cases w with
      | inl w =>
          have hw := congrArg pauliWeight hzw
          change pauliWeight (activeTwoSitePauliAnticommutingLabel P z) =
            pauliWeight (activeOneSitePauliAnticommutingLabel P w) at hw
          rw [pauliWeight_activeTwoSitePauliAnticommutingLabel,
            pauliWeight_activeOneSitePauliAnticommutingLabel] at hw
          omega
      | inr w =>
          exact congrArg Sum.inr
            (activeTwoSitePauliAnticommutingLabel_injective P hzw)

theorem card_pauliActiveSite
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Fintype.card (PauliActiveSite P) = pauliWeight P.1 := by
  rw [Fintype.card_coe, ← pauliWeight_eq_card_pauliSupport]

theorem card_pauliEnhancedActiveFan
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Fintype.card (PauliEnhancedActiveFan P) =
      2 * pauliWeight P.1 * n := by
  have hn : n ≠ 0 := by
    intro hn
    obtain ⟨i, _hi⟩ := pauliCharacterSupport_nonempty P
    subst n
    exact Fin.elim0 i
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    card_pauliActiveSite, card_pauliActiveFanPair]
  simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp
  ring

/-- Every weight-`w` Pauli string has at least `2wn` distinct anticommuting
directions in the ordinary one/two-local Pauli dictionary.  Both alternate
axes are retained, and one-site directions supply the missing diagonal term. -/
theorem card_filter_twoLocalPauli_anticommuting_ge_enhancedActiveWeight
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n)) :
    2 * pauliWeight P.1 * n ≤
      ((nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1).card := by
  rw [← card_pauliEnhancedActiveFan P]
  let f : PauliEnhancedActiveFan P →
      {Q // Q ∈ (nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1} :=
    fun z => ⟨enhancedActivePauliAnticommutingLabel P z,
      Finset.mem_filter.mpr
        ⟨enhancedActivePauliAnticommutingLabel_mem hq P z,
          finitePauliConjugationSign_enhancedActivePauliAnticommutingLabel P z⟩⟩
  have hf : Function.Injective f := by
    intro z w h
    apply enhancedActivePauliAnticommutingLabel_injective P
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_coe] at hcard

abbrev PauliBoundaryExtraFan
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :=
  (PauliSupportBoundaryPair P × Bool) × Fin 2

def boundaryExtraPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliBoundaryExtraFan P) : Fin n → Option (Fin 3) :=
  pairLabel z.1.1.1.1 z.1.1.2.1
    (pauliAlternateAxis z.1.2 (matchingPauliAxis (P.1 z.1.1.1.1)))
    z.2.succ

theorem pauliWeight_boundaryExtraPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliBoundaryExtraFan P) :
    pauliWeight (boundaryExtraPauliAnticommutingLabel P z) = 2 := by
  rw [pauliWeight_eq_card_pauliSupport]
  change (labelSupport (boundaryExtraPauliAnticommutingLabel P z)).card = 2
  exact card_labelSupport_pairLabel
    (pauliSupportBoundaryPair_ne P z.1.1) _ _

theorem boundaryExtraPauliAnticommutingLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (z : PauliBoundaryExtraFan P) :
    boundaryExtraPauliAnticommutingLabel P z ∈
      nonidentityPauliWords n q := by
  rw [mem_nonidentityPauliWords,
    pauliWeight_boundaryExtraPauliAnticommutingLabel]
  omega

theorem finitePauliConjugationSign_boundaryExtraPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliBoundaryExtraFan P) :
    finitePauliConjugationSign
        (boundaryExtraPauliAnticommutingLabel P z) P.1 = -1 := by
  rw [boundaryExtraPauliAnticommutingLabel,
    finitePauliConjugationSign_pairLabel P.1
      (pauliSupportBoundaryPair_ne P z.1.1)]
  have hi : P.1 z.1.1.1.1 ≠ none := mem_pauliSupport.mp z.1.1.1.2
  have hj : P.1 z.1.1.2.1 = none := by
    by_contra h
    exact z.1.1.2.2 (mem_pauliSupport.mpr h)
  cases hpi : P.1 z.1.1.1.1 with
  | none => exact (hi hpi).elim
  | some a =>
      simp only [matchingPauliAxis]
      rw [boolPauliConjugationSign_alternate_source_eq_neg_one]
      simp [hj, boolPauliConjugationSign]

theorem boundaryExtraPauliAnticommutingLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (boundaryExtraPauliAnticommutingLabel P) := by
  rintro ⟨⟨⟨zi, zj⟩, zb⟩, za⟩ ⟨⟨⟨wi, wj⟩, wb⟩, wa⟩ hzw
  have hi : zi.1 = wi.1 := by
    by_contra hne
    have hiw2 : zi.1 ≠ wj.1 := by
      intro h
      exact wj.2 (h ▸ zi.2)
    have hvalue := congrFun hzw zi.1
    simp [boundaryExtraPauliAnticommutingLabel, pairLabel,
      hne, hiw2] at hvalue
  have hisub : zi = wi := Subtype.ext hi
  subst wi
  have hj : zj.1 = wj.1 := by
    by_contra hne
    have hzji : zj.1 ≠ zi.1 := Ne.symm
      (pauliSupportBoundaryPair_ne P ⟨zi, zj⟩)
    have hvalue := congrFun hzw zj.1
    simp [boundaryExtraPauliAnticommutingLabel, pairLabel,
      hzji, hne] at hvalue
  have hjsub : zj = wj := Subtype.ext hj
  subst wj
  have hb : zb = wb := by
    apply pauliAlternateAxis_bool_injective
    have hvalue := congrFun hzw zi.1
    simpa [boundaryExtraPauliAnticommutingLabel, pairLabel,
      matchingPauliAxis] using hvalue
  subst wb
  have ha : za = wa := by
    apply Fin.succ_injective
    have hvalue := congrFun hzw zj.1
    simpa [boundaryExtraPauliAnticommutingLabel, pairLabel,
      Ne.symm (pauliSupportBoundaryPair_ne P ⟨zi, zj⟩)] using hvalue
  subst wa
  rfl

theorem activeTwoSitePauliAnticommutingLabel_ne_boundaryExtra
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliActiveFanPair P × Bool)
    (w : PauliBoundaryExtraFan P) :
    activeTwoSitePauliAnticommutingLabel P z ≠
      boundaryExtraPauliAnticommutingLabel P w := by
  intro hzw
  have hi : z.1.1.1 = w.1.1.1.1 := by
    by_contra hne
    have hiw2 : z.1.1.1 ≠ w.1.1.2.1 := by
      intro h
      exact w.1.1.2.2 (h ▸ z.1.1.2)
    have hvalue := congrFun hzw z.1.1.1
    simp [activeTwoSitePauliAnticommutingLabel,
      boundaryExtraPauliAnticommutingLabel, pairLabel,
      hne, hiw2] at hvalue
  have hj : z.1.2.1 = w.1.1.2.1 := by
    by_contra hne
    have hzji : z.1.2.1 ≠ z.1.1.1 := z.1.2.2
    have hzjw1 : z.1.2.1 ≠ w.1.1.1.1 := by simpa [hi] using hzji
    have hvalue := congrFun hzw z.1.2.1
    simp [activeTwoSitePauliAnticommutingLabel,
      boundaryExtraPauliAnticommutingLabel, pairLabel,
      hzji, hzjw1, hne] at hvalue
  have hjInactive : P.1 z.1.2.1 = none := by
    have := w.1.1.2.2
    rw [← hj] at this
    by_contra h
    exact this (mem_pauliSupport.mpr h)
  have hvalue := congrFun hzw z.1.2.1
  have hzji : z.1.2.1 ≠ z.1.1.1 := z.1.2.2
  have hwji : w.1.1.2.1 ≠ w.1.1.1.1 :=
    Ne.symm (pauliSupportBoundaryPair_ne P w.1.1)
  have hwinactive : P.1 w.1.1.2.1 = none := by
    by_contra h
    exact w.1.1.2.2 (mem_pauliSupport.mpr h)
  have heq : (0 : Fin 3) = w.2.succ := by
    simpa [activeTwoSitePauliAnticommutingLabel,
      boundaryExtraPauliAnticommutingLabel, pairLabel,
      hzji, hwji, hi, hj, hwinactive, matchingPauliAxis] using hvalue
  exact (Fin.succ_ne_zero w.2) heq.symm

abbrev PauliExactTwoLocalAnticommutingFan
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :=
  PauliEnhancedActiveFan P ⊕ PauliBoundaryExtraFan P

def exactTwoLocalPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    PauliExactTwoLocalAnticommutingFan P → Fin n → Option (Fin 3)
  | Sum.inl z => enhancedActivePauliAnticommutingLabel P z
  | Sum.inr z => boundaryExtraPauliAnticommutingLabel P z

theorem exactTwoLocalPauliAnticommutingLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (z : PauliExactTwoLocalAnticommutingFan P) :
    exactTwoLocalPauliAnticommutingLabel P z ∈
      nonidentityPauliWords n q := by
  cases z with
  | inl z => exact enhancedActivePauliAnticommutingLabel_mem hq P z
  | inr z => exact boundaryExtraPauliAnticommutingLabel_mem hq P z

theorem finitePauliConjugationSign_exactTwoLocalPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliExactTwoLocalAnticommutingFan P) :
    finitePauliConjugationSign
        (exactTwoLocalPauliAnticommutingLabel P z) P.1 = -1 := by
  cases z with
  | inl z =>
      exact finitePauliConjugationSign_enhancedActivePauliAnticommutingLabel P z
  | inr z =>
      exact finitePauliConjugationSign_boundaryExtraPauliAnticommutingLabel P z

theorem exactTwoLocalPauliAnticommutingLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (exactTwoLocalPauliAnticommutingLabel P) := by
  intro z w hzw
  cases z with
  | inl z =>
      cases w with
      | inl w =>
          exact congrArg Sum.inl
            (enhancedActivePauliAnticommutingLabel_injective P hzw)
      | inr w =>
          cases z with
          | inl z =>
              have hw := congrArg pauliWeight hzw
              change pauliWeight (activeOneSitePauliAnticommutingLabel P z) =
                pauliWeight (boundaryExtraPauliAnticommutingLabel P w) at hw
              rw [pauliWeight_activeOneSitePauliAnticommutingLabel,
                pauliWeight_boundaryExtraPauliAnticommutingLabel] at hw
              omega
          | inr z =>
              exact False.elim
                (activeTwoSitePauliAnticommutingLabel_ne_boundaryExtra P z w hzw)
  | inr z =>
      cases w with
      | inl w =>
          cases w with
          | inl w =>
              have hw := congrArg pauliWeight hzw
              change pauliWeight (boundaryExtraPauliAnticommutingLabel P z) =
                pauliWeight (activeOneSitePauliAnticommutingLabel P w) at hw
              rw [pauliWeight_boundaryExtraPauliAnticommutingLabel,
                pauliWeight_activeOneSitePauliAnticommutingLabel] at hw
              omega
          | inr w =>
              exact False.elim
                (activeTwoSitePauliAnticommutingLabel_ne_boundaryExtra P w z hzw.symm)
      | inr w =>
          exact congrArg Sum.inr
            (boundaryExtraPauliAnticommutingLabel_injective P hzw)

theorem card_pauliBoundaryExtraFan
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Fintype.card (PauliBoundaryExtraFan P) =
      4 * pauliWeight P.1 * (n - pauliWeight P.1) := by
  rw [Fintype.card_prod, Fintype.card_prod,
    card_pauliSupportBoundaryPair]
  simp
  ring

theorem card_pauliExactTwoLocalAnticommutingFan
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Fintype.card (PauliExactTwoLocalAnticommutingFan P) =
      2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) := by
  have hw : pauliWeight P.1 ≤ n := by
    rw [pauliWeight_eq_card_pauliSupport]
    simpa using Finset.card_le_card
      (show pauliSupport P.1 ⊆ (Finset.univ : Finset (Fin n)) from
        Finset.subset_univ _)
  rw [Fintype.card_sum, card_pauliEnhancedActiveFan,
    card_pauliBoundaryExtraFan]
  have hpoly :
      3 * n - 2 * pauliWeight P.1 =
        n + 2 * (n - pauliWeight P.1) := by
    omega
  rw [hpoly]
  ring

theorem pauliWeight_pos_of_nonzeroCharacter
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    0 < pauliWeight P.1 := by
  rw [pauliWeight_eq_card_pauliSupport, Finset.card_pos]
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply P.2
  funext i
  have hi : i ∉ pauliSupport P.1 := by simp [h]
  simpa [pauliSupport, pauliCharacterZero] using hi

theorem six_mul_qubitCount_sub_four_le_fullWeightPolynomial_of_weight
    {n w : ℕ} (hw1 : 1 ≤ w) (hwn : w ≤ n) :
    6 * n - 4 ≤ 2 * w * (3 * n - 2 * w) := by
  by_cases hw : w = 1
  · subst w
    omega
  have hw2 : 2 ≤ w := by omega
  have hn2 : 2 ≤ n := by omega
  have hinner : 4 * w + 4 ≤ 6 * n := by omega
  have hinnerZ : 4 * (w : ℤ) + 4 ≤ 6 * (n : ℤ) := by
    exact_mod_cast hinner
  have hwZ : 1 ≤ (w : ℤ) := by exact_mod_cast hw1
  have hA : 0 ≤ 6 * (n : ℤ) - 4 * (w : ℤ) - 4 := by linarith
  have hB : 0 ≤ (w : ℤ) - 1 := by linarith
  have hZ :
      6 * (n : ℤ) - 4 ≤
        2 * (w : ℤ) * (3 * (n : ℤ) - 2 * (w : ℤ)) := by
    nlinarith [mul_nonneg hA hB]
  have hL : 4 ≤ 6 * n := by omega
  have hR : 2 * w ≤ 3 * n := by omega
  have hcast :
      ((6 * n - 4 : ℕ) : ℤ) ≤
        ((2 * w * (3 * n - 2 * w) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hL, Nat.cast_sub hR]
    exact hZ
  exact_mod_cast hcast

/-- The full weight polynomial has worst-target value `6n-4`.  Equality is
attained at weight one; extensive weights receive a quadratic charge. -/
theorem six_mul_qubitCount_sub_four_le_fullWeightPolynomial
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    6 * n - 4 ≤
      2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) := by
  apply six_mul_qubitCount_sub_four_le_fullWeightPolynomial_of_weight
    (pauliWeight_pos_of_nonzeroCharacter P)
  rw [pauliWeight_eq_card_pauliSupport]
  simpa using Finset.card_le_card
    (show pauliSupport P.1 ⊆ (Finset.univ : Finset (Fin n)) from
      Finset.subset_univ _)

/-- Full polynomial incidence lower bound.  A Pauli target of weight `w`
has at least `2w(3n-2w)` anticommuting nonidentity Pauli words of weight at
most two.  The injected family retains every active--active direction and all
three inactive-site axes. -/
theorem card_filter_twoLocalPauli_anticommuting_ge_fullWeightPolynomial
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) ≤
      ((nonidentityPauliWords n 2).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1).card := by
  rw [← card_pauliExactTwoLocalAnticommutingFan P]
  let f : PauliExactTwoLocalAnticommutingFan P →
      {Q // Q ∈ (nonidentityPauliWords n 2).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1} :=
    fun z => ⟨exactTwoLocalPauliAnticommutingLabel P z,
      Finset.mem_filter.mpr
        ⟨exactTwoLocalPauliAnticommutingLabel_mem (by omega) P z,
          finitePauliConjugationSign_exactTwoLocalPauliAnticommutingLabel P z⟩⟩
  have hf : Function.Injective f := by
    intro z w h
    apply exactTwoLocalPauliAnticommutingLabel_injective P
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_coe] at hcard

end

end GaloisForLFunctions.HTGeometry
