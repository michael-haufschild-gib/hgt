import GaloisForLFunctions.HTGeometry.NonidentityPauliWordCount
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectSelector
import GaloisForLFunctions.HTGeometry.PauliChainLabels
import GaloisForLFunctions.HTGeometry.GraphLocalPauliDetector

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def matchingPauliAxis : Option (Fin 3) → Fin 3
  | none => 0
  | some a => a

theorem boolPauliConjugationSign_matchingPauliAxis (p : Option (Fin 3)) :
    boolPauliConjugationSign (some (matchingPauliAxis p)) p = 1 := by
  cases p <;> simp [matchingPauliAxis, boolPauliConjugationSign]

theorem finitePauliConjugationSign_pairLabel
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) {v w : σ} (hvw : v ≠ w)
    (a b : Fin 3) :
    finitePauliConjugationSign (pairLabel v w a b) P =
      boolPauliConjugationSign (some a) (P v) *
        boolPauliConjugationSign (some b) (P w) := by
  rw [finitePauliConjugationSign]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton v _ (by simp)]
  have hrest :
      (∏ s ∈ Finset.univ \ {v},
        boolPauliConjugationSign (pairLabel v w a b s) (P s)) =
        boolPauliConjugationSign (some b) (P w) := by
    have hwval : pairLabel v w a b w = some b := by
      simp [pairLabel, Ne.symm hvw]
    rw [← hwval]
    apply Finset.prod_eq_single w
    · intro s hs hsw
      have hsv : s ≠ v := by
        have hnotmem := (Finset.mem_sdiff.mp hs).2
        simpa using hnotmem
      simp [pairLabel, hsv, hsw, boolPauliConjugationSign]
    · intro hw
      exact False.elim (hw (by simp [Ne.symm hvw]))
  rw [hrest]
  simp [pairLabel]

def localPauliAnticommutingFanLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (j : {j : Fin n // j ≠ firstActivePauliSite P}) :
    Fin n → Option (Fin 3) :=
  pairLabel (firstActivePauliSite P) j.1
    (pauliAxisPrev (firstActivePauliAxis P))
    (matchingPauliAxis (P.1 j.1))

theorem pauliWeight_localPauliAnticommutingFanLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (j : {j : Fin n // j ≠ firstActivePauliSite P}) :
    pauliWeight (localPauliAnticommutingFanLabel P j) = 2 := by
  rw [pauliWeight_eq_card_pauliSupport]
  change (labelSupport (localPauliAnticommutingFanLabel P j)).card = 2
  exact card_labelSupport_pairLabel (Ne.symm j.2) _ _

theorem localPauliAnticommutingFanLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (j : {j : Fin n // j ≠ firstActivePauliSite P}) :
    localPauliAnticommutingFanLabel P j ∈ nonidentityPauliWords n q := by
  rw [mem_nonidentityPauliWords,
    pauliWeight_localPauliAnticommutingFanLabel]
  omega

theorem finitePauliConjugationSign_localPauliAnticommutingFanLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (j : {j : Fin n // j ≠ firstActivePauliSite P}) :
    finitePauliConjugationSign
        (localPauliAnticommutingFanLabel P j) P.1 = -1 := by
  rw [localPauliAnticommutingFanLabel,
    finitePauliConjugationSign_pairLabel P.1 (Ne.symm j.2)]
  rw [← firstActivePauliAxis_spec P,
    boolPauliConjugationSign_prev_source_eq_neg_one,
    boolPauliConjugationSign_matchingPauliAxis]
  norm_num

theorem localPauliAnticommutingFanLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (localPauliAnticommutingFanLabel P) := by
  intro j k hjk
  apply Subtype.ext
  by_contra hne
  have hvalue := congrFun hjk j.1
  have hjfirst : j.1 ≠ firstActivePauliSite P := j.2
  have hkfirst : k.1 ≠ firstActivePauliSite P := k.2
  have hjk' : j.1 ≠ k.1 := by
    intro h
    exact hne h
  simp [localPauliAnticommutingFanLabel, pairLabel,
    hjfirst, hjk'] at hvalue

/-- Every nonidentity Pauli target has at least `n-1` distinct anticommuting
directions already inside the ordinary two-local Pauli ensemble. -/
theorem exists_twoLocalPauliAnticommutingFan
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n)) :
    ∃ f : {j : Fin n // j ≠ firstActivePauliSite P} →
        {Q : Fin n → Option (Fin 3) // Q ∈ nonidentityPauliWords n q},
      Function.Injective f ∧
      ∀ j, finitePauliConjugationSign (f j).1 P.1 = -1 := by
  let f : {j : Fin n // j ≠ firstActivePauliSite P} →
      {Q : Fin n → Option (Fin 3) // Q ∈ nonidentityPauliWords n q} :=
    fun j => ⟨localPauliAnticommutingFanLabel P j,
      localPauliAnticommutingFanLabel_mem hq P j⟩
  refine ⟨f, ?_, ?_⟩
  · intro j k h
    exact localPauliAnticommutingFanLabel_injective P
      (congrArg Subtype.val h)
  · intro j
    exact finitePauliConjugationSign_localPauliAnticommutingFanLabel P j

theorem card_sites_ne_firstActivePauliSite
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Fintype.card {j : Fin n // j ≠ firstActivePauliSite P} = n - 1 := by
  rw [Fintype.card_subtype_compl]
  simp

/-- Counting form: the bounded two-local coefficient set contains at least
`n-1` labels anticommuting with every fixed nonidentity Pauli target. -/
theorem card_filter_twoLocalPauli_anticommuting_ge
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n)) :
    n - 1 ≤
      ((nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1).card := by
  obtain ⟨f, hf, hanti⟩ := exists_twoLocalPauliAnticommutingFan hq P
  rw [← card_sites_ne_firstActivePauliSite P]
  let g : {j : Fin n // j ≠ firstActivePauliSite P} →
      {Q // Q ∈ (nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1} :=
    fun j => ⟨(f j).1, Finset.mem_filter.mpr ⟨(f j).2, hanti j⟩⟩
  have hg : Function.Injective g := by
    intro j k h
    have hraw : (f j).1 = (f k).1 :=
      congrArg (fun z => z.1) h
    exact hf (Subtype.ext hraw)
  have hcard := Fintype.card_le_of_injective g hg
  rw [Fintype.card_coe] at hcard
  exact hcard

end

end GaloisForLFunctions.HTGeometry
