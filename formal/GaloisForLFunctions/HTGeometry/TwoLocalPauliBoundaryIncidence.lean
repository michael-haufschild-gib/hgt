import GaloisForLFunctions.HTGeometry.TwoLocalPauliAnticommutingFan

/-!
# Boundary lower bound for two-local Pauli strings anticommuting with a given string

Let `P` be a nonzero Pauli string on `n` qubits with support of size `|P|`. For each pair
`(i, j)` with `i` in the support and `j` outside it, the weight-two string with axis `prev(P_i)` at
`i` and axis `0` at `j` anticommutes with `P`: it anticommutes at site `i` and commutes at the
idle site `j`. These strings are pairwise distinct, so at least `|P| (n - |P|)` nonidentity Pauli
strings of weight at most `q ≥ 2` anticommute with `P`.

## Main results

- `card_filter_twoLocalPauli_anticommuting_ge_boundary`: for `2 ≤ q`, the number of nonidentity
  Pauli strings of weight at most `q` anticommuting with `P` is at least `|P| (n - |P|)`.
- `boundaryPauliAnticommutingLabel_injective`: the boundary construction is injective on
  support-boundary pairs.

## Hypotheses

Unconditional; the only premise is `2 ≤ q`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pairs `(i, j)` with `i` in the support of `P` and `j` outside it. -/
abbrev PauliSupportBoundaryPair
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :=
  {i : Fin n // i ∈ pauliSupport P.1} ×
    {j : Fin n // j ∉ pauliSupport P.1}

theorem pauliSupportBoundaryPair_ne
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliSupportBoundaryPair P) : z.1.1 ≠ z.2.1 := by
  intro h
  exact z.2.2 (h ▸ z.1.2)

/-- The weight-two string with axis `prev(P_i)` at `i` and axis `0` at `j`. -/
def boundaryPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliSupportBoundaryPair P) :
    Fin n → Option (Fin 3) :=
  pairLabel z.1.1 z.2.1
    (pauliAxisPrev (matchingPauliAxis (P.1 z.1.1))) 0

/-- The boundary string has Pauli weight exactly two. -/
theorem pauliWeight_boundaryPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliSupportBoundaryPair P) :
    pauliWeight (boundaryPauliAnticommutingLabel P z) = 2 := by
  rw [pauliWeight_eq_card_pauliSupport]
  change (labelSupport (boundaryPauliAnticommutingLabel P z)).card = 2
  exact card_labelSupport_pairLabel (pauliSupportBoundaryPair_ne P z) _ _

theorem boundaryPauliAnticommutingLabel_mem
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n))
    (z : PauliSupportBoundaryPair P) :
    boundaryPauliAnticommutingLabel P z ∈ nonidentityPauliWords n q := by
  rw [mem_nonidentityPauliWords,
    pauliWeight_boundaryPauliAnticommutingLabel]
  omega

/-- The boundary string anticommutes with `P` (conjugation sign `-1`). -/
theorem finitePauliConjugationSign_boundaryPauliAnticommutingLabel
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (z : PauliSupportBoundaryPair P) :
    finitePauliConjugationSign
        (boundaryPauliAnticommutingLabel P z) P.1 = -1 := by
  rw [boundaryPauliAnticommutingLabel,
    finitePauliConjugationSign_pairLabel P.1
      (pauliSupportBoundaryPair_ne P z)]
  have hi : P.1 z.1.1 ≠ none := mem_pauliSupport.mp z.1.2
  have hj : P.1 z.2.1 = none := by
    by_contra h
    exact z.2.2 (mem_pauliSupport.mpr h)
  cases hpi : P.1 z.1.1 with
  | none => exact (hi hpi).elim
  | some a =>
      simp only [matchingPauliAxis]
      rw [boolPauliConjugationSign_prev_source_eq_neg_one]
      simp [hj, boolPauliConjugationSign]

/-- Distinct support-boundary pairs give distinct boundary strings. -/
theorem boundaryPauliAnticommutingLabel_injective
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Function.Injective (boundaryPauliAnticommutingLabel P) := by
  intro z w hzw
  have hi : z.1.1 = w.1.1 := by
    by_contra hne
    have hiw2 : z.1.1 ≠ w.2.1 := by
      intro h
      exact w.2.2 (h ▸ z.1.2)
    have hvalue := congrFun hzw z.1.1
    have hzij : z.1.1 ≠ z.2.1 := pauliSupportBoundaryPair_ne P z
    simp [boundaryPauliAnticommutingLabel, pairLabel,
      hne, hiw2] at hvalue
  have hj : z.2.1 = w.2.1 := by
    by_contra hne
    have hz2i : z.2.1 ≠ z.1.1 := Ne.symm (pauliSupportBoundaryPair_ne P z)
    have hz2w1 : z.2.1 ≠ w.1.1 := by simpa [hi] using hz2i
    have hvalue := congrFun hzw z.2.1
    simp [boundaryPauliAnticommutingLabel, pairLabel,
      hz2i, hz2w1, hne] at hvalue
  exact Prod.ext (Subtype.ext hi) (Subtype.ext hj)

/-- There are `|P| (n - |P|)` support-boundary pairs. -/
theorem card_pauliSupportBoundaryPair
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    Fintype.card (PauliSupportBoundaryPair P) =
      pauliWeight P.1 * (n - pauliWeight P.1) := by
  rw [Fintype.card_prod, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe,
    ← pauliWeight_eq_card_pauliSupport]

/-- For `2 ≤ q`, at least `|P| (n - |P|)` nonidentity Pauli strings of weight at most `q`
anticommute with the nonzero string `P`. -/
theorem card_filter_twoLocalPauli_anticommuting_ge_boundary
    {n q : ℕ} (hq : 2 ≤ q)
    (P : NonzeroPauliCharacter (Fin n)) :
    pauliWeight P.1 * (n - pauliWeight P.1) ≤
      ((nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1).card := by
  rw [← card_pauliSupportBoundaryPair P]
  let f : PauliSupportBoundaryPair P →
      {Q // Q ∈ (nonidentityPauliWords n q).filter fun Q =>
        finitePauliConjugationSign Q P.1 = -1} :=
    fun z => ⟨boundaryPauliAnticommutingLabel P z,
      Finset.mem_filter.mpr
        ⟨boundaryPauliAnticommutingLabel_mem hq P z,
          finitePauliConjugationSign_boundaryPauliAnticommutingLabel P z⟩⟩
  have hf : Function.Injective f := by
    intro z w h
    apply boundaryPauliAnticommutingLabel_injective P
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_coe] at hcard

end

end GaloisForLFunctions.HTGeometry
