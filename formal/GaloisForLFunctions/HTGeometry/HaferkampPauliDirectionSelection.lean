import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw

/-!
# Fresh Pauli directions for the Haferkamp et al. rank induction

Appendix B of Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern
(2022) chooses a new nonidentity Pauli string at every step of its Clifford
light-cone construction.  This module supplies that finite selection fact and
the resulting independence from the span of all earlier literal Pauli
matrices.  The exact threshold is `4^n - 1`, the number of nonidentity
`n`-qubit Pauli strings.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal `n`-qubit Pauli labels used by the paper's Clifford induction. -/
abbrev HaferkampPauliLabel (n : ℕ) := Fin n → Option (Fin 3)

/-- All nonidentity literal `n`-qubit Pauli labels. -/
def haferkampNonidentityPauliLabels (n : ℕ) : Finset (HaferkampPauliLabel n) :=
  Finset.univ.filter fun P => P ≠ fun _ => none

/-- There are exactly `4^n - 1` nonidentity `n`-qubit Pauli labels. -/
theorem card_haferkampNonidentityPauliLabels (n : ℕ) :
    (haferkampNonidentityPauliLabels n).card = 4 ^ n - 1 := by
  rw [haferkampNonidentityPauliLabels]
  have hfilter :
      (Finset.univ.filter fun P : HaferkampPauliLabel n => P ≠ fun _ => none) =
        (Finset.univ : Finset (HaferkampPauliLabel n)).erase (fun _ => none) := by
    ext P
    simp [Finset.mem_erase]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

/-- A set of fewer than `4^n - 1` Pauli labels omits a nonidentity label. -/
theorem exists_fresh_haferkampNonidentityPauli
    {n : ℕ} (S : Finset (HaferkampPauliLabel n))
    (hS : S.card < 4 ^ n - 1) :
    ∃ P, P ≠ (fun _ => none) ∧ P ∉ S := by
  by_contra h
  push Not at h
  have hsubset : haferkampNonidentityPauliLabels n ⊆ S := by
    intro P hP
    exact h P (Finset.mem_filter.mp hP).2
  have hcard := Finset.card_le_card hsubset
  rw [card_haferkampNonidentityPauliLabels] at hcard
  exact (not_le_of_gt hS) hcard

/-- A literal Pauli matrix outside a selected label set is outside the complex
span of its selected predecessors. -/
theorem finitePauliMatrix_not_mem_span_of_not_mem
    {n : ℕ} {P : HaferkampPauliLabel n} {S : Set (HaferkampPauliLabel n)}
    (hP : P ∉ S) :
    finitePauliMatrix P ∉ Submodule.span ℂ (finitePauliMatrix '' S) := by
  intro hmem
  have hnot := linearIndependent_iff_notMem_span.mp
    (finitePauliMatrix_linearIndependent (σ := Fin n)) P
  apply hnot
  apply Submodule.span_mono ?_ hmem
  rintro _ ⟨Q, hQ, rfl⟩
  refine ⟨Q, ⟨Set.mem_univ Q, ?_⟩, rfl⟩
  simpa only [Set.mem_singleton_iff] using
    (fun hQP : Q = P => hP (hQP ▸ hQ))

/-- The next nonidentity Pauli direction exists and is linearly new whenever
fewer than `4^n - 1` predecessor labels have been selected. -/
theorem exists_fresh_haferkampNonidentityPauli_not_mem_span
    {n : ℕ} (S : Finset (HaferkampPauliLabel n))
    (hS : S.card < 4 ^ n - 1) :
    ∃ P, P ≠ (fun _ => none) ∧
      finitePauliMatrix P ∉
        Submodule.span ℂ (finitePauliMatrix '' (S : Set (HaferkampPauliLabel n))) := by
  obtain ⟨P, hPnonid, hPnot⟩ := exists_fresh_haferkampNonidentityPauli S hS
  exact ⟨P, hPnonid, finitePauliMatrix_not_mem_span_of_not_mem hPnot⟩

end

end GaloisForLFunctions.HTGeometry
