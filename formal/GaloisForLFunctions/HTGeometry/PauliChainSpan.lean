/-
# The chain Pauli span

The nearest-neighbour Pauli family of an open qubit path consists of the strings supported on one
site and the strings supported on one edge, that is exactly the nonidentity strings whose support
has diameter at most one.  Peeling the last qubit takes such a string to another one, and takes a
string supported at the previous endpoint, coupled to a nonidentity factor on the new site, to a
string supported on the new edge.

Main results:
* `pauliLabelSpan` — the real span of the nonidentity Pauli strings with a prescribed label
  property, and its coupling law `coupleSnoc_mem_pauliLabelSpan`.
* `pauliChainSpan`, `pauliSiteSpan` — the chain family and the one-site families.
* `pauliSpan_two_le_pauliChainSpan` — on two qubits the chain span is the whole two-local span.
* `couple_one_mem_pauliChainSpan`, `couple_one_mem_pauliSiteSpan`,
  `couple_field_mem_pauliSiteSpan`, `couple_last_mem_pauliChainSpan` — the four coupling laws the
  leaf extension needs.
-/
import GaloisForLFunctions.HTGeometry.PauliBoundedWeightSpan

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The real span of the nonidentity Pauli strings whose label satisfies `L`. -/
def pauliLabelSpan (n : ℕ) (L : (Fin n → Option (Fin 3)) → Prop) :
    Submodule ℝ (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :=
  Submodule.span ℝ
    {A | ∃ P : Fin n → Option (Fin 3),
      L P ∧ P ≠ pauliIdentityLabel n ∧ finitePauliMatrix P = A}

theorem finitePauliMatrix_mem_pauliLabelSpan {n : ℕ} {L : (Fin n → Option (Fin 3)) → Prop}
    {P : Fin n → Option (Fin 3)} (hL : L P) (hne : P ≠ pauliIdentityLabel n) :
    finitePauliMatrix P ∈ pauliLabelSpan n L :=
  Submodule.subset_span ⟨P, hL, hne, rfl⟩

theorem pauliLabelSpan_mono {n : ℕ} {L L' : (Fin n → Option (Fin 3)) → Prop}
    (h : ∀ P, L P → L' P) : pauliLabelSpan n L ≤ pauliLabelSpan n L' := by
  refine Submodule.span_mono ?_
  rintro A ⟨P, hL, hne, rfl⟩
  exact ⟨P, h P hL, hne, rfl⟩

theorem trace_eq_zero_of_mem_pauliLabelSpan {n : ℕ} {L : (Fin n → Option (Fin 3)) → Prop}
    {A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hA : A ∈ pauliLabelSpan n L) : A.trace = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro B ⟨P, -, hne, rfl⟩
    exact finitePauliMatrix_trace_eq_zero_of_ne_identity P hne
  · exact Matrix.trace_zero _ _
  · intro B B' _ _ hB hB'
    rw [Matrix.trace_add, hB, hB', add_zero]
  · intro c B _ hB
    rw [Matrix.trace_smul, hB, smul_zero]

/-- **The coupling law of a label-property span.**  If snoccing the local factor `p` carries the
property `L` to the property `L'`, then it carries the span to the span. -/
theorem coupleSnoc_mem_pauliLabelSpan {n : ℕ} {L : (Fin n → Option (Fin 3)) → Prop}
    {L' : (Fin (n + 1) → Option (Fin 3)) → Prop} (p : Option (Fin 3))
    (hstep : ∀ P, L P → P ≠ pauliIdentityLabel n → L' (Fin.snoc P p))
    (hid : ∀ P : Fin n → Option (Fin 3), P ≠ pauliIdentityLabel n →
      Fin.snoc P p ≠ pauliIdentityLabel (n + 1))
    {A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hA : A ∈ pauliLabelSpan n L) :
    coupleSnoc n (boolPauliOption p) A ∈ pauliLabelSpan (n + 1) L' := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro B ⟨P, hL, hne, rfl⟩
    rw [coupleSnoc_pauli]
    exact finitePauliMatrix_mem_pauliLabelSpan (hstep P hL hne) (hid P hne)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro B B' _ _ hB hB'
    rw [map_add]
    exact Submodule.add_mem _ hB hB'
  · intro c B _ hB
    rw [map_smul]
    exact Submodule.smul_mem _ c hB

/-! ## Chain labels and site labels -/

/-- A label whose support has diameter at most one: one site, or one edge of the open path. -/
def IsChainLabel {n : ℕ} (P : Fin n → Option (Fin 3)) : Prop :=
  ∀ i j : Fin n, P i ≠ none → P j ≠ none → (i : ℕ) ≤ (j : ℕ) + 1

/-- A label supported at the single site `s`. -/
def IsSiteLabel {n : ℕ} (s : Fin n) (P : Fin n → Option (Fin 3)) : Prop :=
  ∀ i : Fin n, P i ≠ none → i = s

theorem isChainLabel_of_isSiteLabel {n : ℕ} {s : Fin n} {P : Fin n → Option (Fin 3)}
    (h : IsSiteLabel s P) : IsChainLabel P := by
  intro i j hi hj
  rw [h i hi, h j hj]
  omega

/-- The real span of the nearest-neighbour Pauli strings of an open qubit path. -/
def pauliChainSpan (n : ℕ) :
    Submodule ℝ (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :=
  pauliLabelSpan n IsChainLabel

/-- The real span of the Pauli strings supported at a single site. -/
def pauliSiteSpan (n : ℕ) (s : Fin n) :
    Submodule ℝ (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :=
  pauliLabelSpan n (IsSiteLabel s)

theorem pauliSiteSpan_le_pauliChainSpan (n : ℕ) (s : Fin n) :
    pauliSiteSpan n s ≤ pauliChainSpan n :=
  pauliLabelSpan_mono fun _ h => isChainLabel_of_isSiteLabel h

theorem trace_eq_zero_of_mem_pauliChainSpan {n : ℕ}
    {A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hA : A ∈ pauliChainSpan n) : A.trace = 0 :=
  trace_eq_zero_of_mem_pauliLabelSpan hA

theorem trace_eq_zero_of_mem_pauliSiteSpan {n : ℕ} {s : Fin n}
    {A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hA : A ∈ pauliSiteSpan n s) : A.trace = 0 :=
  trace_eq_zero_of_mem_pauliLabelSpan hA

/-- On two qubits every label is a chain label: the whole two-local span is the chain span. -/
theorem pauliSpan_two_le_pauliChainSpan (q : ℕ) : pauliSpan 2 q ≤ pauliChainSpan 2 := by
  refine pauliLabelSpan_mono ?_
  intro P _ i j _ _
  have hi := i.isLt
  have hj := j.isLt
  omega

/-! ## Snoccing a label -/

theorem snoc_none_support {n : ℕ} (P : Fin n → Option (Fin 3)) {i : Fin (n + 1)}
    (hi : (Fin.snoc P none : Fin (n + 1) → Option (Fin 3)) i ≠ none) :
    ∃ i' : Fin n, i = i'.castSucc ∧ P i' ≠ none := by
  refine Fin.lastCases ?_ ?_ i hi
  · intro hlast
    rw [Fin.snoc_last] at hlast
    exact absurd rfl hlast
  · intro i' hi'
    rw [Fin.snoc_castSucc] at hi'
    exact ⟨i', rfl, hi'⟩

theorem snoc_some_support {n : ℕ} (P : Fin n → Option (Fin 3)) (q : Fin 3) {i : Fin (n + 1)}
    (hi : (Fin.snoc P (some q) : Fin (n + 1) → Option (Fin 3)) i ≠ none) :
    i = Fin.last n ∨ ∃ i' : Fin n, i = i'.castSucc ∧ P i' ≠ none := by
  refine Fin.lastCases ?_ ?_ i hi
  · intro _
    exact Or.inl rfl
  · intro i' hi'
    rw [Fin.snoc_castSucc] at hi'
    exact Or.inr ⟨i', rfl, hi'⟩

/-! ## The four coupling laws -/

/-- **`H ↦ H ⊗ 1` preserves the chain span.** -/
theorem couple_one_mem_pauliChainSpan {n : ℕ}
    {H : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hH : H ∈ pauliChainSpan n) :
    coupleSnoc n (boolPauliOption none) H ∈ pauliChainSpan (n + 1) := by
  refine coupleSnoc_mem_pauliLabelSpan none ?_ (fun P hne => snoc_ne_identity_of_ne hne none) hH
  intro P hL _ i j hi hj
  obtain ⟨i', rfl, hi'⟩ := snoc_none_support P hi
  obtain ⟨j', rfl, hj'⟩ := snoc_none_support P hj
  simpa using hL i' j' hi' hj'

/-- **`V ↦ V ⊗ 1` preserves a one-site span.** -/
theorem couple_one_mem_pauliSiteSpan {n : ℕ} {s : Fin n}
    {V : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hV : V ∈ pauliSiteSpan n s) :
    coupleSnoc n (boolPauliOption none) V ∈ pauliSiteSpan (n + 1) s.castSucc := by
  refine coupleSnoc_mem_pauliLabelSpan none ?_ (fun P hne => snoc_ne_identity_of_ne hne none) hV
  intro P hL _ i hi
  obtain ⟨i', rfl, hi'⟩ := snoc_none_support P hi
  rw [hL i' hi']

/-- **A field on the new qubit is a one-site string at the new site.** -/
theorem couple_field_mem_pauliSiteSpan (n : ℕ) (q : Fin 3) :
    coupleSnoc n (boolPauliOption (some q))
        (1 : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)
      ∈ pauliSiteSpan (n + 1) (Fin.last n) := by
  have hid : (1 : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) = finitePauliMatrix (pauliIdentityLabel n) :=
      by
    ext x y
    rw [finitePauliMatrix_pauliIdentityLabel]
    simp [Matrix.one_apply]
  rw [hid, coupleSnoc_pauli]
  refine finitePauliMatrix_mem_pauliLabelSpan ?_ (snoc_some_ne_identity _ q)
  intro i hi
  rcases snoc_some_support _ q hi with h | ⟨i', -, hi'⟩
  · exact h
  · exact absurd rfl hi'

/-- **Coupling the previous endpoint to a nonidentity factor on the new site gives a string
supported on the new edge.** -/
theorem couple_last_mem_pauliChainSpan {m : ℕ} (q : Fin 3)
    {V : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
      (FiniteQubitConfiguration (Fin (m + 1))) ℂ}
    (hV : V ∈ pauliSiteSpan (m + 1) (Fin.last m)) :
    coupleSnoc (m + 1) (boolPauliOption (some q)) V ∈ pauliChainSpan (m + 2) := by
  refine coupleSnoc_mem_pauliLabelSpan (some q) ?_
    (fun P _ => snoc_some_ne_identity P q) hV
  intro P hL _ i j hi hj
  have hval : ∀ x : Fin (m + 2),
      (Fin.snoc P (some q) : Fin (m + 2) → Option (Fin 3)) x ≠ none →
      (x : ℕ) = m ∨ (x : ℕ) = m + 1 := by
    intro x hx
    rcases snoc_some_support P q hx with h | ⟨x', rfl, hx'⟩
    · exact Or.inr (by rw [h]; rfl)
    · left
      rw [hL x' hx']
      rfl
  rcases hval i hi with h1 | h1 <;> rcases hval j hj with h2 | h2 <;> omega

end GaloisForLFunctions.HTGeometry

end
