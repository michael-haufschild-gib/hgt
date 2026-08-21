/-
# The bounded-weight Pauli span and the leaf extension

The real span of the nonidentity Pauli strings of weight at most `q` is the coefficient space of the
card's shell ensemble.  Peeling the last qubit turns the three summands of a physical leaf
Hamiltonian -- `H ⊗ 1`, `1 ⊗ (field)` and `(probe) ⊗ (edge)` -- into Pauli strings whose weights are
`wt H`, `1` and `wt(probe) + 1`, so a leaf extension of a weight-`≤1`-probed, weight-`≤2` Hamiltonian
stays weight `≤2`.

Main results:
* `pauliSpan` — the real span of the nonidentity Pauli strings of weight at most `q`.
* `couple_one_mem_pauliSpan` — `H ↦ H ⊗ 1` preserves the span.
* `couple_id_mem_pauliSpan` — a field on the new qubit is weight one.
* `couple_mem_pauliSpan_succ` — a weight-`w` operator coupled to a nonidentity single-qubit factor
  has weight `w+1`.
-/
import GaloisForLFunctions.HTGeometry.QubitSnocPauli

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The real span of the nonidentity Pauli strings of weight at most `q`. -/
def pauliSpan (n q : ℕ) :
    Submodule ℝ (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :=
  Submodule.span ℝ
    {A | ∃ P : Fin n → Option (Fin 3),
      pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n ∧ finitePauliMatrix P = A}

theorem finitePauliMatrix_mem_pauliSpan {n q : ℕ} {P : Fin n → Option (Fin 3)}
    (hw : pauliWeight P ≤ q) (hne : P ≠ pauliIdentityLabel n) :
    finitePauliMatrix P ∈ pauliSpan n q :=
  Submodule.subset_span ⟨P, hw, hne, rfl⟩

theorem pauliSpan_mono {n q q' : ℕ} (h : q ≤ q') : pauliSpan n q ≤ pauliSpan n q' := by
  refine Submodule.span_mono ?_
  rintro A ⟨P, hw, hne, rfl⟩
  exact ⟨P, le_trans hw h, hne, rfl⟩

/-- The coupling-and-reindex map, as a real linear map in its first argument. -/
def coupleSnoc (n : ℕ) (B : Matrix Bool Bool ℂ) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ →ₗ[ℝ]
      Matrix (FiniteQubitConfiguration (Fin (n + 1))) (FiniteQubitConfiguration (Fin (n + 1))) ℂ where
  toFun A := Matrix.reindex (snocConfig n) (snocConfig n) (layerMatrixCoupling A B)
  map_add' A A' := by
    ext x y
    simp [layerMatrixCoupling, add_mul]
  map_smul' c A := by
    ext x y
    simp [layerMatrixCoupling, mul_assoc]

@[simp] theorem coupleSnoc_apply (n : ℕ) (B : Matrix Bool Bool ℂ)
    (A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :
    coupleSnoc n B A = Matrix.reindex (snocConfig n) (snocConfig n) (layerMatrixCoupling A B) :=
  rfl

theorem coupleSnoc_pauli (n : ℕ) (P : Fin n → Option (Fin 3)) (p : Option (Fin 3)) :
    coupleSnoc n (boolPauliOption p) (finitePauliMatrix P) = finitePauliMatrix (Fin.snoc P p) := by
  rw [coupleSnoc_apply, finitePauliMatrix_snoc]

theorem snoc_ne_identity_of_ne {n : ℕ} {P : Fin n → Option (Fin 3)}
    (hne : P ≠ pauliIdentityLabel n) (p : Option (Fin 3)) :
    Fin.snoc P p ≠ pauliIdentityLabel (n + 1) := by
  intro hcon
  apply hne
  funext i
  have := congrFun hcon i.castSucc
  rwa [Fin.snoc_castSucc] at this

theorem snoc_some_ne_identity {n : ℕ} (P : Fin n → Option (Fin 3)) (j : Fin 3) :
    Fin.snoc P (some j) ≠ pauliIdentityLabel (n + 1) := by
  intro hcon
  have := congrFun hcon (Fin.last n)
  rw [Fin.snoc_last] at this
  simp [pauliIdentityLabel] at this

/-- **`H ↦ H ⊗ 1` preserves the bounded-weight span.** -/
theorem couple_one_mem_pauliSpan {n q : ℕ}
    {H : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hH : H ∈ pauliSpan n q) :
    coupleSnoc n (boolPauliOption none) H ∈ pauliSpan (n + 1) q := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hH
  · rintro A ⟨P, hw, hne, rfl⟩
    rw [coupleSnoc_pauli]
    exact finitePauliMatrix_mem_pauliSpan
      (by rw [pauliWeight_snoc_none]; exact hw) (snoc_ne_identity_of_ne hne none)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro A A' _ _ hA hA'
    rw [map_add]
    exact Submodule.add_mem _ hA hA'
  · intro c A _ hA
    rw [map_smul]
    exact Submodule.smul_mem _ c hA

/-- **A field on the new qubit is a weight-one Pauli string.** -/
theorem couple_id_mem_pauliSpan {n q : ℕ} (hq : 1 ≤ q) (j : Fin 3) :
    coupleSnoc n (boolPauliOption (some j))
        (1 : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)
      ∈ pauliSpan (n + 1) q := by
  have hid : finitePauliMatrix (pauliIdentityLabel n)
      = (1 : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) := by
    ext x y
    simp only [finitePauliMatrix, boolPauliOptionEntry, pauliIdentityLabel, boolPauliOption,
      Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [if_neg hxy]
      obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := Function.ne_iff.mp hxy
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      simp [hs]
  rw [← hid, coupleSnoc_pauli]
  refine finitePauliMatrix_mem_pauliSpan ?_ (snoc_some_ne_identity _ j)
  rw [pauliWeight_snoc_some]
  have hzero : pauliWeight (pauliIdentityLabel n) = 0 := by
    simp [pauliWeight, pauliIdentityLabel]
  omega

/-- **Coupling a bounded-weight operator to a nonidentity single-qubit factor raises the weight by
one.** -/
theorem couple_mem_pauliSpan_succ {n q : ℕ}
    {V : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hV : V ∈ pauliSpan n q) (j : Fin 3) :
    coupleSnoc n (boolPauliOption (some j)) V ∈ pauliSpan (n + 1) (q + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hV
  · rintro A ⟨P, hw, hne, rfl⟩
    rw [coupleSnoc_pauli]
    refine finitePauliMatrix_mem_pauliSpan ?_ (snoc_some_ne_identity _ j)
    rw [pauliWeight_snoc_some]
    omega
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro A A' _ _ hA hA'
    rw [map_add]
    exact Submodule.add_mem _ hA hA'
  · intro c A _ hA
    rw [map_smul]
    exact Submodule.smul_mem _ c hA

end GaloisForLFunctions.HTGeometry

end
