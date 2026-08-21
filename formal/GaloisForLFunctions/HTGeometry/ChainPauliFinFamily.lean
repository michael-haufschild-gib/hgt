/-
# The nearest-neighbour Pauli family in numbered coordinates

The card's interaction family is the set of nonidentity Pauli strings supported on one site or on
one edge of the open path.  Numbering those labels and transporting the register to `Fin (2^n)`
puts the family in the shape the shell machinery consumes: a finite Hermitian family indexed by
`Fin m` acting on `Fin D`, orthonormal in the Hilbert--Schmidt pairing up to the factor `D`.

Main results:
* `chainPauliFin` — the numbered nearest-neighbour Pauli family.
* `trace_chainPauliFin_mul` — its Hilbert--Schmidt orthogonality.
* `reindexFin_mem_span_range_chainPauliFin` — the chain span is the real span of the family.
-/
import GaloisForLFunctions.HTGeometry.PauliChainSpan
import GaloisForLFunctions.HTGeometry.PauliCommutatorCoefficient

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The computational register of `n` qubits, numbered. -/
def qubitConfigFin (n : ℕ) : FiniteQubitConfiguration (Fin n) ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by simp [FiniteQubitConfiguration])

/-- A nearest-neighbour Pauli label of an open path of `n` qubits. -/
def ChainLabel (n : ℕ) : Type :=
  {P : Fin n → Option (Fin 3) // IsChainLabel P ∧ P ≠ pauliIdentityLabel n}

instance (n : ℕ) : DecidableEq (ChainLabel n) := Subtype.instDecidableEq

instance (n : ℕ) : Fintype (ChainLabel n) := by
  classical
  exact Subtype.fintype _

/-- The numbered nearest-neighbour Pauli family. -/
def chainPauliFin (n : ℕ) (a : Fin (Fintype.card (ChainLabel n))) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (qubitConfigFin n) (qubitConfigFin n)
    (finitePauliMatrix ((Fintype.equivFin (ChainLabel n)).symm a).1)

theorem chainPauliFin_isHermitian (n : ℕ) (a : Fin (Fintype.card (ChainLabel n))) :
    (chainPauliFin n a).IsHermitian :=
  (finitePauliMatrix_isHermitian _).submatrix _

theorem trace_reindex_qubitConfigFin {n : ℕ}
    (X : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :
    (Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact Equiv.sum_comp (qubitConfigFin n).symm
    (fun i : FiniteQubitConfiguration (Fin n) => X i i)

theorem reindex_qubitConfigFin_mul {n : ℕ}
    (X Y : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ) :
    Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) X *
        Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) Y
      = Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) (X * Y) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv X Y (qubitConfigFin n).symm (qubitConfigFin n).symm
      (qubitConfigFin n).symm]

/-- **The numbered family is Hilbert--Schmidt orthogonal**, with squared norm `2^n`. -/
theorem trace_chainPauliFin_mul (n : ℕ) (a b : Fin (Fintype.card (ChainLabel n))) :
    (chainPauliFin n a * chainPauliFin n b).trace
      = if a = b then (((2 ^ n : ℝ)) : ℂ) else 0 := by
  rw [chainPauliFin, chainPauliFin, reindex_qubitConfigFin_mul, trace_reindex_qubitConfigFin,
    trace_pauli_mul]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl]
    simp
  · rw [if_neg hab, if_neg]
    intro hcon
    exact hab ((Fintype.equivFin (ChainLabel n)).symm.injective (Subtype.ext hcon))

/-- **The chain span is the real span of the numbered family.** -/
theorem reindexFin_mem_span_range_chainPauliFin {n : ℕ}
    {A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hA : A ∈ pauliChainSpan n) :
    Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) A
      ∈ Submodule.span ℝ (Set.range (chainPauliFin n)) := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro B ⟨P, hL, hne, rfl⟩
    refine Submodule.subset_span ⟨Fintype.equivFin (ChainLabel n) ⟨P, hL, hne⟩, ?_⟩
    rw [chainPauliFin, Equiv.symm_apply_apply]
  · exact Submodule.zero_mem _
  · intro B B' _ _ hB hB'
    have hadd : Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) (B + B')
        = Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) B
          + Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) B' := by
      ext x y; rfl
    rw [hadd]
    exact Submodule.add_mem _ hB hB'
  · intro c B _ hB
    have hsmul : Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) (c • B)
        = c • Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) B := by
      ext x y; rfl
    rw [hsmul]
    exact Submodule.smul_mem _ c hB

end GaloisForLFunctions.HTGeometry

end
