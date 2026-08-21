/-
# Transporting the two-qubit graph seed to the Pauli register

The corpus's endpoint-complete two-qubit seed lives on `Bool × Bool`; the card's ensemble lives on
`FiniteQubitConfiguration (Fin 2)`.  The two are the same register through the snoc equivalence, and
under it the seed's one-site endpoint probe is literally a weight-one Pauli string at the last
qubit.  A unitary conjugate of a zero-sum diagonal is traceless, so the recentred seed Hamiltonian
lands in the bounded-weight Pauli span.

Main results:
* `trace_unitary_conj_diagonal` — the trace of `U diag(E) Uᴴ` is `∑ E`.
* `boolPauli_eq_boolPauliOption` — the two single-qubit Pauli namings agree.
* `twoQubitConfigEquiv` — `Bool × Bool ≃ FiniteQubitConfiguration (Fin 2)`.
* `reindex_twoQubitConfigEquiv_layerMatrixCoupling_one` — a one-site operator at the second factor
  is the corresponding weight-one Pauli string.
* `endpointProbe_mem_pauliSpan` — **the seed's endpoint probe is in the weight-one Pauli span**.
-/
import GaloisForLFunctions.HTGeometry.PauliBoundedWeightSpan
import GaloisForLFunctions.HTGeometry.PhysicalTwoQubitGraphSeed

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The trace of a unitary conjugate of a diagonal is the sum of the diagonal. -/
theorem trace_unitary_conj_diagonal {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {U : Matrix β α ℂ} (hU : Uᴴ * U = 1) (E : α → ℂ) :
    (U * Matrix.diagonal E * Uᴴ).trace = ∑ i, E i := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

theorem boolPauli_eq_boolPauliOption (q : Fin 3) : boolPauli q = boolPauliOption (some q) := rfl

/-- The single-qubit configuration equivalence. -/
def oneQubitConfigEquiv : Bool ≃ FiniteQubitConfiguration (Fin 1) :=
  (Equiv.funUnique (Fin 1) Bool).symm

/-- The two-qubit configuration equivalence. -/
def twoQubitConfigEquiv : Bool × Bool ≃ FiniteQubitConfiguration (Fin 2) :=
  (Equiv.prodCongr oneQubitConfigEquiv (Equiv.refl Bool)).trans (snocConfig 1)

theorem reindex_prodCongr_layerMatrixCoupling (A B : Matrix Bool Bool ℂ) :
    Matrix.reindex (Equiv.prodCongr oneQubitConfigEquiv (Equiv.refl Bool))
        (Equiv.prodCongr oneQubitConfigEquiv (Equiv.refl Bool)) (layerMatrixCoupling A B)
      = layerMatrixCoupling (Matrix.reindex oneQubitConfigEquiv oneQubitConfigEquiv A) B := by
  ext x y
  rfl

theorem reindex_oneQubitConfigEquiv_one :
    Matrix.reindex oneQubitConfigEquiv oneQubitConfigEquiv (1 : Matrix Bool Bool ℂ)
      = (1 : Matrix (FiniteQubitConfiguration (Fin 1)) (FiniteQubitConfiguration (Fin 1)) ℂ) := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    simp
  · rw [if_neg h, if_neg fun hcon => h (oneQubitConfigEquiv.symm.injective hcon)]

/-- **A one-site operator at the second factor is the corresponding weight-one Pauli string.** -/
theorem reindex_twoQubitConfigEquiv_layerMatrixCoupling_one (B : Matrix Bool Bool ℂ) :
    Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
        (layerMatrixCoupling (1 : Matrix Bool Bool ℂ) B)
      = coupleSnoc 1 B
          (1 : Matrix (FiniteQubitConfiguration (Fin 1)) (FiniteQubitConfiguration (Fin 1)) ℂ) := by
  have hsplit : Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv
      (layerMatrixCoupling (1 : Matrix Bool Bool ℂ) B)
      = Matrix.reindex (snocConfig 1) (snocConfig 1)
        (Matrix.reindex (Equiv.prodCongr oneQubitConfigEquiv (Equiv.refl Bool))
          (Equiv.prodCongr oneQubitConfigEquiv (Equiv.refl Bool))
          (layerMatrixCoupling (1 : Matrix Bool Bool ℂ) B)) := by
    ext x y
    rfl
  rw [hsplit, reindex_prodCongr_layerMatrixCoupling, reindex_oneQubitConfigEquiv_one,
    coupleSnoc_apply]

/-- **The seed's endpoint probe is a weight-one Pauli string.** -/
theorem endpointProbe_mem_pauliSpan {q₀ : ℕ} (hq : 1 ≤ q₀) (q : Fin 3) :
    Matrix.reindex twoQubitConfigEquiv twoQubitConfigEquiv (twoQubitEndpointProbe true q)
      ∈ pauliSpan 2 q₀ := by
  have hprobe : twoQubitEndpointProbe true q
      = layerMatrixCoupling (1 : Matrix Bool Bool ℂ) (boolPauliOption (some q)) := by
    rw [twoQubitEndpointProbe, if_neg (by simp), boolPauli_eq_boolPauliOption]
  rw [hprobe, reindex_twoQubitConfigEquiv_layerMatrixCoupling_one]
  exact couple_id_mem_pauliSpan hq q

end GaloisForLFunctions.HTGeometry

end
