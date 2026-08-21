/-
# Splitting the last qubit off a Pauli string

The Pauli string of a finite qubit register is a *product over sites* of single-qubit entries, so
peeling the last site is an entrywise identity rather than a tensor-algebra construction: a Pauli
string on `n+1` qubits is the layer coupling of its restriction to the first `n` with its last
single-qubit factor, read through the snoc equivalence of configurations.

Main results:
* `snocConfig` — the configuration equivalence `(Fin n → Bool) × Bool ≃ (Fin (n+1) → Bool)`.
* `finitePauliMatrix_snoc` — **the Pauli string splits as a layer coupling**.
* `pauliWeight_snoc_none`, `pauliWeight_snoc_some` — how the weight changes.
-/
import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels
import GaloisForLFunctions.HTGeometry.LocalExtensionMatrixChart

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The configuration equivalence peeling the last qubit. -/
def snocConfig (n : ℕ) :
    FiniteQubitConfiguration (Fin n) × Bool ≃ FiniteQubitConfiguration (Fin (n + 1)) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool))

@[simp] theorem snocConfig_apply (n : ℕ) (c : FiniteQubitConfiguration (Fin n)) (b : Bool) :
    snocConfig n (c, b) = Fin.snoc c b := rfl

@[simp] theorem snocConfig_symm_apply (n : ℕ) (x : FiniteQubitConfiguration (Fin (n + 1))) :
    (snocConfig n).symm x = (Fin.init x, x (Fin.last n)) := rfl

/-- **A Pauli string splits as a layer coupling of its head and its last factor.** -/
theorem finitePauliMatrix_snoc {n : ℕ} (P : Fin n → Option (Fin 3)) (p : Option (Fin 3)) :
    finitePauliMatrix (Fin.snoc P p)
      = Matrix.reindex (snocConfig n) (snocConfig n)
          (layerMatrixCoupling (finitePauliMatrix P) (boolPauliOption p)) := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, layerMatrixCoupling,
    snocConfig_symm_apply, finitePauliMatrix, boolPauliOptionEntry]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.snoc_castSucc]
    rfl
  · rw [Fin.snoc_last]

theorem pauliWeight_snoc_none {n : ℕ} (P : Fin n → Option (Fin 3)) :
    pauliWeight (Fin.snoc P none) = pauliWeight P := by
  classical
  simp only [pauliWeight, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem pauliWeight_snoc_some {n : ℕ} (P : Fin n → Option (Fin 3)) (q : Fin 3) :
    pauliWeight (Fin.snoc P (some q)) = pauliWeight P + 1 := by
  classical
  simp only [pauliWeight, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

end GaloisForLFunctions.HTGeometry

end
