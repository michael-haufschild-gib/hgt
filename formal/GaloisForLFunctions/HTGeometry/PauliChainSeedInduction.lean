/-
# The Pauli-path induction

Iterating the leaf extension from the two-qubit seed produces, on every number of qubits at least
two, a nearest-neighbour Pauli Hamiltonian with maximally projective zero-sum spectrum together
with a one-site endpoint probe whose spectral matrix has no vanishing off-diagonal entry.

Main results:
* `seedIndex` — the spectral index type of the `k`-th stage, with its cardinality `2^(k+2)`.
* `exists_pauliChainSeed` — **the endpoint-complete nearest-neighbour Pauli seed at every size**.
-/
import GaloisForLFunctions.HTGeometry.PauliSeedExtension

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The spectral index type of the `k`-th stage of the Pauli-path induction. -/
def seedIndex : ℕ → Type
  | 0 => Bool × Bool
  | k + 1 => seedIndex k × Bool

instance seedIndexFintype : ∀ k, Fintype (seedIndex k)
  | 0 => inferInstanceAs (Fintype (Bool × Bool))
  | k + 1 => letI := seedIndexFintype k; inferInstanceAs (Fintype (seedIndex k × Bool))

instance seedIndexDecidableEq : ∀ k, DecidableEq (seedIndex k)
  | 0 => inferInstanceAs (DecidableEq (Bool × Bool))
  | k + 1 => letI := seedIndexDecidableEq k; inferInstanceAs (DecidableEq (seedIndex k × Bool))

instance seedIndexInhabited : ∀ k, Inhabited (seedIndex k)
  | 0 => inferInstanceAs (Inhabited (Bool × Bool))
  | k + 1 => letI := seedIndexInhabited k; inferInstanceAs (Inhabited (seedIndex k × Bool))

instance seedIndexNonempty (k : ℕ) : Nonempty (seedIndex k) := ⟨default⟩

theorem card_seedIndex : ∀ k : ℕ, Fintype.card (seedIndex k) = 2 ^ (k + 2)
  | 0 => by
      show Fintype.card (Bool × Bool) = 2 ^ 2
      simp
  | k + 1 => by
      show Fintype.card (seedIndex k × Bool) = 2 ^ (k + 3)
      rw [Fintype.card_prod, Fintype.card_bool, card_seedIndex k]
      ring

theorem three_le_card_seedIndex (k : ℕ) : 3 ≤ Fintype.card (seedIndex k) := by
  rw [card_seedIndex k]
  calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The endpoint-complete nearest-neighbour Pauli seed at every size.** -/
theorem exists_pauliChainSeed : ∀ k : ℕ,
    ∃ (E : seedIndex k → ℝ)
      (U : Matrix (FiniteQubitConfiguration (Fin (k + 2))) (seedIndex k) ℂ)
      (V : Matrix (FiniteQubitConfiguration (Fin (k + 2)))
        (FiniteQubitConfiguration (Fin (k + 2))) ℂ),
      MaximallyProjectiveEnergy E ∧ (∑ i, E i) = 0 ∧
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      V.IsHermitian ∧ V ∈ pauliSiteSpan (k + 2) (Fin.last (k + 1)) ∧
      (U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ) ∈ pauliChainSpan (k + 2) ∧
      (∀ a b : seedIndex k, a ≠ b → (Uᴴ * V * U) a b ≠ 0)
  | 0 => exists_twoQubit_pauliSeed
  | k + 1 => by
      obtain ⟨E, U, V, hEmax, hEsum, hUleft, hUright, hVherm, hVspan, hHspan, hVtrans⟩ :=
        exists_pauliChainSeed k
      exact exists_pauliSeed_succ (three_le_card_seedIndex k) hEmax hUleft hUright
        hVherm hVspan hHspan hVtrans

end GaloisForLFunctions.HTGeometry

end
