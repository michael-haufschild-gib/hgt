import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitArchitecture

/-!
# Exact two-qubit circuit complexity

This module packages the paper's exact unitary circuit complexity on a finite
qubit register.  A circuit is a concrete fixed architecture together with one
`SU(4)` parameter per ordered location.  Complexity is the infimum of gate
counts among circuits whose contraction is exactly the target; it is `⊤` when
no such circuit exists.  The accompanying characterization is the form used
by all later lower bounds.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One concrete exact two-qubit circuit on an `n`-qubit Boolean register. -/
structure TwoQubitCircuit (n : ℕ) where
  gateCount : ℕ
  architecture : TwoQubitArchitecture n gateCount
  gates : Fin gateCount → Matrix.specialUnitaryGroup (Bool × Bool) ℂ

namespace TwoQubitCircuit

/-- Global unitary implemented by a concrete circuit. -/
def eval {n : ℕ} (C : TwoQubitCircuit n) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  C.architecture.contraction C.gates

end TwoQubitCircuit

/-- Exact two-qubit circuit complexity of a unitary.  The inner infimum is
over equality witnesses, so a gate count without an exact implementation does
not contribute to the infimum. -/
noncomputable def exactTwoQubitCircuitComplexity (n : ℕ)
    (U : Matrix.unitaryGroup (Fin n → Bool) ℂ) : ℕ∞ :=
  ⨅ C : TwoQubitCircuit n, ⨅ _h : C.eval = U, (C.gateCount : ℕ∞)

/-- Every explicit circuit witnesses the corresponding upper bound on exact
circuit complexity. -/
theorem exactTwoQubitCircuitComplexity_le_gateCount
    {n : ℕ} (C : TwoQubitCircuit n) :
    exactTwoQubitCircuitComplexity n C.eval ≤ (C.gateCount : ℕ∞) := by
  refine le_trans (iInf_le _ C) ?_
  exact iInf_le (fun _h : C.eval = C.eval => (C.gateCount : ℕ∞)) rfl

/-- A lower bound on exact circuit complexity is exactly a lower bound on
every concrete circuit that implements the target. -/
theorem le_exactTwoQubitCircuitComplexity_iff
    {n : ℕ} (U : Matrix.unitaryGroup (Fin n → Bool) ℂ) (s : ℕ∞) :
    s ≤ exactTwoQubitCircuitComplexity n U ↔
      ∀ C : TwoQubitCircuit n, C.eval = U → s ≤ (C.gateCount : ℕ∞) := by
  constructor
  · intro h C hC
    rw [exactTwoQubitCircuitComplexity, le_iInf_iff] at h
    exact le_iInf_iff.mp (h C) hC
  · intro h
    rw [exactTwoQubitCircuitComplexity, le_iInf_iff]
    intro C
    rw [le_iInf_iff]
    intro hC
    exact h C hC

end

end GaloisForLFunctions.HTGeometry
