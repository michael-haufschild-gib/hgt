import GaloisForLFunctions.HTGeometry.TracelessLocalPauliTransferConservationLaw

/-!
# Tracelessness is exactly the vanishing identity Pauli coordinate

Expanding a self-adjoint matrix in the Pauli basis and taking the trace kills every nonidentity
string, so the trace is the identity coordinate times the Hilbert-space dimension.  A traceless
Hamiltonian therefore has no identity Pauli coordinate, which is the hypothesis the traceless
two-query separator needs.  The nonidentity weight-at-most-`q` dictionary is inhabited as soon as
there is one qubit and `q ≥ 1`.
-/

open scoped Matrix
open Module NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The trace of a self-adjoint matrix, as a real-linear functional. -/
def selfAdjointTraceLinear (κ : Type*) [Fintype κ] [DecidableEq κ] :
    selfAdjoint (Matrix κ κ ℂ) →ₗ[ℝ] ℂ where
  toFun X := Matrix.trace (X : Matrix κ κ ℂ)
  map_add' X Y := by
    change Matrix.trace ((X : Matrix κ κ ℂ) + (Y : Matrix κ κ ℂ)) = _
    rw [Matrix.trace_add]
  map_smul' r X := by
    change Matrix.trace (r • (X : Matrix κ κ ℂ)) = _
    rw [Matrix.trace_smul]
    simp

theorem trace_finitePauliMatrix_pauliIdentityLabel (n : ℕ) :
    (finitePauliMatrix (pauliIdentityLabel n)).trace = ((2 ^ n : ℕ) : ℂ) := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, finitePauliMatrix_pauliIdentityLabel,
    Finset.sum_const, nsmul_eq_mul]
  simp [FiniteQubitConfiguration]

/-- **The identity Pauli coordinate is the normalized trace.** -/
theorem trace_eq_pauliIdentityCoordinate_mul
    (n : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)) :
    Matrix.trace (H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)
      = (((finitePauliSelfAdjointBasis (Fin n)).repr H (pauliIdentityLabel n) : ℝ) : ℂ)
          * ((2 ^ n : ℕ) : ℂ) := by
  classical
  have hexp := (finitePauliSelfAdjointBasis (Fin n)).sum_repr H
  have hstep := congrArg (selfAdjointTraceLinear (FiniteQubitConfiguration (Fin n))) hexp
  rw [map_sum] at hstep
  have hterm : ∀ P : Fin n → Option (Fin 3),
      selfAdjointTraceLinear (FiniteQubitConfiguration (Fin n))
          ((finitePauliSelfAdjointBasis (Fin n)).repr H P •
            finitePauliSelfAdjointBasis (Fin n) P)
        = if P = pauliIdentityLabel n then
            (((finitePauliSelfAdjointBasis (Fin n)).repr H P : ℝ) : ℂ) * ((2 ^ n : ℕ) : ℂ)
          else 0 := by
    intro P
    rw [map_smul, finitePauliSelfAdjointBasis_apply]
    change ((finitePauliSelfAdjointBasis (Fin n)).repr H P : ℝ) •
      Matrix.trace (finitePauliMatrix P) = _
    by_cases hP : P = pauliIdentityLabel n
    · subst hP
      rw [if_pos rfl, trace_finitePauliMatrix_pauliIdentityLabel]
      simp [Complex.real_smul]
    · rw [if_neg hP, finitePauliMatrix_trace_eq_zero_of_ne_identity P hP, smul_zero]
  rw [Finset.sum_congr rfl fun P _ => hterm P, Finset.sum_ite_eq' Finset.univ] at hstep
  rw [if_pos (Finset.mem_univ _)] at hstep
  exact hstep.symm

/-- **A traceless Hamiltonian has no identity Pauli coordinate.** -/
theorem hasZeroPauliIdentityCoordinate_of_trace_eq_zero
    (n : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ))
    (htrace : Matrix.trace (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) = 0) :
    HasZeroPauliIdentityCoordinate n H := by
  have hrepr := trace_eq_pauliIdentityCoordinate_mul n H
  rw [htrace] at hrepr
  have hne : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by
    simp
  have hzero := (mul_eq_zero.mp hrepr.symm).resolve_right hne
  rw [HasZeroPauliIdentityCoordinate]
  exact_mod_cast hzero

/-- The nonidentity weight-at-most-`q` dictionary is inhabited whenever there is a qubit and
`q ≥ 1`. -/
instance instNonemptyFiniteQTracelessPauliLabel (n q : ℕ) [NeZero n] [NeZero q] :
    Nonempty (FiniteQTracelessPauliLabel n q) := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨⟨pauliZLabel (⟨0, hn⟩ : Fin n), ?_, ?_⟩⟩
  · intro hcon
    have := congrFun hcon (⟨0, hn⟩ : Fin n)
    simp [pauliZLabel, pauliIdentityLabel] at this
  · have hset : (Finset.univ.filter
        fun s : Fin n => pauliZLabel (⟨0, hn⟩ : Fin n) s ≠ none) = {(⟨0, hn⟩ : Fin n)} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        pauliZLabel]
      by_cases hs : s = (⟨0, hn⟩ : Fin n) <;> simp [hs]
    rw [finitePauliWeight, hset, Finset.card_singleton]
    exact Nat.pos_of_ne_zero (NeZero.ne q)

/-- **The traceless two-query separator, stated with tracelessness.**  Every nonzero traceless
Hamiltonian of Pauli weight at most `q` keeps its product-stabilizer two-query transfer signal
strictly above the exact Haar benchmark `1/(2^n+1)`, at every real time. -/
theorem finiteQTracelessAutonomousTransferSignal_gt_haarBenchmark_of_trace_eq_zero
    (n q : ℕ) [NeZero n] [NeZero q]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0)
    (htrace : Matrix.trace (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) = 0)
    (hlocal : HasPauliWeightAtMost (Fin n) q H)
    (t : ℝ)
    (hsep : Fintype.card (FiniteQTracelessPauliLabel n q) * 3 ^ q < 2 ^ n + 1) :
    1 / (((2 ^ n + 1 : ℕ) : ℝ)) <
      productStabilizerTwoQueryProtocolSignal
        (fun P : FiniteQTracelessPauliLabel n q => P.1)
        (finiteQTracelessPauliTransferMatrix n q H t) :=
  finiteQTracelessAutonomousTransferSignal_gt_haarBenchmark n q H hH
    (hasZeroPauliIdentityCoordinate_of_trace_eq_zero n H htrace) hlocal t hsep

/-- The dimension-linear lower bound `3^{-q}/M_q` in the same traceless form. -/
theorem finiteQTracelessAutonomousTransferSignal_ge_of_trace_eq_zero
    (n q : ℕ) [NeZero n] [NeZero q]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0)
    (htrace : Matrix.trace (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) = 0)
    (hlocal : HasPauliWeightAtMost (Fin n) q H)
    (t : ℝ) :
    ((1 : ℝ) / 3) ^ q / (Fintype.card (FiniteQTracelessPauliLabel n q) : ℝ) ≤
      productStabilizerTwoQueryProtocolSignal
        (fun P : FiniteQTracelessPauliLabel n q => P.1)
        (finiteQTracelessPauliTransferMatrix n q H t) :=
  finiteQTracelessAutonomousTransferSignal_ge n q H hH
    (hasZeroPauliIdentityCoordinate_of_trace_eq_zero n H htrace) hlocal t

end

end GaloisForLFunctions.HTGeometry
