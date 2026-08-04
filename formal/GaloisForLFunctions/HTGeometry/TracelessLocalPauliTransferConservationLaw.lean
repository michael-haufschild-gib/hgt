import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels

/-!
# Traceless local Pauli-transfer conservation

This module removes identity contamination from the concrete local
Pauli-transfer block.  For a nonzero Hamiltonian with zero identity Pauli
coordinate and Pauli weight at most `q`, the principal block indexed by
nonidentity weight-at-most-`q` strings fixes the Hamiltonian coefficient
vector exactly.  The exact product-stabilizer twirl therefore gives the
dimension-linear lower bound `3⁻q / M_q` needed by the physical two-query
locality test.
-/

open scoped Matrix
open Module NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Predicate selecting nonidentity Pauli strings of weight at most `q`. -/
def IsFiniteQTracelessPauliLabel
    (n q : ℕ) (P : Fin n → Option (Fin 3)) : Prop :=
  P ≠ pauliIdentityLabel n ∧ finitePauliWeight P ≤ q

instance instDecidableIsFiniteQTracelessPauliLabel
    (n q : ℕ) (P : Fin n → Option (Fin 3)) :
    Decidable (IsFiniteQTracelessPauliLabel n q P) := by
  unfold IsFiniteQTracelessPauliLabel
  infer_instance

/-- Nonidentity Pauli strings supported on at most `q` qubits. -/
abbrev FiniteQTracelessPauliLabel (n q : ℕ) :=
  {P : Fin n → Option (Fin 3) // IsFiniteQTracelessPauliLabel n q P}

/-- The Hamiltonian has no physically irrelevant identity Pauli
coordinate. -/
def HasZeroPauliIdentityCoordinate
    (n : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)) : Prop :=
  ((finitePauliSelfAdjointBasis (Fin n)).repr H :
      (Fin n → Option (Fin 3)) → ℝ) (pauliIdentityLabel n) = 0

/-- Principal nonidentity `q`-local block of the exact Pauli-transfer
matrix. -/
def finiteQTracelessPauliTransferMatrix
    (n q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (t : ℝ) :
    Matrix (FiniteQTracelessPauliLabel n q)
      (FiniteQTracelessPauliLabel n q) ℝ :=
  matrixCoordinateCompression
    (IsFiniteQTracelessPauliLabel n q)
    (LinearMap.toMatrix
      (finitePauliSelfAdjointBasis (Fin n))
      (finitePauliSelfAdjointBasis (Fin n))
      (finiteMatrixSelfAdjointConjugationLinearMap
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ))))))

/-- Restriction of the Hamiltonian's Pauli coordinates to the nonidentity
weight-at-most-`q` dictionary. -/
def finiteQTracelessEnergyCoordinates
    (n q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)) :
    FiniteQTracelessPauliLabel n q → ℝ :=
  vectorCoordinateRestriction
    (IsFiniteQTracelessPauliLabel n q)
    ((finitePauliSelfAdjointBasis (Fin n)).repr H :
      (Fin n → Option (Fin 3)) → ℝ)

/-- Exact autonomous conservation survives compression after the identity
coordinate is removed. -/
theorem finiteQTracelessPauliTransferMatrix_fixes_energyCoordinates
    (n q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hzero : HasZeroPauliIdentityCoordinate n H)
    (hlocal : HasPauliWeightAtMost (Fin n) q H)
    (t : ℝ) :
    finiteQTracelessPauliTransferMatrix n q H t *ᵥ
        finiteQTracelessEnergyCoordinates n q H =
      finiteQTracelessEnergyCoordinates n q H := by
  rw [finiteQTracelessPauliTransferMatrix,
    finiteQTracelessEnergyCoordinates]
  apply
    matrixCoordinateCompression_mulVec_restriction_eq_of_fixed_of_support
  · exact
      linearMap_toMatrix_mulVec_repr_eq_of_fixed
        (finitePauliSelfAdjointBasis (Fin n))
        (finiteMatrixSelfAdjointConjugationLinearMap
          (exp (t • ((-Complex.I) •
            (H : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))))
        H
        (finiteMatrixSelfAdjointConjugation_fixes_energy H t)
  · intro P hP
    by_cases hidentity : P = pauliIdentityLabel n
    · simpa [HasZeroPauliIdentityCoordinate, hidentity] using hzero
    · have hweight : ¬ finitePauliWeight P ≤ q := by
        intro hle
        exact hP ⟨hidentity, hle⟩
      exact hlocal P (Nat.lt_of_not_ge hweight)

/-- A nonzero Hamiltonian supported on the traceless local dictionary has a
nonzero restricted coefficient vector. -/
theorem finiteQTracelessEnergyCoordinates_ne_zero
    (n q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0)
    (hzero : HasZeroPauliIdentityCoordinate n H)
    (hlocal : HasPauliWeightAtMost (Fin n) q H) :
    finiteQTracelessEnergyCoordinates n q H ≠ 0 := by
  rw [finiteQTracelessEnergyCoordinates]
  apply vectorCoordinateRestriction_ne_zero_of_ne_zero_of_support
  · intro hcoeff
    apply hH
    apply (finitePauliSelfAdjointBasis (Fin n)).repr.injective
    exact Finsupp.ext fun P => by
      simpa using congrFun hcoeff P
  · intro P hP
    by_cases hidentity : P = pauliIdentityLabel n
    · simpa [HasZeroPauliIdentityCoordinate, hidentity] using hzero
    · have hweight : ¬ finitePauliWeight P ≤ q := by
        intro hle
        exact hP ⟨hidentity, hle⟩
      exact hlocal P (Nat.lt_of_not_ge hweight)

/-- **Traceless local two-query sub-signal.**  The literal nonidentity local
Pauli-transfer block of every nonzero traceless `q`-local autonomous
Hamiltonian has product-stabilizer signal at least `3⁻q / M_q` at every real
time. -/
theorem finiteQTracelessAutonomousTransferSignal_ge
    (n q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0)
    (hzero : HasZeroPauliIdentityCoordinate n H)
    (hlocal : HasPauliWeightAtMost (Fin n) q H)
    (t : ℝ)
    [Nonempty (FiniteQTracelessPauliLabel n q)] :
    ((1 : ℝ) / 3) ^ q /
        (Fintype.card (FiniteQTracelessPauliLabel n q) : ℝ) ≤
      productStabilizerTwoQueryProtocolSignal
        (fun P : FiniteQTracelessPauliLabel n q => P.1)
        (finiteQTracelessPauliTransferMatrix n q H t) := by
  exact productStabilizerTwoQueryProtocolSignal_ge
    q
    (fun P : FiniteQTracelessPauliLabel n q => P.1)
    Subtype.val_injective
    (fun P => P.2.2)
    (finiteQTracelessPauliTransferMatrix n q H t)
    (finiteQTracelessEnergyCoordinates n q H)
    (finiteQTracelessEnergyCoordinates_ne_zero
      n q H hH hzero hlocal)
    (finiteQTracelessPauliTransferMatrix_fixes_energyCoordinates
      n q H hzero hlocal t)

/-- The traceless local sub-signal is strictly above the exact balanced Haar
benchmark whenever `M_q 3^q < 2^n + 1`.  The separate physical-score module
identifies both sides with the same randomized two-query experiment. -/
theorem finiteQTracelessAutonomousTransferSignal_gt_haarBenchmark
    (n q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0)
    (hzero : HasZeroPauliIdentityCoordinate n H)
    (hlocal : HasPauliWeightAtMost (Fin n) q H)
    (t : ℝ)
    [Nonempty (FiniteQTracelessPauliLabel n q)]
    (hsep :
      Fintype.card (FiniteQTracelessPauliLabel n q) * 3 ^ q <
        2 ^ n + 1) :
    1 / (((2 ^ n + 1 : ℕ) : ℝ)) <
      productStabilizerTwoQueryProtocolSignal
        (fun P : FiniteQTracelessPauliLabel n q => P.1)
        (finiteQTracelessPauliTransferMatrix n q H t) := by
  exact productStabilizerTwoQueryProtocolSignal_gt_haarBenchmark
    q (2 ^ n)
    (fun P : FiniteQTracelessPauliLabel n q => P.1)
    Subtype.val_injective
    (fun P => P.2.2)
    (finiteQTracelessPauliTransferMatrix n q H t)
    (finiteQTracelessEnergyCoordinates n q H)
    (finiteQTracelessEnergyCoordinates_ne_zero
      n q H hH hzero hlocal)
    (finiteQTracelessPauliTransferMatrix_fixes_energyCoordinates
      n q H hzero hlocal t)
    hsep

end

end GaloisForLFunctions.HTGeometry
