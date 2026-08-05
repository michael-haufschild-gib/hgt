import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.TracelessLocalPauliTransferConservationLaw

/-!
# Bounded Pauli weight and vanishing identity coordinate are realized

Both interfaces of the finite-qubit Pauli layer — that a self-adjoint operator has no Pauli
component above a given weight, and that its identity component vanishes — are conditions on
finitely many coordinates of one basis expansion.  Each is satisfied by the zero operator and is
stable under the linear operations, so each cuts out a genuine submodule of the self-adjoint
operators rather than a single point; bounded weight is also monotone in the weight budget.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Bounded Pauli weight -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem hasPauliWeightAtMost_zero (q : ℕ) : HasPauliWeightAtMost σ q 0 := by
  intro P _
  simp

/-- Bounded Pauli weight is monotone in the budget. -/
theorem HasPauliWeightAtMost.mono {q q' : ℕ} {H : selfAdjoint
    (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)}
    (h : HasPauliWeightAtMost σ q H) (hq : q ≤ q') :
    HasPauliWeightAtMost σ q' H := by
  intro P hP
  exact h P (lt_of_le_of_lt hq hP)

/-- Bounded Pauli weight is closed under addition. -/
theorem HasPauliWeightAtMost.add {q : ℕ} {H K : selfAdjoint
    (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)}
    (hH : HasPauliWeightAtMost σ q H) (hK : HasPauliWeightAtMost σ q K) :
    HasPauliWeightAtMost σ q (H + K) := by
  intro P hP
  simp [hH P hP, hK P hP]

/-- Bounded Pauli weight is closed under negation. -/
theorem HasPauliWeightAtMost.neg {q : ℕ} {H : selfAdjoint
    (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)}
    (hH : HasPauliWeightAtMost σ q H) : HasPauliWeightAtMost σ q (-H) := by
  intro P hP
  simp [hH P hP]

/-! ## Vanishing identity coordinate -/

theorem hasZeroPauliIdentityCoordinate_zero (n : ℕ) :
    HasZeroPauliIdentityCoordinate n 0 := by
  rw [HasZeroPauliIdentityCoordinate]
  simp

theorem HasZeroPauliIdentityCoordinate.add {n : ℕ} {H K : selfAdjoint
    (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)}
    (hH : HasZeroPauliIdentityCoordinate n H) (hK : HasZeroPauliIdentityCoordinate n K) :
    HasZeroPauliIdentityCoordinate n (H + K) := by
  rw [HasZeroPauliIdentityCoordinate] at hH hK ⊢
  simp [hH, hK]

theorem HasZeroPauliIdentityCoordinate.neg {n : ℕ} {H : selfAdjoint
    (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ)}
    (hH : HasZeroPauliIdentityCoordinate n H) :
    HasZeroPauliIdentityCoordinate n (-H) := by
  rw [HasZeroPauliIdentityCoordinate] at hH ⊢
  simp [hH]

end GaloisForLFunctions.HTGeometry
