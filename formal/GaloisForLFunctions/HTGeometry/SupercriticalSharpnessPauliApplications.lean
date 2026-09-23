import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.HTGeometry.PauliScalarDistanceCommutatorLaw

/-!
# Finite-density selection for Pauli coefficients

Closed applications of the finite-family density selector from arXiv:2603.03257 to Pauli-word
coefficient energy.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Some Pauli word carries at least the average squared coefficient norm of the complete finite
Pauli dictionary. -/
theorem exists_pauliWord_totalCoefficientEnergy_le_card_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) :
    ∃ P : σ → Option (Fin 3),
      (∑ Q, ‖J Q‖ ^ (2 : ℕ)) ≤
        (Fintype.card (σ → Option (Fin 3)) : ℝ) * ‖J P‖ ^ (2 : ℕ) := by
  rcases finiteFamilySum_empty_or_le_card_mul (fun Q ↦ ‖J Q‖ ^ (2 : ℕ)) with hempty | hcarrier
  · have hpos : 0 < Fintype.card (σ → Option (Fin 3)) := Fintype.card_pos
    omega
  · exact hcarrier

/-- Non-scalar Pauli dictionary is empty, or one non-scalar word carries at least its average
squared coefficient energy. -/
theorem nonzeroPauliWord_empty_or_exists_coefficientEnergy_le_card_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : (σ → Option (Fin 3)) → ℂ) :
    Fintype.card (NonzeroPauliCharacter σ) = 0 ∨
      ∃ P : NonzeroPauliCharacter σ,
        (∑ Q : NonzeroPauliCharacter σ, ‖J Q.1‖ ^ (2 : ℕ)) ≤
          (Fintype.card (NonzeroPauliCharacter σ) : ℝ) * ‖J P.1‖ ^ (2 : ℕ) := by
  exact finiteFamilySum_empty_or_le_card_mul
    (fun Q : NonzeroPauliCharacter σ ↦ ‖J Q.1‖ ^ (2 : ℕ))

end GaloisForLFunctions.HTGeometry
