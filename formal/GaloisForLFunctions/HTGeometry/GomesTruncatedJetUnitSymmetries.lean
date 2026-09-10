import GaloisForLFunctions.HTGeometry.GomesTruncatedJetScalarBoundary
import GaloisForLFunctions.HTGeometry.GomesFiniteFockSymmetrySpectrum

/-!
# Explicit invertible symmetries at the sharp phase-order boundary

The phase-order shear is invertible for every actual phase. It is non-scalar
exactly when a positive phase order fits below the finite horizon, so the
surviving algebraic freedom is realized by genuine invertible matrix symmetries.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The identity plus the actual phase-order clock power. -/
def gomesTruncatedJetOrderShear (n : ℕ) (z : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  1 + fockShiftMatrix (n + 1) ^ orderOf z

/-- The phase-order shear is an actual joint symmetry for every phase. -/
theorem gomesTruncatedJetOrderShear_mem (n : ℕ) (z : ℂ) :
    gomesTruncatedJetOrderShear n z ∈ gomesTruncatedJetJointAlgebra n z :=
  (gomesTruncatedJetJointAlgebra n z).add_mem (Subalgebra.one_mem _)
    (gomesTruncatedJetJointAlgebra_orderPower_mem n z)

/-- The existing polynomial-symbol representation realizes the shear exactly. -/
theorem gomesTruncatedJetOrderShear_polynomial (n : ℕ) (z : ℂ) :
    gomesFiniteFockPolynomialHom (n + 1) (1 + X ^ orderOf z) =
      gomesTruncatedJetOrderShear n z := by
  rw [map_add, map_one, map_pow, gomesFiniteFockPolynomialHom_X]
  rfl

/-- Every phase-order shear is invertible, including zero-order phases where it is twice the identity. -/
theorem gomesTruncatedJetOrderShear_isUnit (n : ℕ) (z : ℂ) :
    IsUnit (gomesTruncatedJetOrderShear n z) := by
  rw [← gomesTruncatedJetOrderShear_polynomial, gomesFiniteFockPolynomialHom_isUnit_iff]
  by_cases hd : orderOf z = 0
  · simp [hd]
  · simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Ne.symm hd]

/-- Adding the identity changes no scalar/non-scalar boundary for the actual order-power symmetry. -/
theorem gomesTruncatedJetOrderShear_scalar_iff (n : ℕ) (z : ℂ) :
    gomesTruncatedJetOrderShear n z ∈
        (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ↔
      orderOf z = 0 ∨ n + 1 ≤ orderOf z := by
  rw [← gomesTruncatedJetClock_orderPower_scalar_iff]
  constructor
  · intro h
    have hs := (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).sub_mem h
      (Subalgebra.one_mem _)
    simpa only [gomesTruncatedJetOrderShear, add_sub_cancel_left] using hs
  · intro h
    exact (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).add_mem
      (Subalgebra.one_mem _) h

/-- Invertible non-scalar joint symmetries exist exactly at the positive finite-order horizon boundary. -/
theorem gomesTruncatedJetJointAlgebra_exists_nonscalar_unit_iff (n : ℕ) (z : ℂ) :
    (∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsUnit M ∧ M ∈ gomesTruncatedJetJointAlgebra n z ∧
        M ∉ (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) ↔
      0 < orderOf z ∧ orderOf z < n + 1 := by
  constructor
  · rintro ⟨M, _, hm, hn⟩
    exact (gomesTruncatedJetJointAlgebra_exists_nonscalar_iff n z).mp ⟨M, hm, hn⟩
  · rintro ⟨hp, hl⟩
    refine ⟨gomesTruncatedJetOrderShear n z, gomesTruncatedJetOrderShear_isUnit n z,
      gomesTruncatedJetOrderShear_mem n z, ?_⟩
    intro h
    rcases (gomesTruncatedJetOrderShear_scalar_iff n z).mp h with hz | hh
    · exact (Nat.ne_of_gt hp) hz
    · exact (Nat.not_le_of_gt hl) hh

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
