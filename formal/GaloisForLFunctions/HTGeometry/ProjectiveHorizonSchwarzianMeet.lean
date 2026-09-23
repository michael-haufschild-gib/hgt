import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianInvariance
import GaloisForLFunctions.HTGeometry.FreeCoordinateChainRule
import GaloisForLFunctions.HTGeometry.SemilinearFractionField

/-!
# The depth-one meet is the Schwarzian field

A jet observable killed by the translation and inversion currents is killed by their bracket too.
Conjugating the three currents into the Schwarzian coordinates and expanding by the chain rule, the
tail coordinates drop out because the currents annihilate every Schwarzian jet, and what is left is
three equations in the three derivatives along `x`, `x'`, `x''`.

The translation equation kills the first derivative outright; substituting into the other two leaves
`(x')^(2 : ℕ)` times the third, so all three vanish and the observable is a rational function of the
Schwarzian.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
theorem freeCoordinateDerivation_numeral (m : ℕ) :
    freeCoordinateDerivation C ℕ m (2 : FreeScalarJetField C) = 0 := by
  rw [show (2 : FreeScalarJetField C) = algebraMap C (FreeScalarJetField C) 2 from by
    norm_num [map_ofNat]]
  exact Derivation.map_algebraMap _ _

omit [CharZero C] in
theorem freeJetShiftPolynomialDerivation_lie_zero (C : Type*) [Field C] :
    ⁅freeJetShiftPolynomialDerivation C, MvPolynomial.pderiv (R := C) 0⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro l
  rw [Derivation.commutator_apply, Derivation.zero_apply,
    freeJetShiftPolynomialDerivation_X,
    MvPolynomial.pderiv_X_of_ne (show l + 1 ≠ 0 by omega), sub_zero]
  rcases eq_or_ne l 0 with rfl | hl
  · rw [MvPolynomial.pderiv_X_self, Derivation.map_one_eq_zero]
  · rw [MvPolynomial.pderiv_X_of_ne hl, map_zero]

omit [CharZero C] in
theorem freeCoordinateDerivation_zero_lie_shift (C : Type*) [Field C] :
    ⁅freeJetShift C, freeCoordinateDerivation C ℕ 0⁆ = 0 := by
  rw [freeJetShift, freeCoordinateDerivation, extendFreeCoordinatePolynomialDerivation_lie,
    freeJetShiftPolynomialDerivation_lie_zero, extendFreeCoordinatePolynomialDerivation_zero]

omit [CharZero C] in
theorem freeCoordinateDerivation_zero_schwarzianJet (k : ℕ) :
    freeCoordinateDerivation C ℕ 0 (differentialJet k (freeJetSchwarzian C)) = 0 := by
  induction k with
  | zero =>
      rw [differentialJet_zero]
      exact freeCoordinateDerivation_zero_freeJetSchwarzian
  | succ k ih =>
      have h := congrArg
        (fun D : Derivation C (FreeScalarJetField C) (FreeScalarJetField C) =>
          D (differentialJet k (freeJetSchwarzian C))) (freeCoordinateDerivation_zero_lie_shift C)
      simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
      rw [differentialJet_succ, freeScalarJetField_deriv_apply, ← sub_eq_zero.1 h, ih, map_zero]

/-- The bracket of the translation and inversion currents. -/
def jetH (C : Type*) [Field C] :
    Derivation C (FreeScalarJetField C) (FreeScalarJetField C) :=
  ⁅freeCoordinateDerivation C ℕ 0, freeJetFZero C⁆

omit [CharZero C] in
theorem jetH_apply (f : FreeScalarJetField C) :
    jetH C f = freeCoordinateDerivation C ℕ 0 (freeJetFZero C f) -
      freeJetFZero C (freeCoordinateDerivation C ℕ 0 f) :=
  Derivation.commutator_apply _

omit [CharZero C] in
theorem jetH_freeCoordinate_zero :
    jetH C (freeCoordinate C ℕ 0) = -(2 * freeCoordinate C ℕ 0) := by
  rw [jetH_apply, freeJetFZero_freeCoordinate', squareJet_zero,
    freeCoordinateDerivation_freeCoordinate_self]
  simp only [map_neg, Derivation.leibniz, smul_eq_mul,
    freeCoordinateDerivation_freeCoordinate_self, Derivation.map_one_eq_zero, sub_zero]
  ring

omit [CharZero C] in
theorem jetH_freeCoordinate_one :
    jetH C (freeCoordinate C ℕ 1) = -(2 * freeCoordinate C ℕ 1) := by
  have h0 : freeCoordinateDerivation C ℕ 0 (freeCoordinate C ℕ 1) = 0 :=
    freeCoordinateDerivation_freeCoordinate_of_ne (by omega)
  have hn : freeCoordinateDerivation C ℕ 0 (2 : FreeScalarJetField C) = 0 :=
    freeCoordinateDerivation_numeral 0
  rw [jetH_apply, freeJetFZero_freeCoordinate', squareJet_one, h0, map_zero, sub_zero]
  simp only [map_neg, Derivation.leibniz, smul_eq_mul, hn,
    freeCoordinateDerivation_freeCoordinate_self, h0]
  ring

omit [CharZero C] in
theorem jetH_freeCoordinate_two :
    jetH C (freeCoordinate C ℕ 2) = -(2 * freeCoordinate C ℕ 2) := by
  have h0 : freeCoordinateDerivation C ℕ 0 (freeCoordinate C ℕ 2) = 0 :=
    freeCoordinateDerivation_freeCoordinate_of_ne (by omega)
  have h1 : freeCoordinateDerivation C ℕ 0 (freeCoordinate C ℕ 1) = 0 :=
    freeCoordinateDerivation_freeCoordinate_of_ne (by omega)
  have hn : freeCoordinateDerivation C ℕ 0 (2 : FreeScalarJetField C) = 0 :=
    freeCoordinateDerivation_numeral 0
  rw [jetH_apply, freeJetFZero_freeCoordinate', squareJet_two, h0, map_zero, sub_zero]
  simp only [map_neg, map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, hn,
    freeCoordinateDerivation_freeCoordinate_self, h0, h1]
  ring

theorem jetH_schwarzianJet (k : ℕ) :
    jetH C (differentialJet k (freeJetSchwarzian C)) = 0 := by
  rw [jetH_apply, freeJetFZero_schwarzianJet, map_zero]
  rw [freeCoordinateDerivation_zero_schwarzianJet, map_zero, sub_zero]

end

end GaloisForLFunctions.HTGeometry
