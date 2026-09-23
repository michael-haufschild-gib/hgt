import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianTransport

/-!
# The chart currents annihilate the Schwarzian

The translation current is the zeroth coordinate derivation, and the Schwarzian involves only the
first three positive jets, so the translation current kills it outright.  The inversion current
sends the `n`-th jet to minus the `n`-th jet of the square of the base coordinate; substituting the
first three of those into the Schwarzian and clearing denominators gives zero.

Both currents commute with the jet shift, so they annihilate every jet of the Schwarzian, not only
the Schwarzian itself.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

/-! ## The jets of the square of the base coordinate -/

/-- The `n`-th jet of the square of the base coordinate, in the jet field. -/
def squareJet (C : Type*) [Field C] (n : ℕ) : FreeScalarJetField C :=
  algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) (freeJetSquareCoefficient C n)

omit [CharZero C] in
@[simp]
theorem freeJetFZero_freeCoordinate' (n : ℕ) :
    freeJetFZero C (freeCoordinate C ℕ n) = -squareJet C n :=
  freeJetFZero_freeCoordinate n

omit [CharZero C] in
theorem squareJet_succ (n : ℕ) : squareJet C (n + 1) = freeJetShift C (squareJet C n) := by
  rw [squareJet, squareJet, freeJetShift_algebraMap,
    freeJetShiftPolynomialDerivation_squareCoefficient]

omit [CharZero C] in
theorem squareJet_zero : squareJet C 0 = freeCoordinate C ℕ 0 * freeCoordinate C ℕ 0 := by
  rw [squareJet, freeJetSquareCoefficient, Function.iterate_zero_apply, map_mul]
  rfl

omit [CharZero C] in
theorem freeJetShift_two : freeJetShift C (2 : FreeScalarJetField C) = 0 := by
  rw [show (2 : FreeScalarJetField C) = algebraMap C (FreeScalarJetField C) 2 from by
    norm_num [map_ofNat]]
  exact Derivation.map_algebraMap _ _

omit [CharZero C] in
theorem squareJet_one :
    squareJet C 1 = 2 * freeCoordinate C ℕ 0 * freeCoordinate C ℕ 1 := by
  rw [squareJet_succ, squareJet_zero, Derivation.leibniz, freeJetShift_freeCoordinate]
  simp only [smul_eq_mul]
  ring

omit [CharZero C] in
theorem squareJet_two :
    squareJet C 2 = 2 * freeCoordinate C ℕ 1 ^ (2 : ℕ) +
      2 * freeCoordinate C ℕ 0 * freeCoordinate C ℕ 2 := by
  rw [squareJet_succ, squareJet_one]
  simp only [Derivation.leibniz, freeJetShift_freeCoordinate, freeJetShift_two, smul_eq_mul]
  ring

omit [CharZero C] in
theorem squareJet_three :
    squareJet C 3 = 6 * freeCoordinate C ℕ 1 * freeCoordinate C ℕ 2 +
      2 * freeCoordinate C ℕ 0 * freeCoordinate C ℕ 3 := by
  rw [squareJet_succ, squareJet_two]
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, freeJetShift_freeCoordinate,
    freeJetShift_two, smul_eq_mul]
  ring

/-! ## Annihilation of the Schwarzian -/

theorem freeJetFZero_numeral : freeJetFZero C (3 / 2 : FreeScalarJetField C) = 0 := by
  have hnum : (3 / 2 : FreeScalarJetField C) =
      algebraMap C (FreeScalarJetField C) ((3 : C) / 2) := by
    rw [map_div₀]
    norm_num [map_ofNat]
  rw [hnum]
  exact Derivation.map_algebraMap _ _

/-- **The inversion current annihilates the Schwarzian.** -/
theorem freeJetFZero_freeJetSchwarzian : freeJetFZero C (freeJetSchwarzian C) = 0 := by
  have h1 : freeCoordinate C ℕ 1 ≠ 0 := freeScalarJetCoordinate_ne_zero 1
  rw [freeJetSchwarzian, schwarzian, freeJetBase_deriv3, freeJetBase_deriv2, freeJetBase_deriv,
    map_sub, Derivation.leibniz_div, Derivation.leibniz, freeJetFZero_numeral,
    Derivation.leibniz_pow, Derivation.leibniz_div, freeJetFZero_freeCoordinate',
    freeJetFZero_freeCoordinate', freeJetFZero_freeCoordinate', squareJet_one, squareJet_two,
    squareJet_three]
  have hcancel : freeCoordinate C ℕ 1 ^ (3 : ℕ) * (freeCoordinate C ℕ 1)⁻¹ ^ (2 : ℕ) =
      freeCoordinate C ℕ 1 := by
    field_simp
  simp only [smul_eq_mul, mul_zero, add_zero]
  field_simp
  linear_combination (12 * freeCoordinate C ℕ 2) * hcancel

omit [CharZero C] in
/-- **The translation current annihilates the Schwarzian.** -/
theorem freeCoordinateDerivation_zero_freeJetSchwarzian :
    freeCoordinateDerivation C ℕ 0 (freeJetSchwarzian C) = 0 :=
  freeCoordinateField_le_commonKernel ({1, 2, 3} : Set ℕ) freeJetSchwarzian_mem 0 (by simp)

/-! ## Propagation to every jet -/

theorem freeJetFZero_schwarzianJet (k : ℕ) :
    freeJetFZero C (differentialJet k (freeJetSchwarzian C)) = 0 := by
  induction k with
  | zero =>
      rw [differentialJet_zero]
      exact freeJetFZero_freeJetSchwarzian
  | succ k ih =>
      have h := congrArg
        (fun D : Derivation C (FreeScalarJetField C) (FreeScalarJetField C) =>
          D (differentialJet k (freeJetSchwarzian C))) (freeJet_lie_shift_F_zero (C := C))
      simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
      rw [differentialJet_succ, freeScalarJetField_deriv_apply, ← sub_eq_zero.1 h, ih, map_zero]

end

end GaloisForLFunctions.HTGeometry
