import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import GaloisForLFunctions.HTGeometry.DerivationLowerJetJacobianWitness
import GaloisForLFunctions.HTGeometry.HeisenbergHorizonRepresentation

/-!
# Heisenberg mechanics on the free-coordinate field

Free rational coordinates realize both the canonical commutation relation and an exact jet ladder.
The coordinate derivative gives `[∂ᵢ, M_{xᵢ}] = I`; the universal shift derivation gives
`[D, M_{xₖ}] = M_{xₖ₊₁}` and its iterated Heisenberg commutators recover every coordinate jet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational function field on the countable free jet coordinates. -/
abbrev FreeNatShiftField := FreeCoordinateRationalField ℂ ℕ

/-- Quotient-rule extension of the universal polynomial jet-shift derivation. -/
def freeNatShiftDerivation : Derivation ℂ FreeNatShiftField FreeNatShiftField :=
  extendFreeCoordinatePolynomialDerivation natShiftDerivation

/-- The free-field shift derivation raises a coordinate index by one. -/
@[simp]
theorem freeNatShiftDerivation_freeCoordinate (k : ℕ) :
    freeNatShiftDerivation (freeCoordinate ℂ ℕ k) = freeCoordinate ℂ ℕ (k + 1) := by
  rw [freeNatShiftDerivation, freeCoordinate,
    extendFreeCoordinatePolynomialDerivation_algebraMap, natShiftDerivation_X]
  rfl

/-- **Canonical commutation relation on a free rational coordinate:** `[∂ᵢ, M_{xᵢ}] = I`. -/
theorem freeCoordinate_canonical_commutation (i : ℕ) :
    ⁅derivationEndomorphism (freeCoordinateDerivation ℂ ℕ i),
        Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ i)⁆ =
      LinearMap.id := by
  rw [derivationEndomorphism_commutator_multiplication,
    freeCoordinateDerivation_freeCoordinate_self]
  ext f
  simp

/-- **Heisenberg jet ladder:** commutation with the shift derivation raises the coordinate. -/
theorem freeNatShift_heisenberg_commutator (k : ℕ) :
    ⁅derivationEndomorphism freeNatShiftDerivation,
        Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ k)⁆ =
      Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ (k + 1)) := by
  rw [derivationEndomorphism_commutator_multiplication,
    freeNatShiftDerivation_freeCoordinate]

/-- Every iterate of the shift derivation advances by the exact iteration count. -/
theorem freeNatShiftDerivation_iterate_freeCoordinate (n k : ℕ) :
    ((freeNatShiftDerivation : FreeNatShiftField → FreeNatShiftField)^[n])
        (freeCoordinate ℂ ℕ k) = freeCoordinate ℂ ℕ (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        freeNatShiftDerivation_freeCoordinate]
      simp [Nat.add_assoc]

/-- Nested Heisenberg commutators of multiplication by `x₀` recover multiplication by `xₙ`. -/
theorem freeNatShift_heisenbergJetOperator (n : ℕ) :
    heisenbergJetOperator freeNatShiftDerivation (freeCoordinate ℂ ℕ 0) n =
      Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ n) := by
  rw [heisenbergJetOperator_eq_multiplication,
    freeNatShiftDerivation_iterate_freeCoordinate]
  simp

end

end GaloisForLFunctions.HTGeometry
