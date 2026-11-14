import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDyadicAntichainCoordinates
import GaloisForLFunctions.HTGeometry.Moments.DelayedGeometricMemory
import GaloisForLFunctions.HTGeometry.Moments.FiniteStateLocalClosure

/-!
# Constant dyadic energy does not bound response memory

The normalized dyadic impulse at depth `d` is a geometric response delayed by `d`
labels. Its squared energy is always `4/3`, whereas its minimum state dimension
is exactly `d + 1`. Even arbitrarily accurate finite-window fits cannot use a
smaller fixed dimension. Leading Hankel determinants distinguish delays that the
homogeneous energy norm does not distinguish.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open _root_.HTGeometry.FiniteHankel

/-- The native normalized impulse is a delayed geometric response of ratio one half. -/
theorem fermiDyadicImpulse_eq_delayedGeometric (d : ℕ) :
    fermiDyadicImpulse d = delayedGeometric (1 / 2 : ℝ) d := by
  funext n
  unfold fermiDyadicImpulse delayedGeometric
  by_cases h : d ≤ n
  · rw [if_pos h, if_pos h, one_div_pow]
    have hn : (2 : ℝ)^n = (2 : ℝ)^(n - d) * (2 : ℝ)^d := by
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [hn]
    field_simp
  · rw [if_neg h, if_neg h]

/-- Minimum state dimension grows exactly with the assigned dyadic depth. -/
theorem fermiDyadicImpulse_minimal_stateSpace (d : ℕ) :
    _root_.HTGeometry.AlgebraicStateSpaceDimensionAtMost (d + 1) (fermiDyadicImpulse d) ∧
      ∀ B, _root_.HTGeometry.AlgebraicStateSpaceDimensionAtMost B (fermiDyadicImpulse d) →
        d + 1 ≤ B := by
  rw [fermiDyadicImpulse_eq_delayedGeometric]
  exact delayedGeometric_minimal_stateSpace (1 / 2 : ℝ) d

/-- The unique nonempty nonsingular leading block records the dyadic depth. -/
theorem fermiDyadicImpulse_leadingDet_ne_zero_iff (d n : ℕ) :
    leadingDet (fermiDyadicImpulse d) n ≠ 0 ↔ n = 0 ∨ n = d + 1 := by
  rw [fermiDyadicImpulse_eq_delayedGeometric]
  exact delayedGeometric_leadingDet_ne_zero_iff (1 / 2 : ℝ) d n

/-- A smaller dimension cannot even approximate every finite observation window. -/
theorem fermiDyadicImpulse_not_localClosure (d B : ℕ) (hB : B ≤ d) :
    ¬ _root_.HTGeometry.FixedAlgebraicStateSpaceDimensionLocalClosure B (fermiDyadicImpulse d) := by
  intro h
  obtain ⟨e, he, hs⟩ := stateSpace_of_fixedDimension_localClosure h
  have hde := (fermiDyadicImpulse_minimal_stateSpace d).2 e hs
  omega

/-- A fixed positive energy level contains responses requiring arbitrarily large state dimension. -/
theorem fermi_energy_level_unbounded_memory (B : ℕ) :
    ∃ s : ℕ → ℝ, HasSum (fun n => (s n)^2) (4 / 3 : ℝ) ∧
      _root_.HTGeometry.AlgebraicStateSpaceDimensionAtMost (B + 1) s ∧
      ¬ _root_.HTGeometry.FixedAlgebraicStateSpaceDimensionLocalClosure B s :=
  ⟨fermiDyadicImpulse B, fermiDyadicImpulse_square_hasSum B,
    (fermiDyadicImpulse_minimal_stateSpace B).1, fermiDyadicImpulse_not_localClosure B B le_rfl⟩

#print axioms fermiDyadicImpulse_minimal_stateSpace
#print axioms fermiDyadicImpulse_leadingDet_ne_zero_iff
#print axioms fermi_energy_level_unbounded_memory

end GaloisForLFunctions.TransHorizonIncidenceMechanics
