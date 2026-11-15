import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerGenusNormalizationBalance
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalParameter
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RegularDifferentialEquivalence

/-!
# Parity classifies the geometric-sum Kummer fields

For a fixed nonzero scalar, when the branch prime power is the covering
degree minus one, all even geometric-sum exponents give one rational field
and all odd exponents give one positive-genus field. Genus invariance separates the two classes, so
parity is a complete invariant within this family over its square constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ)

/-- The family whose covering degree is one more than its branch prime power. -/
abbrev SquareKummerGeometricField (r : ℕ) :=
  SquareKummerField p s c (p ^ (s + 1) - 2) (kummerExponent (p ^ (s + 1)) r)

theorem squareKummerGeometricGenus_odd_pos (n : ℕ) :
    0 < squareKummerGeometricGenus p s s c (2 * n + 1) := by
  rw [squareKummerGeometricGenus_odd]
  have hq : 2 ≤ p ^ (s + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hm : 2 ≤ p ^ (s + 1) * (p ^ (s + 1) - 1) := by
    calc
      2 = 2 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul hq (by omega)
  omega

/-- Positive odd genus obstructs an isomorphism with an even model. -/
theorem squareKummerEvenOdd_not_equiv (n m : ℕ) :
    ¬ Nonempty (SquareKummerGeometricField p s c (2 * n) ≃ₐ[SquareConstantField p s]
      SquareKummerGeometricField p s c (2 * m + 1)) := by
  rintro ⟨e⟩
  have h := globalRegularDifferential_finrank_eq e
  change squareKummerGeometricGenus p s s c (2 * n) =
    squareKummerGeometricGenus p s s c (2 * m + 1) at h
  rw [squareKummerGeometricGenus_even] at h
  have hp := squareKummerGeometricGenus_odd_pos p s c m
  omega

/-- Two members of the family are isomorphic over their constants exactly when their lengths have equal parity. -/
theorem squareKummerGeometricField_equiv_iff_parity (r t : ℕ) :
    Nonempty (SquareKummerGeometricField p s c r ≃ₐ[SquareConstantField p s]
      SquareKummerGeometricField p s c t) ↔ r % 2 = t % 2 := by
  have hform (a : ℕ) : ∃ n, a = 2 * n ∨ a = 2 * n + 1 := by
    refine ⟨a / 2, ?_⟩
    have hd := Nat.div_add_mod a 2
    have hm := Nat.mod_lt a (show 0 < 2 by omega)
    omega
  obtain ⟨n, hn⟩ := hform r
  obtain ⟨m, hm⟩ := hform t
  rcases hn with rfl | rfl <;> rcases hm with rfl | rfl
  · constructor
    · intro _; omega
    · intro _
      exact ⟨((kummerGeometricExponentEvenEquiv c (p ^ (s + 1) - 2) (p ^ (s + 1)) n).trans
        (kummerGeometricExponentEvenEquiv c (p ^ (s + 1) - 2) (p ^ (s + 1)) m).symm).restrictScalars _⟩
  · constructor
    · intro h; exact (squareKummerEvenOdd_not_equiv p s c n m h).elim
    · intro h; omega
  · constructor
    · rintro ⟨e⟩
      exact (squareKummerEvenOdd_not_equiv p s c m n ⟨e.symm⟩).elim
    · intro h; omega
  · constructor
    · intro _; omega
    · intro _
      exact ⟨((kummerGeometricExponentOddEquiv c (p ^ (s + 1) - 2) (p ^ (s + 1)) n).trans
        (kummerGeometricExponentOddEquiv c (p ^ (s + 1) - 2) (p ^ (s + 1)) m).symm).restrictScalars _⟩

/-- Rationality over the stated constant field is equivalent to even geometric-sum length. -/
theorem squareKummerGeometricField_rational_iff_even (r : ℕ) :
    Nonempty (SquareKummerGeometricField p s c r ≃ₐ[SquareConstantField p s]
      RatFunc (SquareConstantField p s)) ↔ r % 2 = 0 := by
  let e0 : RatFunc (SquareConstantField p s) ≃ₐ[SquareConstantField p s]
      SquareKummerGeometricField p s c 0 :=
    kummerEvenGeometricRationalEquiv c (p ^ (s + 1) - 2) (p ^ (s + 1)) 0
  constructor
  · rintro ⟨e⟩
    exact (squareKummerGeometricField_equiv_iff_parity p s c r 0).mp ⟨e.trans e0⟩
  · intro hr
    obtain ⟨e⟩ := (squareKummerGeometricField_equiv_iff_parity p s c r 0).mpr hr
    exact ⟨e.trans e0.symm⟩

#print axioms squareKummerGeometricField_equiv_iff_parity
#print axioms squareKummerGeometricField_rational_iff_even
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
