import GaloisForLFunctions.HTGeometry.CoppoFourierCircuit
import GaloisForLFunctions.HTGeometry.TwoProjectionQuantumWalk

/-!
# Chebyshev propagation on the finite Fourier core

The translation identity in Bhakta–Bhattacharjya, equation (4.6),
applies to the actual harmonic shifts of the Josephson Fourier core.
The denominator-free convention is `C_n(2x)=2T_n(x)`.
Its symmetric propagator has exactly two endpoints; the sine companion
recovers their oriented difference.
-/

namespace HTGeometry

/-- Repeating a harmonic translation adds its frequency exactly. -/
theorem coppoFourierShift_pow (k : ℤ) (n : ℕ) :
    coppoFourierShift k ^ n = coppoFourierShift ((n : ℤ) * k) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, coppoFourierShift_zero]
  | succ n ih =>
    rw [pow_succ, ih, coppoFourierShift_mul, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

/-- The cosine recurrence produces the two opposite harmonic translations at every order. -/
theorem coppoFourierShift_cosine (k : ℤ) (n : ℕ) :
    unitaryCosineRecurrence (coppoFourierShift k + coppoFourierShift (-k)) n =
      coppoFourierShift ((n : ℤ) * k) + coppoFourierShift (-((n : ℤ) * k)) := by
  have huv : coppoFourierShift k * coppoFourierShift (-k) = 1 := by
    rw [coppoFourierShift_mul, add_neg_cancel, coppoFourierShift_zero]
  have hvu : coppoFourierShift (-k) * coppoFourierShift k = 1 := by
    rw [coppoFourierShift_mul, neg_add_cancel, coppoFourierShift_zero]
  rw [unitaryCosineRecurrence_add_inversePair _ _ huv hvu,
    coppoFourierShift_pow, coppoFourierShift_pow, mul_neg]

/-- The sine recurrence factors the oriented endpoint difference through the first shift difference. -/
theorem coppoFourierShift_sine (k : ℤ) (n : ℕ) :
    unitarySineRecurrence (coppoFourierShift k + coppoFourierShift (-k)) n *
        (coppoFourierShift k - coppoFourierShift (-k)) =
      coppoFourierShift ((n : ℤ) * k) - coppoFourierShift (-((n : ℤ) * k)) := by
  have huv : coppoFourierShift k * coppoFourierShift (-k) = 1 := by
    rw [coppoFourierShift_mul, add_neg_cancel, coppoFourierShift_zero]
  have hvu : coppoFourierShift (-k) * coppoFourierShift k = 1 := by
    rw [coppoFourierShift_mul, neg_add_cancel, coppoFourierShift_zero]
  rw [unitarySineRecurrence_mul_sub_inversePair _ _ huv hvu,
    coppoFourierShift_pow, coppoFourierShift_pow, mul_neg]

/-- A Fourier basis state propagates to precisely the two endpoint frequencies. -/
theorem coppoFourierShift_cosine_basis (k m : ℤ) (n : ℕ) :
    unitaryCosineRecurrence (coppoFourierShift k + coppoFourierShift (-k)) n
        (Finsupp.single m 1) =
      Finsupp.single (m + (n : ℤ) * k) 1 + Finsupp.single (m - (n : ℤ) * k) 1 := by
  rw [coppoFourierShift_cosine]
  simp only [LinearMap.add_apply, coppoFourierShift_basis, sub_eq_add_neg]

end HTGeometry

#print axioms HTGeometry.coppoFourierShift_cosine
#print axioms HTGeometry.coppoFourierShift_sine
#print axioms HTGeometry.coppoFourierShift_cosine_basis
