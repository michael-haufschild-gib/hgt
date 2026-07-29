import GaloisForLFunctions.HTGeometry.SourceOddPositivitySquareLaw

/-!
# Reciprocal squares conserve every positive trace moment

For any finite rectangular complex transfer `D`, the positive matrices `Dᴴ * D` and `D * Dᴴ`
live on different sides but have equal traces of every positive power. This is the trace-moment
form of equality of their nonzero singular spectral data.

The proof is exact rectangular matrix algebra using cyclicity of trace. The theorem is classical
and does not identify either side with quantum, gauge, causal, or gravitational physics.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

set_option maxRecDepth 4096

/--
Move a positive power of the domain reciprocal square across its rectangular transfer.
-/
theorem reciprocalDomainSquare_pow_succ
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n ℂ) (k : ℕ) :
    (reciprocalDomainSquare D) ^ (k + 1) =
      Dᴴ * (reciprocalCodomainSquare D) ^ k * D := by
  induction k with
  | zero =>
      simp [reciprocalDomainSquare, reciprocalCodomainSquare]
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ, ih]
      simp only [reciprocalDomainSquare, reciprocalCodomainSquare]
      rw [pow_succ]
      simp only [Matrix.mul_assoc]

/--
**Reciprocal spectral-moment conservation.** Every positive power trace agrees on the two sides
of a finite rectangular transfer.
-/
theorem reciprocalSquare_trace_pow_succ_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n ℂ) (k : ℕ) :
    ((reciprocalDomainSquare D) ^ (k + 1)).trace =
      ((reciprocalCodomainSquare D) ^ (k + 1)).trace := by
  rw [reciprocalDomainSquare_pow_succ D k]
  calc
    (Dᴴ * (reciprocalCodomainSquare D) ^ k * D).trace =
        (D * Dᴴ * (reciprocalCodomainSquare D) ^ k).trace :=
      Matrix.trace_mul_cycle Dᴴ ((reciprocalCodomainSquare D) ^ k) D
    _ = ((reciprocalCodomainSquare D) ^ (k + 1)).trace := by
      simp [reciprocalCodomainSquare, pow_succ']

end GaloisForLFunctions.HTGeometry
