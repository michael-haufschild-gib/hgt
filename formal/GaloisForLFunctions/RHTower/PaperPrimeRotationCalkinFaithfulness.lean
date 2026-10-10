import GaloisForLFunctions.HTGeometry.PaperRotationCalkinFaithfulness
import GaloisForLFunctions.RHTower.PaperPrimeRotationNormRate

/-!
# The native prime rotation algebra survives the compact quotient

The entire closed algebra of the native prime phase retains its norm after quotienting by compact
operators. In particular, the literal prime commutator has the same first-order essential-norm
coefficient as its ordinary norm: integer area times the prime logarithm.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry Filter Topology
open scoped ENNReal Classical

/-- The full closed rotation algebra for the actual corpus-native prime phase. -/
def paperPrimeRotationAlgebra (p : Nat.Primes) (q : ℕ) :
    StarSubalgebra ℂ (PaperRotationHilbert →L[ℂ] PaperRotationHilbert) :=
  paperRotationAlgebra (paperPrimeRotationFrequency p q)

theorem paperPrimeRotationCommutator_mem_algebra
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    paperPrimeRotationCommutator p q a b c d ∈ paperPrimeRotationAlgebra p q := by
  have hA := paperRotationWord_mem_algebra (paperPrimeRotationFrequency p q) a b
  have hB := paperRotationWord_mem_algebra (paperPrimeRotationFrequency p q) c d
  exact (paperRotationAlgebra _).sub_mem
    ((paperRotationAlgebra _).mul_mem hA hB) ((paperRotationAlgebra _).mul_mem hB hA)

/-- The full prime algebra retains all operator norms in the quotient. -/
theorem paperPrimeRotationAlgebra_compactIdealDistance
    (p : Nat.Primes) (q : ℕ) (A : paperPrimeRotationAlgebra p q) :
    compactIdealDistance A.1 = ‖A.1‖ :=
  paperRotationAlgebra_compactIdealDistance (paperPrimeRotationFrequency p q) A

/-- Distinct prime-algebra elements cannot become equal after a compact correction. -/
theorem paperPrimeRotationAlgebra_compact_sub_iff_eq
    (p : Nat.Primes) (q : ℕ) (A B : paperPrimeRotationAlgebra p q) :
    IsCompactOperator (A.1 - B.1) ↔ A = B :=
  paperRotationAlgebra_compact_sub_iff_eq (paperPrimeRotationFrequency p q) A B

/-- Every nonzero member of the full native prime algebra has infinite paper ideal cost. -/
theorem paperPrimeRotationAlgebra_traceCost
    (p : Nat.Primes) (q : ℕ) (A : paperPrimeRotationAlgebra p q) :
    compactOperatorTraceCost PaperRotationHilbert A.1 = if A = 0 then 0 else ∞ :=
  paperRotationAlgebra_traceCost (paperPrimeRotationFrequency p q) A

/-- Every compact correction leaves the literal prime commutator norm bounded below by its
uncorrected norm, at every clock denominator. -/
theorem paperPrimeRotationCommutator_norm_le_sub_compact
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) :
    ‖paperPrimeRotationCommutator p q a b c d‖ ≤
      ‖paperPrimeRotationCommutator p q a b c d - K.1‖ :=
  paperRotationAlgebra_norm_le_sub_compact (paperPrimeRotationFrequency p q)
    ⟨_, paperPrimeRotationCommutator_mem_algebra p q a b c d⟩ K

theorem paperPrimeRotationCommutator_compactIdealDistance
    (p : Nat.Primes) (q : ℕ) (a b c d : ℤ) :
    compactIdealDistance (paperPrimeRotationCommutator p q a b c d) =
      ‖paperPrimeRotationCommutator p q a b c d‖ :=
  paperPrimeRotationAlgebra_compactIdealDistance p q
    ⟨_, paperPrimeRotationCommutator_mem_algebra p q a b c d⟩

/-- The signed-area prime-log coefficient also survives in the essential norm. -/
theorem paperPrimeRotationCommutator_scaled_essentialNorm_tendsto
    (p : Nat.Primes) (a b c d : ℤ) :
    Tendsto (fun q : ℕ => ((q : ℝ) + 1) *
      compactIdealDistance (paperPrimeRotationCommutator p (q + 1) a b c d))
      atTop (𝓝 (paperPrimeRotationNormSlope p a b c d)) := by
  simpa only [paperPrimeRotationCommutator_compactIdealDistance] using
    paperPrimeRotationCommutator_scaled_norm_tendsto p a b c d

/-- The prime logarithm is visible after compact operators have been quotiented out. -/
theorem paperPrimeRotationPrimitive_scaled_essentialNorm_tendsto (p : Nat.Primes) :
    Tendsto (fun q : ℕ => ((q : ℝ) + 1) *
      compactIdealDistance (paperPrimeRotationCommutator p (q + 1) 0 1 1 0))
      atTop (𝓝 (Real.log p)) := by
  simpa only [paperPrimeRotationCommutator_compactIdealDistance] using
    paperPrimeRotationPrimitive_scaled_norm_tendsto p

/-- Primitive essential-norm profiles distinguish primes after passing to the compact quotient. -/
theorem paperPrimeRotationPrimitive_essentialNorm_profile_eq_iff (p r : Nat.Primes) :
    (∀ q : ℕ, compactIdealDistance (paperPrimeRotationCommutator p (q + 1) 0 1 1 0) =
      compactIdealDistance (paperPrimeRotationCommutator r (q + 1) 0 1 1 0)) ↔ p = r := by
  simpa only [paperPrimeRotationCommutator_compactIdealDistance] using
    paperPrimeRotationPrimitive_norm_profile_eq_iff p r

end

end RHTower
