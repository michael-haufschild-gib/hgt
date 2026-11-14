import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import Mathlib.Algebra.Ring.GeomSum

/-!
# Weighted cyclic companion resolvents

The relation `C^(n+1) = a I` replaces the permutation denominator `1-s^(n+1)`
by `1-a*s^(n+1)`. The same finite numerator works at every value of the cyclic
parameter, including the nilpotent specialization `a=0`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped BigOperators

variable {L : Type*} [Field L]

/-- The finite geometric numerator for the weighted cyclic companion. -/
def cyclicCompanionNumerator (n : ℕ) (a s : L) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  ∑ k ∈ Finset.range (n + 1), (s • cyclicCompanionMatrix n a) ^ k

/-- Two-sided denominator clearing, valid even on the singular parameter locus. -/
theorem cyclicCompanionNumerator_factorization (n : ℕ) (a s : L) :
    (1 - s • cyclicCompanionMatrix n a) * cyclicCompanionNumerator n a s =
        (1 - a * s ^ (n + 1)) • 1 ∧
      cyclicCompanionNumerator n a s * (1 - s • cyclicCompanionMatrix n a) =
        (1 - a * s ^ (n + 1)) • 1 := by
  unfold cyclicCompanionNumerator
  rw [mul_neg_geom_sum, geom_sum_mul_neg, smul_pow, cyclicCompanionMatrix_pow_succ]
  constructor <;> simp only [smul_smul, mul_comm (s ^ (n + 1)) a, sub_smul, one_smul]

/-- At the truncated specialization the numerator is an actual inverse for every scalar. -/
def cyclicCompanionTruncatedResolventUnit (n : ℕ) (s : L) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) L)ˣ where
  val := 1 - s • cyclicCompanionMatrix n 0
  inv := cyclicCompanionNumerator n 0 s
  val_inv := by simpa only [zero_mul, sub_zero, one_smul] using
    (cyclicCompanionNumerator_factorization n 0 s).1
  inv_val := by simpa only [zero_mul, sub_zero, one_smul] using
    (cyclicCompanionNumerator_factorization n 0 s).2

end GaloisForLFunctions.HTGeometry.ABHN

#print axioms GaloisForLFunctions.HTGeometry.ABHN.cyclicCompanionNumerator_factorization
#print axioms GaloisForLFunctions.HTGeometry.ABHN.cyclicCompanionTruncatedResolventUnit
