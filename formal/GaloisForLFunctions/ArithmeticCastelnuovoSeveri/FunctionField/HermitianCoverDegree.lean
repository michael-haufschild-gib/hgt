import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianCoverCoordinates
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPolynomialCoverDegree

/-!
# Degree of the normalized Hermitian cover

The two radical degrees agree over the prescribed square constant field.
The polynomial-coordinate tower formula therefore identifies the cover
degree with the degree of the trace-power polynomial.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime]

/-- The canonical normalized trace cover has the exact degree of its trace-power coordinate. -/
theorem normalizedKummerHermitianEmbedding_finrank (d r m : ℕ) :
    Module.finrank (normalizedKummerHermitianEmbedding p d r m).fieldRange
      (HermitianKummerField p (hermitianKummerCoverIndex d r m)) =
        p ^ ((d + 1) * (r + 1) * m) * kummerExponent (p ^ (d + 1)) (r + 1) := by
  let s := hermitianKummerCoverIndex d r m
  let K := SquareConstantField p s
  let H := HermitianKummerField p s
  let c := (kummerTraceConstant p s)⁻¹
  let Q := p ^ (s + 1)
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  let f := normalizedKummerHermitianEmbedding p d r m
  let x := algebraMap K[X] H X
  let P : K[X] := frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) X ^ R
  have hP : f (algebraMap K[X] _ X) = aeval x P := by
    rw [normalizedKummerHermitianEmbedding_coordinate]
    change frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) x ^ R =
      aeval x (frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) X ^ R)
    simp only [frobeniusTraceSum, map_pow, map_sum, aeval_X]
  have hdegree : P.natDegree = p ^ ((d + 1) * (r + 1) * m) * R := by
    dsimp only [P]
    rw [natDegree_pow]
    have he : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
      Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
    have ht := frobeniusTraceSum_polynomial_natDegree (K := K) p ((d + 1) * (r + 1) - 1) m
    rw [he] at ht
    rw [ht, Nat.mul_comm]
  exact (kummerBranchField_polynomial_cover_finrank (c ^ R) c
    (p ^ (d + 1) - 2) R (Q - 2) 1 Q f P hP).trans hdegree

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
