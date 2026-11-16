import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianKummerFields

/-!
# Coordinates of the normalized Hermitian covering

The normalized covering pulls back the rational coordinate to a power
of the relative trace and the radical to the same power of the Hermitian
radical. These formulas retain the stated square constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d r m : ℕ)
local notation "s" => hermitianKummerCoverIndex d r m
local notation "K" => SquareConstantField p s
local notation "H" => HermitianKummerField p s

/-- The normalized covering coordinate is the geometric-exponent power of the relative trace. -/
theorem normalizedKummerHermitianEmbedding_coordinate :
    normalizedKummerHermitianEmbedding p d r m
      (algebraMap K[X] (NormalizedKummerField p s d r) X) =
    frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1)
      (algebraMap K[X] H X) ^ kummerExponent (p ^ (d + 1)) (r + 1) := by
  exact kummerBranchFieldHomOfCoordinates_coordinate _ _ _ _ _ _ _ _

/-- The normalized covering radical is the corresponding power of the Hermitian radical. -/
theorem normalizedKummerHermitianEmbedding_root :
    normalizedKummerHermitianEmbedding p d r m
      (AdjoinRoot.root (kummerBranchFieldPolynomial
        ((kummerTraceConstant p s)⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
        (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))
        (p ^ (s + 1)))) =
    AdjoinRoot.root (kummerBranchFieldPolynomial (kummerTraceConstant p s)⁻¹
      (p ^ (s + 1) - 2) 1 (p ^ (s + 1))) ^
        kummerExponent (p ^ (d + 1)) (r + 1) := by
  exact kummerBranchFieldHomOfCoordinates_root _ _ _ _ _ _ _ _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
