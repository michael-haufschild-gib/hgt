import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTraceFieldEmbedding
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizedPrimeFibers

/-!
# Hermitian function fields and trace covers over the square field

The trace-zero normalization converts the source radical equation to
`v^(Q+1)=u^Q+u`. When the Kummer exponent length divides the Frobenius
length, the trace substitution gives an actual embedding into this
Hermitian function field over the same square constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime]

/-- The square-field index for a positive multiple of the exponent length. -/
def hermitianKummerCoverIndex (d r m : ℕ) : ℕ :=
  kummerSquareIndex d ((r + 1) * (m + 1) - 1)

/-- The cover index realizes the exact product of the three positive degree parameters. -/
theorem hermitianKummerCoverIndex_succ (d r m : ℕ) :
    hermitianKummerCoverIndex d r m + 1 = (d + 1) * (r + 1) * (m + 1) := by
  rw [hermitianKummerCoverIndex, kummerSquareIndex_succ,
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos m))]
  ring

/-- Every exponent length dividing the Frobenius length has an actual Hermitian function-field cover. -/
def normalizedKummerHermitianEmbedding (d r m : ℕ) :
    NormalizedKummerField p (hermitianKummerCoverIndex d r m) d r
      →ₐ[SquareConstantField p (hermitianKummerCoverIndex d r m)]
    HermitianKummerField p (hermitianKummerCoverIndex d r m) := by
  let s := hermitianKummerCoverIndex d r m
  have hs : s + 1 = (d + 1) * (r + 1) * (m + 1) := hermitianKummerCoverIndex_succ d r m
  change KummerBranchField
    ((kummerTraceConstant p s)⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
    (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)) (p ^ (s + 1))
    →ₐ[SquareConstantField p s]
    KummerBranchField (kummerTraceConstant p s)⁻¹ (p ^ (s + 1) - 2) 1 (p ^ (s + 1))
  rw [hs]
  exact hermitianKummerFieldHom p (kummerTraceConstant p s)⁻¹ d r m

/-- The Hermitian trace-cover homomorphism is injective. -/
theorem normalizedKummerHermitianEmbedding_injective (d r m : ℕ) :
    Function.Injective (normalizedKummerHermitianEmbedding p d r m) :=
  (normalizedKummerHermitianEmbedding p d r m).injective

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
