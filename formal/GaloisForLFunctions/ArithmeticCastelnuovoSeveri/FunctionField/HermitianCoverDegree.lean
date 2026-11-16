import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianKummerFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTraceCoverDegree

/-!
# Degree of the normalized Hermitian cover

Transporting the trace-power field embedding to the prescribed square
constant field preserves its exact extension degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime]

private theorem traceCover_finrank_transport {K : Type*} [Field K] [CharP K p]
    (c : Kˣ) (d r m Q : ℕ) (hQ : Q = p ^ ((d + 1) * (r + 1) * (m + 1))) :
    Module.finrank
      (Eq.mpr (congrArg (fun N : ℕ =>
        KummerBranchField (c ^ kummerExponent (p ^ (d + 1)) (r + 1))
          (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)) N →ₐ[K]
        KummerBranchField c (N - 2) 1 N) hQ)
        (hermitianKummerFieldHom p c d r m)).fieldRange
      (KummerBranchField c (Q - 2) 1 Q) =
        p ^ ((d + 1) * (r + 1) * m) * kummerExponent (p ^ (d + 1)) (r + 1) := by
  subst Q
  exact hermitianKummerFieldHom_finrank p c d r m

/-- The canonical normalized trace cover has the exact degree of its trace-power coordinate. -/
theorem normalizedKummerHermitianEmbedding_finrank (d r m : ℕ) :
    Module.finrank (normalizedKummerHermitianEmbedding p d r m).fieldRange
      (HermitianKummerField p (hermitianKummerCoverIndex d r m)) =
        p ^ ((d + 1) * (r + 1) * m) * kummerExponent (p ^ (d + 1)) (r + 1) := by
  exact traceCover_finrank_transport p
    (kummerTraceConstant p (hermitianKummerCoverIndex d r m))⁻¹ d r m _
    (congrArg (p ^ ·) (hermitianKummerCoverIndex_succ d r m))


end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
