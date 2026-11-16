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

private theorem traceCover_coordinates_transport {K₀ : Type*} [Field K₀] [CharP K₀ p]
    (c : K₀ˣ) (Q : ℕ) (hQ : Q = p ^ ((d + 1) * (r + 1) * (m + 1))) :
    let f := Eq.mpr (congrArg (fun N : ℕ =>
      KummerBranchField (c ^ kummerExponent (p ^ (d + 1)) (r + 1))
        (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)) N →ₐ[K₀]
      KummerBranchField c (N - 2) 1 N) hQ)
      (hermitianKummerFieldHom p c d r m)
    f (algebraMap K₀[X] _ X) =
      frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1)
        (algebraMap K₀[X] (KummerBranchField c (Q - 2) 1 Q) X) ^
          kummerExponent (p ^ (d + 1)) (r + 1) ∧
    f (AdjoinRoot.root (kummerBranchFieldPolynomial
      (c ^ kummerExponent (p ^ (d + 1)) (r + 1)) (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) (r + 1)) Q)) =
      AdjoinRoot.root (kummerBranchFieldPolynomial c (Q - 2) 1 Q) ^
        kummerExponent (p ^ (d + 1)) (r + 1) := by
  subst Q
  exact ⟨hermitianKummerFieldHom_coordinate p c d r m,
    hermitianKummerFieldHom_root p c d r m⟩

/-- The normalized covering coordinate is the geometric-exponent power of the relative trace. -/
theorem normalizedKummerHermitianEmbedding_coordinate :
    normalizedKummerHermitianEmbedding p d r m
      (algebraMap K[X] (NormalizedKummerField p s d r) X) =
    frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1)
      (algebraMap K[X] H X) ^ kummerExponent (p ^ (d + 1)) (r + 1) := by
  exact (traceCover_coordinates_transport p d r m (kummerTraceConstant p s)⁻¹ _
    (congrArg (p ^ ·) (hermitianKummerCoverIndex_succ d r m))).1

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
  exact (traceCover_coordinates_transport p d r m (kummerTraceConstant p s)⁻¹ _
    (congrArg (p ^ ·) (hermitianKummerCoverIndex_succ d r m))).2

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
