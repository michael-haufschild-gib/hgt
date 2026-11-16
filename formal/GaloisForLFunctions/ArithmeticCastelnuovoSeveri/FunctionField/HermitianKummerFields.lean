import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTraceFieldEmbedding
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizedPrimeFibers

/-!
# Hermitian function fields and trace covers over the square field

The trace-zero normalization converts the source radical equation to
`v^(Q+1)=u^Q+u`. Trace coordinates construct the covering directly over
the prescribed square constant field when the exponent length divides
the full Frobenius length.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis

/-- The square-field index for a positive multiple of the exponent length. -/
def hermitianKummerCoverIndex (d r m : ℕ) : ℕ :=
  kummerSquareIndex d ((r + 1) * (m + 1) - 1)

/-- The cover index realizes the exact product of the three positive degree parameters. -/
theorem hermitianKummerCoverIndex_succ (d r m : ℕ) :
    hermitianKummerCoverIndex d r m + 1 = (d + 1) * (r + 1) * (m + 1) := by
  rw [hermitianKummerCoverIndex, kummerSquareIndex_succ,
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos m))]
  simp only [Nat.succ_eq_add_one, Nat.mul_assoc]

variable (p : ℕ) [Fact p.Prime] (d r m : ℕ)
local notation "s" => hermitianKummerCoverIndex d r m
local notation "K" => SquareConstantField p s
local notation "H" => HermitianKummerField p s
local notation "c" => (kummerTraceConstant p s)⁻¹
local notation "Q" => p ^ (s + 1)
local notation "R" => kummerExponent (p ^ (d + 1)) (r + 1)
local notation "x" => algebraMap K[X] H X
local notation "v" => AdjoinRoot.root (kummerBranchFieldPolynomial c (Q - 2) 1 Q)

private instance normalizedTraceCover_charP : CharP H p :=
  charP_of_injective_algebraMap (algebraMap K H).injective p

private def normalizedTraceCoordinate : H :=
  frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) x ^ R

private theorem normalizedTraceCoordinate_transcendental :
    Transcendental K (normalizedTraceCoordinate p d r m) := by
  have he : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
  have ht := frobeniusTraceSum_transcendental p ((d + 1) * (r + 1) - 1) m
    (kummerBranchField_coordinate_transcendental c (Q - 2) 1 Q)
  rw [he] at ht
  have hR : 0 < R := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (r + 1)) =>
      Nat.zero_le ((p ^ (d + 1)) ^ i)) (Finset.mem_range.mpr (Nat.succ_pos r))
    exact lt_of_lt_of_le Nat.zero_lt_one (by simpa only [kummerExponent, pow_zero] using h)
  intro h
  exact ht (IsIntegral.of_pow hR h.isIntegral).isAlgebraic

private theorem normalizedTraceCover_equation :
    (v ^ R) ^ (Q + 1) = algebraMap K H (c ^ R) * normalizedTraceCoordinate p d r m *
      (1 - normalizedTraceCoordinate p d r m ^ (p ^ (d + 1) - 2 + 1)) ^ R := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hv : v ^ (Q + 1) = algebraMap K H c * (x - x ^ Q) := by
    have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
    have hbranch : x * (1 - x ^ (Q - 2 + 1)) = x - x ^ Q := by
      rw [show Q - 2 + 1 = Q - 1 by omega, mul_sub, mul_one, ← pow_succ',
        Nat.sub_add_cancel (by omega : 1 ≤ Q)]
    rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply, kummerBranch]
    simp only [map_mul, map_pow, map_sub, map_one, pow_one]
    change algebraMap K H c * x * (1 - x ^ (Q - 2 + 1)) = _
    rw [mul_assoc, hbranch]
  have hQ : Q = p ^ ((d + 1) * (r + 1) * (m + 1)) :=
    congrArg (p ^ ·) (hermitianKummerCoverIndex_succ d r m)
  change (v ^ R) ^ (Q + 1) = algebraMap K H ((c : K) ^ R) *
    normalizedTraceCoordinate p d r m *
    (1 - normalizedTraceCoordinate p d r m ^ (p ^ (d + 1) - 2 + 1)) ^ R
  rw [map_pow, show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega,
    ← pow_mul v R (Q + 1), Nat.mul_comm R (Q + 1), pow_mul v (Q + 1) R, hv]
  exact (congrArg (fun N : ℕ => (algebraMap K H c * (x - x ^ N)) ^ R) hQ).trans
    (trace_kummer_identity p (d + 1) (r + 1) (m + 1) (algebraMap K H c) x)

/-- Every exponent length dividing the Frobenius length has an actual Hermitian function-field cover. -/
def normalizedKummerHermitianEmbedding : NormalizedKummerField p s d r →ₐ[K] H :=
  kummerBranchFieldHomOfCoordinates (c ^ R) (p ^ (d + 1) - 2) R Q
    (normalizedTraceCoordinate p d r m) (v ^ R)
    (normalizedTraceCoordinate_transcendental p d r m)
    (normalizedTraceCover_equation p d r m)

/-- The Hermitian trace-cover homomorphism is injective. -/
theorem normalizedKummerHermitianEmbedding_injective :
    Function.Injective (normalizedKummerHermitianEmbedding p d r m) :=
  (normalizedKummerHermitianEmbedding p d r m).injective

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
