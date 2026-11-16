import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianAffineAutomorphisms
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianCoverCoordinates
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTraceParameters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldHomExt

/-!
# Deck automorphisms of the normalized Hermitian trace cover

Radical scalings by roots of the geometric exponent and trace-zero
translations preserve both pulled-back Kummer generators. They give
distinct automorphisms over the actual image field of the covering.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d r m : ℕ)
local notation "s" => hermitianKummerCoverIndex d r m
local notation "K" => SquareConstantField p s
local notation "H" => HermitianKummerField p s
local notation "R" => kummerExponent (p ^ (d + 1)) (r + 1)
local notation "φ" => normalizedKummerHermitianEmbedding p d r m

private instance hermitianCover_charP : CharP H p :=
  charP_of_injective_algebraMap (algebraMap K H).injective p

/-- The scaling and translation parameters of the Hermitian trace cover. -/
abbrev HermitianCoverParameters := rootsOfUnity R K × HermitianCoverTraceKernel p d r m

/-- Each covering parameter gives a constant-field automorphism of the Hermitian source. -/
def hermitianCoverDeckAut (u : HermitianCoverParameters p d r m) : H ≃ₐ[K] H :=
  hermitianAffineAut p s (kummerTraceConstant p s)⁻¹ u.1.val
    ⟨u.2.val, hermitianCoverTraceKernel_fixed p d r m u.2⟩

private theorem cover_scaling_pow (u : HermitianCoverParameters p d r m) :
    ((u.1.val : K) ^ (p ^ (s + 1) + 1)) ^ R = 1 := by
  rw [← pow_mul, Nat.mul_comm (p ^ (s + 1) + 1) R, pow_mul,
    (show (u.1.val : K) ^ R = 1 from congrArg Units.val u.1.property), one_pow]

private theorem cover_scaling_fixed (u : HermitianCoverParameters p d r m) :
    ((u.1.val : K) ^ (p ^ (s + 1) + 1)) ^ p ^ ((d + 1) * (r + 1)) =
      (u.1.val : K) ^ (p ^ (s + 1) + 1) := by
  rw [← pow_mul, Nat.mul_comm (p ^ (s + 1) + 1) (p ^ ((d + 1) * (r + 1))),
    pow_mul, hermitianCoverScalar_fixed]

/-- Every covering parameter fixes the pulled-back rational Kummer coordinate. -/
theorem hermitianCoverDeckAut_fixes_coordinate (u : HermitianCoverParameters p d r m) :
    hermitianCoverDeckAut p d r m u (φ (algebraMap K[X] (NormalizedKummerField p s d r) X)) =
      φ (algebraMap K[X] (NormalizedKummerField p s d r) X) := by
  let σ := hermitianCoverDeckAut p d r m u
  let a : K := (u.1.val : K) ^ (p ^ (s + 1) + 1)
  let x := algebraMap K[X] H X
  have hσ : σ x = algebraMap K H a * x + algebraMap K H u.2.val :=
    hermitianAffineHom_coordinate p s (kummerTraceConstant p s)⁻¹ u.1.val
      ⟨u.2.val, hermitianCoverTraceKernel_fixed p d r m u.2⟩
  have ha : (algebraMap K H a) ^ p ^ ((d + 1) * (r + 1)) = algebraMap K H a := by
    rw [← map_pow, cover_scaling_fixed]
  have hb : frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1)
      (algebraMap K H u.2.val) = 0 := by
    rw [← frobeniusTraceSum_map p (algebraMap K H), u.2.property, map_zero]
  have htrace : σ (frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) x) =
      frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) (σ x) :=
    frobeniusTraceSum_map p σ.toRingHom ((d + 1) * (r + 1)) (m + 1) x
  rw [normalizedKummerHermitianEmbedding_coordinate]
  change σ (frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) x ^ R) = _
  rw [map_pow, htrace, hσ,
    frobeniusTraceSum_affine p ((d + 1) * (r + 1)) (m + 1)
      (algebraMap K H a) (algebraMap K H u.2.val) x ha hb,
    mul_pow, ← map_pow, cover_scaling_pow, map_one, one_mul]

/-- Every covering parameter fixes the pulled-back Kummer radical. -/
theorem hermitianCoverDeckAut_fixes_root (u : HermitianCoverParameters p d r m) :
    hermitianCoverDeckAut p d r m u
      (φ (AdjoinRoot.root (kummerBranchFieldPolynomial ((kummerTraceConstant p s)⁻¹ ^ R)
        (p ^ (d + 1) - 2) R (p ^ (s + 1))))) =
    φ (AdjoinRoot.root (kummerBranchFieldPolynomial ((kummerTraceConstant p s)⁻¹ ^ R)
      (p ^ (d + 1) - 2) R (p ^ (s + 1)))) := by
  rw [normalizedKummerHermitianEmbedding_root, map_pow]
  change (hermitianAffineHom p s (kummerTraceConstant p s)⁻¹ u.1.val
    ⟨u.2.val, hermitianCoverTraceKernel_fixed p d r m u.2⟩
      (AdjoinRoot.root (kummerBranchFieldPolynomial (kummerTraceConstant p s)⁻¹
        (p ^ (s + 1) - 2) 1 (p ^ (s + 1))))) ^ R = _
  rw [hermitianAffineHom_root, mul_pow, ← map_pow,
    (show (u.1.val : K) ^ R = 1 from congrArg Units.val u.1.property), map_one, one_mul]

/-- The two fixed generator images force every element of the covering field to be fixed. -/
theorem hermitianCoverDeckAut_fixes_embedding (u : HermitianCoverParameters p d r m)
    (x : NormalizedKummerField p s d r) :
    hermitianCoverDeckAut p d r m u (φ x) = φ x := by
  have h := kummerBranchField_algHom_ext ((kummerTraceConstant p s)⁻¹ ^ R)
    (p ^ (d + 1) - 2) R (p ^ (s + 1))
    ((hermitianCoverDeckAut p d r m u).toAlgHom.comp φ) φ
    (hermitianCoverDeckAut_fixes_coordinate p d r m u)
    (hermitianCoverDeckAut_fixes_root p d r m u)
  exact congrArg (fun f => f x) h

/-- The affine deck automorphism fixes the actual image subfield, so is an automorphism over it. -/
def hermitianCoverRelativeAut (u : HermitianCoverParameters p d r m) : H ≃ₐ[(φ).fieldRange] H :=
  { (hermitianCoverDeckAut p d r m u).toRingEquiv with
    commutes' := fun y => by
      obtain ⟨x, hx⟩ := y.property
      change hermitianCoverDeckAut p d r m u y.val = y.val
      rw [← hx]
      exact hermitianCoverDeckAut_fixes_embedding p d r m u x }

/-- Distinct trace-cover parameters produce distinct relative automorphisms. -/
theorem hermitianCoverRelativeAut_injective :
    Function.Injective (hermitianCoverRelativeAut p d r m) := by
  intro u v h
  have hσ : hermitianCoverDeckAut p d r m u = hermitianCoverDeckAut p d r m v := by
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun σ : H ≃ₐ[(φ).fieldRange] H => σ x) h
  have hp : (u.1.val, (⟨u.2.val, hermitianCoverTraceKernel_fixed p d r m u.2⟩ :
      squareFrobeniusFixedField p s)) =
      (v.1.val, (⟨v.2.val, hermitianCoverTraceKernel_fixed p d r m v.2⟩ :
        squareFrobeniusFixedField p s)) :=
    hermitianAffineAut_injective p s (kummerTraceConstant p s)⁻¹ hσ
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hp)
  · exact Subtype.ext (congrArg (fun w : Kˣ × squareFrobeniusFixedField p s => w.2.val) hp)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
