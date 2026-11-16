import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerReflectionParameters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizedPrimeFibers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceEquivalences

/-!
# Reflection isomorphisms of finite-field Kummer curves

For `Q=q^(n+1)`, the exponents indexed by `r` and `2n-r` yield
isomorphic function fields over the same constants. The three-point
presentation makes this an explicit reciprocal-coordinate isomorphism.
It also identifies all intrinsic places and rational places.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)

/-- The prime-power three-point presentation has branch exponent `q^(r+1)-1`. -/
def primePowerKummerPowerModelEquiv
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ) (r : ℕ) :
    KummerBranchField (η⁻¹ ^ ((p ^ (d + 1)) ^ (r + 1) - 1)) 0
      ((p ^ (d + 1)) ^ (r + 1) - 1) (primePowerKummerCyclicDegree p d n - 1)
      ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
    SquareKummerField p (kummerSquareIndex d n)
      (η⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)) := by
  let q := p ^ (d + 1)
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hm : q - 2 + 1 = q - 1 := by omega
  have hgeom : kummerExponent q (r + 1) * (q - 1) = q ^ (r + 1) - 1 := by
    have h := kummerExponent_mul_add (q - 1) (r + 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ q)] at h
    omega
  have e := kummerThreePointEquiv (η⁻¹ ^ kummerExponent q (r + 1)) (q - 2)
    (kummerExponent q (r + 1)) (p ^ (kummerSquareIndex d n + 1))
  change KummerBranchField ((η⁻¹ ^ kummerExponent q (r + 1)) ^ (q - 2 + 1)) 0
    (kummerExponent q (r + 1) * (q - 2 + 1))
    ((p ^ (kummerSquareIndex d n + 1) + 1) * (q - 2 + 1) - 1)
    ≃ₐ[SquareConstantField p (kummerSquareIndex d n)] _ at e
  rw [hm, ← pow_mul, hgeom] at e
  exact e

/-- Complementary exponent parameters give isomorphic actual Kummer function fields. -/
def primePowerKummerReflectionEquiv
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ) (r : Fin (2 * n + 1)) :
    SquareKummerField p (kummerSquareIndex d n)
      (η⁻¹ ^ kummerExponent (p ^ (d + 1)) (r.val + 1))
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r.val + 1))
      ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
    SquareKummerField p (kummerSquareIndex d n)
      (η⁻¹ ^ kummerExponent (p ^ (d + 1)) (2 * n - r.val + 1))
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (2 * n - r.val + 1)) := by
  have hM : primePowerKummerCyclicDegree p d n - 1 + 1 = primePowerKummerCyclicDegree p d n :=
    Nat.sub_add_cancel (primePowerKummerCyclicDegree_pos p d n)
  have hrel := primePowerKummer_reflection_exponent_relation p d n r
  rw [← hM] at hrel
  let e := kummerReciprocalEquiv
    (η⁻¹ ^ ((p ^ (d + 1)) ^ (r.val + 1) - 1))
    ((p ^ (d + 1)) ^ (r.val + 1) - 1)
    ((p ^ (d + 1)) ^ (2 * n - r.val + 1) - 1)
    (primePowerKummerCyclicDegree p d n - 1)
    (kummerExponent (p ^ (d + 1)) (n + 1)) hrel
  have e' :
      KummerBranchField (η⁻¹ ^ ((p ^ (d + 1)) ^ (2 * n - r.val + 1) - 1)) 0
        ((p ^ (d + 1)) ^ (2 * n - r.val + 1) - 1) (primePowerKummerCyclicDegree p d n - 1)
        ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
      KummerBranchField (η⁻¹ ^ ((p ^ (d + 1)) ^ (r.val + 1) - 1)) 0
        ((p ^ (d + 1)) ^ (r.val + 1) - 1) (primePowerKummerCyclicDegree p d n - 1) := by
    rw [← primePowerKummer_reflection_coefficient p d n η r]
    exact e
  exact (primePowerKummerPowerModelEquiv p d n η r.val).symm.trans
    (e'.symm.trans (primePowerKummerPowerModelEquiv p d n η (2 * n - r.val)))

/-- Reflection is an isomorphism for the canonical normalized trace-constant family. -/
def normalizedKummerReflectionEquiv (r : Fin (2 * n + 1)) :
    NormalizedKummerField p (kummerSquareIndex d n) d r.val
      ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
    NormalizedKummerField p (kummerSquareIndex d n) d (2 * n - r.val) :=
  primePowerKummerReflectionEquiv p d n (kummerTraceConstant p (kummerSquareIndex d n)) r

/-- Reflection bijects the actual rational valuation places over the fixed constant field. -/
def normalizedKummerReflectionRationalPlacesEquiv (r : Fin (2 * n + 1)) :
    RationalConstantFieldPlaces (SquareConstantField p (kummerSquareIndex d n))
      (NormalizedKummerField p (kummerSquareIndex d n) d r.val) ≃
    RationalConstantFieldPlaces (SquareConstantField p (kummerSquareIndex d n))
      (NormalizedKummerField p (kummerSquareIndex d n) d (2 * n - r.val)) :=
  rationalConstantFieldPlaceEquiv (normalizedKummerReflectionEquiv p d n r)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
