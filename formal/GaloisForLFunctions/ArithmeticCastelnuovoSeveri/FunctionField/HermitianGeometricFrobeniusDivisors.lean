import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricTangentDivisors
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Principal Frobenius relations for all geometric Hermitian divisors

The product of tangent functions, with the signed coefficients of a divisor
as exponents, has divisor `Q D₀ + (Fr D)₀`, where `D₀ = D - deg(D)[infinity]`.
Consequently every Frobenius-invariant signed divisor has `(Q+1)D₀` principal.
The witnesses are units in the actual Hermitian function field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s

/-- The constant function one has zero principal divisor. -/
theorem hermitianGeometricZeroPoleDivisor_one :
    hermitianGeometricZeroPoleDivisor p s 1 = 0 := by
  apply Prod.ext
  · ext w
    change -WithZero.log (w.valuation H 1) = 0
    rw [map_one, WithZero.log_one, neg_zero]
  · change -WithZero.log (hermitianGeometricInfinityValuation p s 1) = 0
    rw [map_one, WithZero.log_one, neg_zero]

/-- Principal divisors add under multiplication of nonzero functions. -/
theorem hermitianGeometricZeroPoleDivisor_mul (f g : H) (hf : f ≠ 0) (hg : g ≠ 0) :
    hermitianGeometricZeroPoleDivisor p s (f * g) =
      hermitianGeometricZeroPoleDivisor p s f + hermitianGeometricZeroPoleDivisor p s g := by
  apply Prod.ext
  · change -finiteValuationDivisor B H (f * g) =
      -finiteValuationDivisor B H f + -finiteValuationDivisor B H g
    rw [finiteValuationDivisor_mul B H f g hf hg, neg_add]
  · change -WithZero.log (hermitianGeometricInfinityValuation p s (f * g)) =
      -WithZero.log (hermitianGeometricInfinityValuation p s f) +
        -WithZero.log (hermitianGeometricInfinityValuation p s g)
    rw [map_mul, WithZero.log_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hg), neg_add]

/-- The actual principal-divisor homomorphism on nonzero rational functions. -/
def hermitianGeometricPrincipalDivisorHom :
    Additive Hˣ →+ HermitianGeometricPlaceDivisor p s where
  toFun f := hermitianGeometricZeroPoleDivisor p s ((Additive.toMul f : Hˣ) : H)
  map_zero' := hermitianGeometricZeroPoleDivisor_one p s
  map_add' f g := by
    change hermitianGeometricZeroPoleDivisor p s
      (((Additive.toMul f : Hˣ) : H) * ((Additive.toMul g : Hˣ) : H)) = _
    exact hermitianGeometricZeroPoleDivisor_mul p s _ _
      (Units.ne_zero (Additive.toMul f)) (Units.ne_zero (Additive.toMul g))

/-- Geometric affine points together with the unique infinity point, represented by `none`. -/
abbrev HermitianGeometricPoint := Option (HermitianAffinePoint p s E)

/-- Square-field Frobenius on all geometric points; infinity is fixed. -/
def hermitianGeometricPointFrobenius : HermitianGeometricPoint p s → HermitianGeometricPoint p s :=
  Option.map (hermitianFrobeniusPoint p s E)

/-- The degree-zero divisor `[P] - [infinity]`, with value zero at infinity. -/
def hermitianGeometricPointDifference : HermitianGeometricPoint p s → HermitianGeometricPlaceDivisor p s
  | none => 0
  | some P => (Finsupp.single (hermitianGeometricPointPrime p s P) 1, -1)

/-- The signed geometric divisor `D - deg(D)[infinity]`, expressed as a sum of point differences. -/
def hermitianGeometricDegreeZeroPart (D : HermitianGeometricPoint p s →₀ ℤ) :
    HermitianGeometricPlaceDivisor p s :=
  D.sum fun P n => n • hermitianGeometricPointDifference p s P

/-- Frobenius pushes forward every signed geometric divisor. -/
def hermitianGeometricFrobeniusDivisor (D : HermitianGeometricPoint p s →₀ ℤ) :
    HermitianGeometricPoint p s →₀ ℤ :=
  Finsupp.mapDomain (hermitianGeometricPointFrobenius p s) D

/-- A tangent as a unit of the function field; infinity contributes the constant one. -/
def hermitianGeometricTangentUnit : HermitianGeometricPoint p s → Hˣ
  | none => 1
  | some P => Units.mk0 (hermitianGeometricTangentFunction p s P)
      (hermitianGeometricTangentFunction_ne_zero p s P)

/-- Each tangent realizes the relation `Q(P-infinity) + (Fr(P)-infinity)`. -/
theorem hermitianGeometricTangentUnit_divisor (P : HermitianGeometricPoint p s) :
    hermitianGeometricPrincipalDivisorHom p s (Additive.ofMul (hermitianGeometricTangentUnit p s P)) =
      ((Q : ℕ) : ℤ) • hermitianGeometricPointDifference p s P +
        hermitianGeometricPointDifference p s (hermitianGeometricPointFrobenius p s P) := by
  cases P with
  | none =>
    change hermitianGeometricZeroPoleDivisor p s 1 = ((Q : ℕ) : ℤ) • 0 + 0
    rw [hermitianGeometricZeroPoleDivisor_one, smul_zero, add_zero]
  | some P =>
    change hermitianGeometricZeroPoleDivisor p s (hermitianGeometricTangentFunction p s P) = _
    rw [hermitianGeometricTangent_zeroPoleDivisor]
    apply Prod.ext
    · change Finsupp.single (hermitianGeometricPointPrime p s P) (Q : ℤ) +
          Finsupp.single (hermitianGeometricPointPrime p s (hermitianFrobeniusPoint p s E P)) 1 =
        ((Q : ℕ) : ℤ) • Finsupp.single (hermitianGeometricPointPrime p s P) 1 +
          Finsupp.single (hermitianGeometricPointPrime p s (hermitianFrobeniusPoint p s E P)) 1
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Nat.cast_pow]
    · change -((Q + 1 : ℕ) : ℤ) = ((Q : ℕ) : ℤ) • (-1 : ℤ) + (-1)
      simp only [smul_eq_mul, mul_neg_one, Nat.cast_add, Nat.cast_one, neg_add]

/-- The explicit product of all tangents to their signed divisor multiplicities. -/
def hermitianGeometricTangentProduct (D : HermitianGeometricPoint p s →₀ ℤ) : Hˣ :=
  Additive.toMul (D.sum fun P n => n • Additive.ofMul (hermitianGeometricTangentUnit p s P))

/-- Every signed divisor satisfies the actual principal relation `Q D₀ + (Fr D)₀`. -/
theorem hermitianGeometricTangentProduct_divisor (D : HermitianGeometricPoint p s →₀ ℤ) :
    hermitianGeometricZeroPoleDivisor p s (hermitianGeometricTangentProduct p s D : H) =
      ((Q : ℕ) : ℤ) • hermitianGeometricDegreeZeroPart p s D +
        hermitianGeometricDegreeZeroPart p s (hermitianGeometricFrobeniusDivisor p s D) := by
  let v := hermitianGeometricPointDifference p s
  let F := hermitianGeometricPointFrobenius p s
  let t := fun P => Additive.ofMul (hermitianGeometricTangentUnit p s P)
  let ψ := hermitianGeometricPrincipalDivisorHom p s
  change ψ (D.sum fun P n => n • t P) =
    ((Q : ℕ) : ℤ) • D.sum (fun P n => n • v P) +
      (Finsupp.mapDomain F D).sum (fun P n => n • v P)
  rw [Finsupp.sum_mapDomain_index (s := D) (f := F) (h := fun P n => n • v P)
    (fun _ => zero_smul ℤ _) (fun _ _ _ => add_smul _ _ _)]
  calc
    ψ (D.sum fun P n => n • t P) =
        D.sum (fun P n => n • (((Q : ℕ) : ℤ) • v P + v (F P))) := by
      unfold Finsupp.sum
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro P _
      rw [map_zsmul]
      exact congrArg (fun d => D P • d) (hermitianGeometricTangentUnit_divisor p s P)
    _ = _ := by
      unfold Finsupp.sum
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro P _
      simp only [smul_add, smul_smul, mul_comm]

/-- Frobenius invariance makes `(Q+1)(D-deg(D)[infinity])` the divisor of an explicit function. -/
theorem hermitianGeometricTangentProduct_divisor_of_frobenius_fixed
    (D : HermitianGeometricPoint p s →₀ ℤ) (hD : hermitianGeometricFrobeniusDivisor p s D = D) :
    hermitianGeometricZeroPoleDivisor p s (hermitianGeometricTangentProduct p s D : H) =
      ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDegreeZeroPart p s D := by
  rw [hermitianGeometricTangentProduct_divisor, hD, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

/-- Every Frobenius-invariant signed geometric divisor yields a nonzero principal witness. -/
theorem hermitianGeometricFrobeniusInvariant_exists_principal
    (D : HermitianGeometricPoint p s →₀ ℤ) (hD : hermitianGeometricFrobeniusDivisor p s D = D) :
    ∃ f : H, f ≠ 0 ∧ hermitianGeometricZeroPoleDivisor p s f =
      ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDegreeZeroPart p s D :=
  ⟨hermitianGeometricTangentProduct p s D, Units.ne_zero _,
    hermitianGeometricTangentProduct_divisor_of_frobenius_fixed p s D hD⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
