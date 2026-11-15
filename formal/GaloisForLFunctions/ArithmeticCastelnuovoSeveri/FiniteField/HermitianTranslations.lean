import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentFactor
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants

/-!
# Rational translations of the Hermitian equation

Each rational point `(a,b)` acts on every constant-field extension by
`(x,y) ↦ (a+x,b+y+a^Q*x)`. Square Frobenius fixes the translation
coefficients, so this preserves the actual Hermitian equation. The
inverse parameter is `(-a,b^Q)`; composition gives the Hermitian parameter law.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
variable (E : Type*) [Field E] [Algebra K E]
local notation "H" => HermitianAffinePoint p s E
local notation "HK" => HermitianAffinePoint p s K
local notation "φ" => algebraMap K E

local instance hermitianTranslationCharP : CharP E p :=
  charP_of_injective_algebraMap (algebraMap K E).injective p

private theorem hermitianTranslation_frobenius_add (x y : E) :
    (x + y) ^ Q = x ^ Q + y ^ Q := by
  change iterateFrobenius E p (s + 1) (x + y) =
    iterateFrobenius E p (s + 1) x + iterateFrobenius E p (s + 1) y
  exact map_add _ _ _

private theorem hermitianTranslation_frobenius_neg (x : E) :
    (-x) ^ Q = -(x ^ Q) := by
  change iterateFrobenius E p (s + 1) (-x) =
    -(iterateFrobenius E p (s + 1) x)
  exact map_neg _ _

private theorem hermitianTranslation_constant_frobenius (a : K) :
    ((φ a) ^ Q) ^ Q = φ a := by
  rw [← map_pow, ← map_pow, squareConstantField_frobenius_sq]

/-- A rational Hermitian point remains a point over every extension of its constants. -/
def hermitianAffinePointExtend (P : HK) : H :=
  ⟨(φ P.val.1, φ P.val.2), by
    simpa only [map_add, map_pow] using congrArg φ P.property⟩

/-- Rational Hermitian points translate every actual affine solution over extended constants. -/
def hermitianAffineTranslate (P : HK) (T : H) : H := by
  let a := φ P.val.1
  let b := φ P.val.2
  let x := T.val.1
  let y := T.val.2
  refine ⟨(a + x, b + y + a ^ Q * x), ?_⟩
  have hP : b ^ Q + b = a ^ (Q + 1) := (hermitianAffinePointExtend p s E P).property
  have hT : y ^ Q + y = x ^ (Q + 1) := T.property
  have ha : (a ^ Q) ^ Q = a := hermitianTranslation_constant_frobenius p s E P.val.1
  change (b + y + a ^ Q * x) ^ Q + (b + y + a ^ Q * x) = (a + x) ^ (Q + 1)
  simp only [hermitianTranslation_frobenius_add p s E, mul_pow, ha]
  calc
    _ = (b ^ Q + b) + (y ^ Q + y) + a * x ^ Q + a ^ Q * x := by ring
    _ = a ^ (Q + 1) + x ^ (Q + 1) + a * x ^ Q + a ^ Q * x := by rw [hP, hT]
    _ = _ := by
      rw [pow_succ (a + x) Q, hermitianTranslation_frobenius_add p s E,
        pow_succ a Q, pow_succ x Q]
      ring

/-- The inverse translation parameter is the actual rational point `(-a,b^Q)`. -/
def hermitianTranslationInverse (P : HK) : HK := by
  refine ⟨(-P.val.1, P.val.2 ^ Q), ?_⟩
  change (P.val.2 ^ Q) ^ Q + P.val.2 ^ Q = (-P.val.1) ^ (Q + 1)
  rw [squareConstantField_frobenius_sq, pow_succ (-P.val.1) Q,
    hermitianTranslation_frobenius_neg p s K]
  calc
    P.val.2 + P.val.2 ^ Q = P.val.2 ^ Q + P.val.2 := add_comm _ _
    _ = P.val.1 ^ (Q + 1) := P.property
    _ = _ := by rw [pow_succ P.val.1 Q]; ring

/-- Inverting a rational translation parameter twice returns the same point. -/
theorem hermitianTranslationInverse_inverse (P : HK) :
    hermitianTranslationInverse p s (hermitianTranslationInverse p s P) = P := by
  apply Subtype.ext
  apply Prod.ext
  · change -(-P.val.1) = P.val.1
    exact neg_neg _
  · exact squareConstantField_frobenius_sq p s P.val.2

/-- Translation by the inverse parameter undoes translation on every extended point. -/
theorem hermitianAffineTranslate_inverse_left (P : HK) (T : H) :
    hermitianAffineTranslate p s E (hermitianTranslationInverse p s P)
      (hermitianAffineTranslate p s E P T) = T := by
  apply Subtype.ext
  apply Prod.ext
  · change φ (-P.val.1) + (φ P.val.1 + T.val.1) = T.val.1
    rw [map_neg]
    ring
  · change φ (P.val.2 ^ Q) + (φ P.val.2 + T.val.2 + (φ P.val.1) ^ Q * T.val.1) +
      (φ (-P.val.1)) ^ Q * (φ P.val.1 + T.val.1) = T.val.2
    rw [map_pow, map_neg, hermitianTranslation_frobenius_neg p s E]
    have hP : (φ P.val.2) ^ Q + φ P.val.2 = (φ P.val.1) ^ (Q + 1) :=
      (hermitianAffinePointExtend p s E P).property
    calc
      _ = ((φ P.val.2) ^ Q + φ P.val.2) -
          (φ P.val.1) ^ Q * φ P.val.1 + T.val.2 := by ring
      _ = T.val.2 := by rw [hP, pow_succ (φ P.val.1) Q]; ring

/-- Translation also undoes the inverse translation on every extended point. -/
theorem hermitianAffineTranslate_inverse_right (P : HK) (T : H) :
    hermitianAffineTranslate p s E P
      (hermitianAffineTranslate p s E (hermitianTranslationInverse p s P) T) = T := by
  have h := hermitianAffineTranslate_inverse_left p s E (hermitianTranslationInverse p s P) T
  rwa [hermitianTranslationInverse_inverse] at h

/-- Every rational Hermitian translation is an explicit permutation over every constant extension. -/
def hermitianAffineTranslationEquiv (P : HK) : H ≃ H where
  toFun := hermitianAffineTranslate p s E P
  invFun := hermitianAffineTranslate p s E (hermitianTranslationInverse p s P)
  left_inv := hermitianAffineTranslate_inverse_left p s E P
  right_inv := hermitianAffineTranslate_inverse_right p s E P

/-- The parameter product is `(a+c,b+d+a^Q*c)`. -/
def hermitianTranslationProduct (P T : HK) : HK := hermitianAffineTranslate p s K P T

/-- Composition of the actual translations obeys the Hermitian parameter law. -/
theorem hermitianAffineTranslate_comp (P U : HK) (T : H) :
    hermitianAffineTranslate p s E P (hermitianAffineTranslate p s E U T) =
      hermitianAffineTranslate p s E (hermitianTranslationProduct p s P U) T := by
  apply Subtype.ext
  apply Prod.ext
  · change φ P.val.1 + (φ U.val.1 + T.val.1) = φ (P.val.1 + U.val.1) + T.val.1
    rw [map_add]
    ring
  · change φ P.val.2 + (φ U.val.2 + T.val.2 + (φ U.val.1) ^ Q * T.val.1) +
      (φ P.val.1) ^ Q * (φ U.val.1 + T.val.1) =
      φ (P.val.2 + U.val.2 + P.val.1 ^ Q * U.val.1) + T.val.2 +
        (φ (P.val.1 + U.val.1)) ^ Q * T.val.1
    simp only [map_add, map_mul, map_pow, hermitianTranslation_frobenius_add p s E]
    ring

/-- The origin is an actual Hermitian point over every constant extension. -/
def hermitianAffineOrigin : H :=
  ⟨(0, 0), by
    simp only [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
      zero_pow (Nat.succ_ne_zero Q), add_zero]⟩

/-- A rational translation sends the origin to its parameter point. -/
theorem hermitianAffineTranslate_origin (P : HK) :
    hermitianAffineTranslate p s E P (hermitianAffineOrigin p s E) =
      hermitianAffinePointExtend p s E P := by
  apply Subtype.ext
  change (φ P.val.1 + 0, φ P.val.2 + 0 + (φ P.val.1) ^ Q * 0) =
    (φ P.val.1, φ P.val.2)
  simp only [add_zero, mul_zero]

/-- The origin parameter acts as the identity on every extended Hermitian point. -/
theorem hermitianAffineTranslate_zero (T : H) :
    hermitianAffineTranslate p s E (hermitianAffineOrigin p s K) T = T := by
  apply Subtype.ext
  change (φ 0 + T.val.1, φ 0 + T.val.2 + (φ 0) ^ Q * T.val.1) = (T.val.1, T.val.2)
  simp only [map_zero, zero_add, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    zero_mul, add_zero]

/-- Exactly one rational translation carries any rational affine Hermitian point to any other. -/
theorem hermitianAffineTranslate_existsUnique (P T : HK) :
    ∃! U : HK, hermitianAffineTranslate p s K U P = T := by
  let U := hermitianTranslationProduct p s T (hermitianTranslationInverse p s P)
  have hcenter : hermitianAffineTranslate p s K (hermitianTranslationInverse p s P) P =
      hermitianAffineOrigin p s K := by
    have h := hermitianAffineTranslate_inverse_left p s K P (hermitianAffineOrigin p s K)
    rw [hermitianAffineTranslate_origin] at h
    exact h
  have hU : hermitianAffineTranslate p s K U P = T := by
    calc
      _ = hermitianAffineTranslate p s K T
          (hermitianAffineTranslate p s K (hermitianTranslationInverse p s P) P) :=
        (hermitianAffineTranslate_comp p s K T (hermitianTranslationInverse p s P) P).symm
      _ = hermitianAffineTranslate p s K T (hermitianAffineOrigin p s K) :=
        congrArg (hermitianAffineTranslate p s K T) hcenter
      _ = T := hermitianAffineTranslate_origin p s K T
  refine ⟨U, hU, ?_⟩
  intro V hV
  have h := hV.trans hU.symm
  have hx := congrArg (fun A : HK => A.val.1) h
  change V.val.1 + P.val.1 = U.val.1 + P.val.1 at hx
  have hx' : V.val.1 = U.val.1 := add_right_cancel hx
  have hy := congrArg (fun A : HK => A.val.2) h
  change V.val.2 + P.val.2 + V.val.1 ^ Q * P.val.1 =
    U.val.2 + P.val.2 + U.val.1 ^ Q * P.val.1 at hy
  rw [hx'] at hy
  exact Subtype.ext (Prod.ext hx' (add_right_cancel (add_right_cancel hy)))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
