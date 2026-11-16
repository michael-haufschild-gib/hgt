import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerMaximalCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPolynomialPrimePoints

/-!
# Rational algebra points of the maximal Kummer normalization

Constant-valued algebra maps correspond to the explicitly classified
rational primes. Removing the unique rational infinity place from the
maximal proper-place count gives `Q²+2Qg` affine evaluation points.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "A" => NormalizedKummerNormalization p (kummerSquareIndex d n) d r
local notation "Q" => p ^ (kummerSquareIndex d n + 1)
local notation "g" => Module.finrank K (NormalizedKummerRegularDifferentials p d n r)

/-- Actual constant-valued points of the affine normalization. -/
abbrev NormalizedKummerAlgebraPoints := A →ₐ[K] K

/-- The algebra points are exactly the explicitly counted finite rational primes. -/
def normalizedKummerAlgebraPointEquiv :
    NormalizedKummerAlgebraPoints p d n r ≃
      {P // P ∈ normalizedKummerRationalPrimes p d n r} :=
  (rationalPolynomialPointEquiv K A).trans
    { toFun := fun P => ⟨P.val,
        (mem_normalizedKummerRationalPrimes_iff p d n r P.val).mpr P.property⟩
      invFun := fun P => ⟨P.val,
        (mem_normalizedKummerRationalPrimes_iff p d n r P.val).mp P.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The affine normalization has finitely many rational algebra points. -/
instance normalizedKummerAlgebraPoints_finite : Finite (NormalizedKummerAlgebraPoints p d n r) :=
  Finite.of_equiv {P // P ∈ normalizedKummerRationalPrimes p d n r}
    (normalizedKummerAlgebraPointEquiv p d n r).symm

/-- The actual affine evaluation set has the maximal-curve length `Q²+2Qg`. -/
theorem normalizedKummerAlgebraPoints_card :
    Nat.card (NormalizedKummerAlgebraPoints p d n r) = Q ^ 2 + 2 * Q * g := by
  have h := normalizedKummerRationalPlaces_card_maximal p d n r
  rw [← Nat.card_congr (normalizedKummerRationalPlaceEquiv p d n r),
    Nat.card_sum] at h
  have hunit : Nat.card PUnit.{1} = 1 := Nat.card_unique
  rw [hunit] at h
  rw [Nat.card_congr (normalizedKummerAlgebraPointEquiv p d n r)]
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
