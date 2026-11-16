import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianOrigin
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianInfinity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianTranslationAction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceActions

/-!
# Tangent orders at actual rational Hermitian places

Transporting the normalized origin by rational translations constructs
a rational valuation place at every affine Hermitian point. The radical
coordinate minus its value is a uniformizer, while the tangent line has
zero order Q+1 in this actual function-field valuation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "H" => HermitianKummerField p s
local notation "u" => hermitianKummerAdditiveCoordinate p s
local notation "v" => hermitianKummerRadicalCoordinate p s
local notation "HK" => HermitianAffinePoint p s K
local notation "φ" => algebraMap K H

/-- The normalized valuation transported from the origin to a rational affine point. -/
def hermitianPointValuation (P : HK) : Valuation H (WithZero (Multiplicative ℤ)) :=
  (hermitianOriginValuation p s).comap (hermitianTranslationFieldHom p s P).toRingHom

/-- Every rational affine Hermitian point determines an actual rational valuation place. -/
def hermitianPointRationalPlace (P : HK) : RationalConstantFieldPlaces K H :=
  rationalConstantFieldPlaceEquiv (hermitianTranslationFieldAutHom p s P)
    (hermitianOriginRationalPlace p s)

/-- The transported rational place has the specified normalized valuation ring. -/
theorem hermitianPointRationalPlace_valuationSubring (P : HK) :
    (hermitianPointRationalPlace p s P).val.val =
      (hermitianPointValuation p s P).valuationSubring := rfl

/-- Nonzero constants remain units at each transported Hermitian place. -/
theorem hermitianPointValuation_constant (P : HK) (a : K) (ha : a ≠ 0) :
    hermitianPointValuation p s P (φ a) = 1 := by
  change hermitianOriginValuation p s (hermitianTranslationFieldHom p s P (φ a)) = 1
  rw [AlgHom.commutes]
  exact hermitianOriginValuation_constant p s a ha

/-- The radical coordinate minus its point value is a uniformizer. -/
theorem hermitianPointValuation_radical_sub (P : HK) :
    hermitianPointValuation p s P (v - φ P.val.1) = WithZero.exp (-1 : ℤ) := by
  change hermitianOriginValuation p s
    (hermitianTranslationFieldHom p s P (v - φ P.val.1)) = _
  rw [map_sub, hermitianTranslationFieldHom_radical, AlgHom.commutes]
  have he : φ P.val.1 + v - φ P.val.1 = v := by ring
  rw [he, hermitianOriginValuation_radical]

/-- The affine tangent line as an element of the actual Hermitian function field. -/
def hermitianTangentFunction (P : HK) : H :=
  u - φ P.val.2 - (φ P.val.1) ^ Q * (v - φ P.val.1)

/-- Translation sends the tangent at its parameter point to the additive coordinate. -/
theorem hermitianTranslationFieldHom_tangent (P : HK) :
    hermitianTranslationFieldHom p s P (hermitianTangentFunction p s P) = u := by
  rw [hermitianTangentFunction, map_sub, map_sub, map_mul, map_sub, map_pow,
    AlgHom.commutes, AlgHom.commutes,
    hermitianTranslationFieldHom_additive, hermitianTranslationFieldHom_radical]
  ring

/-- The tangent at a rational point has zero order Q+1 at its actual normalized place. -/
theorem hermitianPointValuation_tangent (P : HK) :
    hermitianPointValuation p s P (hermitianTangentFunction p s P) =
      WithZero.exp (-((Q + 1 : ℕ) : ℤ)) := by
  change hermitianOriginValuation p s
    (hermitianTranslationFieldHom p s P (hermitianTangentFunction p s P)) = _
  rw [hermitianTranslationFieldHom_tangent, hermitianOriginValuation_additive]

/-- Every rational tangent has pole order Q+1 at the actual infinity place. -/
theorem hermitianInfinityValuation_tangent (P : HK) :
    hermitianInfinityValuation p s (hermitianTangentFunction p s P) =
      WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
  let V := hermitianInfinityValuation p s
  have hc (a : K) : V (φ a) ≤ 1 :=
    (hermitianInfinityRationalPlace p s).val.property.2 a
  have hQ : (0 : ℤ) < (Q : ℕ) := by
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos (s + 1)
  have h1 : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu : V (u - φ P.val.2) = WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
    have hlt : V (φ P.val.2) < V u := by
      rw [hermitianInfinityValuation_additive]
      exact lt_of_le_of_lt (hc P.val.2) h1
    rw [V.map_sub_eq_of_lt_left hlt, hermitianInfinityValuation_additive]
  have htail : V ((φ P.val.1) ^ Q * (v - φ P.val.1)) <
      WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
    by_cases ha : P.val.1 = 0
    · simp only [ha, map_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
        zero_mul]
      exact zero_lt_iff.mpr WithZero.exp_ne_zero
    · rw [map_mul, map_pow, hermitianInfinityValuation_constant p s _ ha,
        one_pow, one_mul]
      have hlt : V (φ P.val.1) < V v := by
        rw [hermitianInfinityValuation_constant p s _ ha, hermitianInfinityValuation_radical,
          ← WithZero.exp_zero, WithZero.exp_lt_exp]
        exact hQ
      rw [V.map_sub_eq_of_lt_left hlt, hermitianInfinityValuation_radical,
        WithZero.exp_lt_exp]
      omega
  change V ((u - φ P.val.2) - (φ P.val.1) ^ Q * (v - φ P.val.1)) = _
  rw [V.map_sub_eq_of_lt_left (by rw [hu]; exact htail), hu]

/-- Distinct rational affine points give distinct actual valuation places. -/
theorem hermitianPointRationalPlace_injective :
    Function.Injective (hermitianPointRationalPlace p s) := by
  intro P U h
  let VP := hermitianPointValuation p s P
  let VU := hermitianPointValuation p s U
  have he : VP.IsEquiv VU := (Valuation.isEquiv_iff_valuationSubring VP VU).mpr
    (congrArg (fun W : RationalConstantFieldPlaces K H => W.val.val) h)
  have hrad (T : HK) : hermitianPointValuation p s T (v - φ T.val.1) < 1 := by
    rw [hermitianPointValuation_radical_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have ha : P.val.1 = U.val.1 := by
    by_contra hne
    have hsmall := VP.map_sub_lt (hrad P) (he.lt_one_iff_lt_one.mpr (hrad U))
    have hid : (v - φ P.val.1) - (v - φ U.val.1) = φ (U.val.1 - P.val.1) := by
      rw [map_sub]
      ring
    rw [hid, hermitianPointValuation_constant p s P _ (sub_ne_zero.mpr (fun he => hne he.symm))] at hsmall
    exact (lt_irrefl _ hsmall)
  have htan (T : HK) : hermitianPointValuation p s T (hermitianTangentFunction p s T) < 1 := by
    rw [hermitianPointValuation_tangent, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    have hpos : (0 : ℤ) < ((Q + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos Q
    omega
  have hb : P.val.2 = U.val.2 := by
    by_contra hne
    have hsmall := VP.map_sub_lt (htan P) (he.lt_one_iff_lt_one.mpr (htan U))
    have hid : hermitianTangentFunction p s P - hermitianTangentFunction p s U =
        φ (U.val.2 - P.val.2) := by
      simp only [hermitianTangentFunction, ha, map_sub]
      ring
    rw [hid, hermitianPointValuation_constant p s P _ (sub_ne_zero.mpr (fun he => hne he.symm))] at hsmall
    exact (lt_irrefl _ hsmall)
  exact Subtype.ext (Prod.ext ha hb)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
