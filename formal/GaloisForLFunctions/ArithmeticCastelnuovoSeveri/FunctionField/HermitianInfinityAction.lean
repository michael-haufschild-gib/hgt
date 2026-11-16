import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianInfinity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianTranslationAction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceActions

/-!
# Hermitian translations fix the actual infinity place

The radical is integral at every finite normalization place and has a
pole at infinity. Translation adds only a constant to the radical, so
the transported infinity place still has that pole. The exhaustive place
classification identifies it with the same unique infinity place.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.HTGeometry IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "H" => HermitianKummerField p s
local notation "B" => SquareKummerNormalization p s η⁻¹ (Q - 2) 1
local notation "v" => hermitianKummerRadicalCoordinate p s
local notation "HK" => HermitianAffinePoint p s K

/-- The radical coordinate is integral at every finite Hermitian normalization place. -/
theorem hermitianFinitePlace_radical_mem (w : HeightOneSpectrum B) :
    v ∈ (squareKummerFiniteConstantPlace p s η⁻¹ s 1 w).val := by
  exact algebraMap_mem_valuationSubringAtPlace H w
    ⟨v, kummerBranchField_root_integral η⁻¹ (Q - 2) 1 Q⟩

/-- The radical coordinate is not integral at the Hermitian infinity place. -/
theorem hermitianInfinity_radical_notMem :
    v ∉ (hermitianInfinityValuation p s).valuationSubring := by
  intro h
  change hermitianInfinityValuation p s v ≤ 1 at h
  rw [hermitianInfinityValuation_radical, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  have hQ : 0 < Q := pow_pos (Fact.out : p.Prime).pos _
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  omega

/-- Every rational Hermitian translation fixes the actual rational infinity place. -/
theorem hermitianTranslation_fixes_infinity (P : HK) :
    rationalConstantFieldPlaceEquiv (hermitianTranslationFieldAutHom p s P)
      (hermitianInfinityRationalPlace p s) = hermitianInfinityRationalPlace p s := by
  apply Subtype.ext
  let W := constantFieldPlaceEquiv (hermitianTranslationFieldAutHom p s P)
    (squareKummerInfinityConstantPlace p s η⁻¹ s 1)
  change W = squareKummerInfinityConstantPlace p s η⁻¹ s 1
  have hnot : v ∉ W.val := by
    change hermitianTranslationFieldHom p s P v ∉
      (hermitianInfinityValuation p s).valuationSubring
    rw [hermitianTranslationFieldHom_radical]
    intro h
    have ha : algebraMap K H P.val.1 ∈ (hermitianInfinityValuation p s).valuationSubring :=
      (squareKummerInfinityConstantPlace p s η⁻¹ s 1).property.2 P.val.1
    have hv := (hermitianInfinityValuation p s).valuationSubring.sub_mem h ha
    have he : algebraMap K H P.val.1 + v - algebraMap K H P.val.1 = v := by ring
    rw [he] at hv
    exact hermitianInfinity_radical_notMem p s hv
  rcases squareKummer_constantPlace_cases p s η⁻¹ s 1 W with ⟨w, hw⟩ | hw
  · exfalso
    apply hnot
    rw [← hw]
    exact hermitianFinitePlace_radical_mem p s w
  · exact hw.symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
