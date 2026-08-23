import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSumQuotient

/-!
# Hasse classification of finite-support invariant profiles

For number-field and rational-function-field place types, two finite-support `ℚ/ℤ` profiles have the
same invariant sum exactly when their difference is zero-sum.  Every invariant value has a profile
representative unique modulo the zero-sum subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Number-field profiles are congruent modulo zero-sum profiles exactly when their invariant sums
agree. -/
theorem numberFieldFinsuppRatModIntSum_congr_hasse_iff
    (K : Type u) [Field K] [NumberField K]
    (x y : NumberFieldPlace K →₀ RatModInt) :
    x - y ∈ (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker ↔
      finsuppRatModIntSumAddHom (NumberFieldPlace K) x =
        finsuppRatModIntSumAddHom (NumberFieldPlace K) y := by
  change finsuppRatModIntSumAddHom (NumberFieldPlace K) (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every number-field invariant value has a finite-support profile representative, unique modulo
zero-sum profiles. -/
theorem numberFieldFinsuppRatModIntSum_exists_unique_mod_zeroSum
    (K : Type u) [Field K] [NumberField K] (z : RatModInt) :
    ∃ x : NumberFieldPlace K →₀ RatModInt,
      finsuppRatModIntSumAddHom (NumberFieldPlace K) x = z ∧
      ∀ y : NumberFieldPlace K →₀ RatModInt,
        finsuppRatModIntSumAddHom (NumberFieldPlace K) y = z ↔
          y - x ∈ (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker := by
  obtain ⟨x, hx⟩ := numberFieldFinsuppRatModIntSum_surjective K z
  refine ⟨x, hx, fun y => ?_⟩
  rw [← hx]
  exact (numberFieldFinsuppRatModIntSum_congr_hasse_iff K y x).symm

/-- Rational-function profiles are congruent modulo zero-sum profiles exactly when their invariant
sums agree. -/
theorem rationalFunctionFinsuppRatModIntSum_congr_hasse_iff
    (F : Type u) [Field F] [Finite F]
    (x y : RationalFunctionPlace F →₀ RatModInt) :
    x - y ∈ (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker ↔
      finsuppRatModIntSumAddHom (RationalFunctionPlace F) x =
        finsuppRatModIntSumAddHom (RationalFunctionPlace F) y := by
  change finsuppRatModIntSumAddHom (RationalFunctionPlace F) (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every rational-function invariant value has a finite-support profile representative, unique
modulo zero-sum profiles. -/
theorem rationalFunctionFinsuppRatModIntSum_exists_unique_mod_zeroSum
    (F : Type u) [Field F] [Finite F] (z : RatModInt) :
    ∃ x : RationalFunctionPlace F →₀ RatModInt,
      finsuppRatModIntSumAddHom (RationalFunctionPlace F) x = z ∧
      ∀ y : RationalFunctionPlace F →₀ RatModInt,
        finsuppRatModIntSumAddHom (RationalFunctionPlace F) y = z ↔
          y - x ∈ (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker := by
  obtain ⟨x, hx⟩ := rationalFunctionFinsuppRatModIntSum_surjective F z
  refine ⟨x, hx, fun y => ?_⟩
  rw [← hx]
  exact (rationalFunctionFinsuppRatModIntSum_congr_hasse_iff F y x).symm

end GaloisForLFunctions.HTGeometry.ABHN
