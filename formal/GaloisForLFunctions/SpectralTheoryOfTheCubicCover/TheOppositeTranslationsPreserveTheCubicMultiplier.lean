import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRotatedThetaProductHasATwoCuspSubtraction

/-!
# Opposite translations preserve the cubic multiplier

The product of the multipliers at opposite integral translates equals the square
of the original multiplier. The two new denominators multiply to `a²−b²c²`;
since `3 ∣ c`, their product agrees with `a²` modulo both nine and `c`.
-/

noncomputable section
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicKubota MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicRamified MetaplecticMobiusDescent.CubicEisenstein
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- Opposite shifts cancel their ramified cubic phases. -/
theorem symbol_opposite_shifts (a b c : O) (ha : lambda ^ 2 ∣ a - 1)
    (hc : (3 : O) ∣ c) :
    symbol c (a + b * c) * symbol c (a - b * c) = symbol c a ^ 2 := by
  have hbc : lambda ^ 2 ∣ b * c :=
    dvd_mul_of_dvd_right (lambda_sq_dvd_three.trans hc) b
  have hA : lambda ^ 2 ∣ a + b * c - 1 := by
    convert dvd_add ha hbc using 1; ring
  have hB : lambda ^ 2 ∣ a - b * c - 1 := by
    convert dvd_sub ha hbc using 1; ring
  have hAB : lambda ^ 2 ∣ (a + b * c) * (a - b * c) - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left hA (a - b * c)) hB using 1; ring
  have haa : lambda ^ 2 ∣ a * a - 1 := by
    convert dvd_mul_of_dvd_left ha (a + 1) using 1; ring
  have h9 : (9 : O) ∣ (a + b * c) * (a - b * c) - a * a := by
    obtain ⟨k, hk⟩ := hc
    refine ⟨-(b * k) ^ 2, ?_⟩
    rw [hk]
    ring
  have hcc : c ∣ (a + b * c) * (a - b * c) - a * a :=
    ⟨-(b ^ 2 * c), by ring⟩
  calc
    _ = symbol c ((a + b * c) * (a - b * c)) :=
      (symbol_mul_denominator _ _ _).symm
    _ = symbol c (a * a) := symbol_denominator_congr c _ _ hAB haa h9 hcc
    _ = symbol c a ^ 2 := by rw [symbol_mul_denominator, pow_two]

theorem complexCharacter_opposite_shifts (b : O) (n : levelThree) :
    complexCharacter (levelThreeConjugate (integralTranslation b) n) *
      complexCharacter (levelThreeConjugate (integralTranslation (-b)) n) =
        complexCharacter n ^ 2 := by
  have hshift (t : O) :
      value (levelThreeConjugate (integralTranslation t) n) =
        symbol ((n : SL(2, O)) 1 0)
          ((n : SL(2, O)) 0 0 + t * (n : SL(2, O)) 1 0) := by
    simp only [value, levelThreeConjugate, integralTranslation,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
  change ringComplex (value _) * ringComplex (value _) = ringComplex (value n) ^ 2
  rw [← map_mul, ← map_pow]
  apply congrArg ringComplex
  rw [hshift, hshift]
  simpa only [value, neg_mul, ← sub_eq_add_neg] using
    symbol_opposite_shifts ((n : SL(2, O)) 0 0) b ((n : SL(2, O)) 1 0)
      (levelThree_primary n) (levelThree_lower n)

/-- The product of opposite translates has the inverse cubic multiplier. -/
theorem sourceTheta_opposite_shifts_automorphy (b : O) (n : levelThree)
    (w : HyperbolicSpace) :
    sourceTheta (integralComplexMatrix (integralTranslation b) • (complexMatrix n • w)) *
      sourceTheta (integralComplexMatrix (integralTranslation (-b)) • (complexMatrix n • w)) =
        (complexCharacter n)⁻¹ *
          (sourceTheta (integralComplexMatrix (integralTranslation b) • w) *
            sourceTheta (integralComplexMatrix (integralTranslation (-b)) • w)) := by
  rw [conj_smul, conj_smul, sourceTheta_automorphy, sourceTheta_automorphy,
    ← complexCharacter_sq_eq_inv, ← complexCharacter_opposite_shifts b n]
  ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
