import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairAlgebra
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspNormalization

/-!
# The same normalization and fraction field for every observation repair

Every intermediate repair algebra has the full two-variable polynomial algebra
as its integral closure in the common fraction field. Multiplication by the
square of the missing gap clears denominators uniformly for all repair ideals.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

theorem cubicRepairMiddle_isIntegral (I : Ideal (Polynomial ℝ)) :
    IsIntegral (cubicRepairAlgebra I) (Polynomial.X : Polynomial (Polynomial ℝ)) := by
  apply IsIntegral.of_pow (n := 2) (by positivity)
  exact isIntegral_algebraMap (x := (⟨Polynomial.X^2,
    cubicRepairAlgebra_contains I cubicCuspAlgebra_square⟩ : cubicRepairAlgebra I))

theorem cubicRepairNormalization_isIntegral (I : Ideal (Polynomial ℝ)) (P : Polynomial (Polynomial ℝ)) :
    IsIntegral (cubicRepairAlgebra I) P := by
  have ha : IsIntegral (cubicRepairAlgebra I) (cubicCuspRemainder P) :=
    isIntegral_algebraMap (x := (⟨_,cubicRepairAlgebra_contains I (cubicCuspRemainder_mem P)⟩ : cubicRepairAlgebra I))
  have hb : IsIntegral (cubicRepairAlgebra I) (Polynomial.C (P.coeff 1)) :=
    isIntegral_algebraMap (x := (⟨_,cubicRepairAlgebra_contains I (cubicCuspAlgebra_constant _)⟩ : cubicRepairAlgebra I))
  rw [cubicCuspRemainder_decomposition P]
  exact ha.add (hb.mul (cubicRepairMiddle_isIntegral I))

theorem cubicRepairNormalization_integralClosure (I : Ideal (Polynomial ℝ)) :
    IsIntegralClosure (Polynomial (Polynomial ℝ)) (cubicRepairAlgebra I)
      (FractionRing (Polynomial (Polynomial ℝ))) := by
  refine ⟨IsFractionRing.injective _ _,?_⟩
  intro z
  constructor
  · intro hz
    exact IsIntegrallyClosed.isIntegral_iff.mp (hz.tower_top (A := Polynomial (Polynomial ℝ)))
  · rintro ⟨P,rfl⟩
    exact IsIntegral.map (A := cubicRepairAlgebra I)
      (IsScalarTower.toAlgHom (cubicRepairAlgebra I) (Polynomial (Polynomial ℝ))
        (FractionRing (Polynomial (Polynomial ℝ)))) (cubicRepairNormalization_isIntegral I P)

set_option maxHeartbeats 800000 in
theorem cubicRepairNormalization_commonFractionField (I : Ideal (Polynomial ℝ)) :
    IsFractionRing (cubicRepairAlgebra I) (FractionRing (Polynomial (Polynomial ℝ))) := by
  apply IsFractionRing.of_field (R := cubicRepairAlgebra I)
  intro z
  obtain ⟨P,Q,_,rfl⟩ := IsFractionRing.div_surjective (Polynomial (Polynomial ℝ)) z
  refine ⟨⟨P*Polynomial.X^2,cubicRepairAlgebra_contains I (cubicCuspAlgebra_clearDenominator P)⟩,
    ⟨Q*Polynomial.X^2,cubicRepairAlgebra_contains I (cubicCuspAlgebra_clearDenominator Q)⟩,?_⟩
  change algebraMap (Polynomial (Polynomial ℝ)) _ P / algebraMap (Polynomial (Polynomial ℝ)) _ Q=
    algebraMap (Polynomial (Polynomial ℝ)) _ (P*Polynomial.X^2) /
      algebraMap (Polynomial (Polynomial ℝ)) _ (Q*Polynomial.X^2)
  have hX : algebraMap (Polynomial (Polynomial ℝ)) (FractionRing (Polynomial (Polynomial ℝ)))
      (Polynomial.X^2) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    exact pow_ne_zero _ Polynomial.X_ne_zero
  rw [map_mul,map_mul,mul_div_mul_right _ _ hX]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
