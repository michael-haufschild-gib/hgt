import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspQuotient
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Normalization of the concrete cubic observation cusp

The missing middle gap is integral, and the exact coefficient decomposition
makes the full two-variable polynomial algebra integral over the cusp algebra.
It is integrally closed. Clearing denominators by the square of the middle gap
proves equality of fraction fields. The full polynomial algebra is therefore
the integral closure in that common fraction field.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


theorem cubicCuspMiddle_isIntegral :
    IsIntegral cubicCuspAlgebra (Polynomial.X : Polynomial (Polynomial ℝ)) := by
  apply IsIntegral.of_pow (n := 2) (by positivity)
  exact isIntegral_algebraMap (x := (⟨Polynomial.X^(2 : ℕ),cubicCuspAlgebra_square⟩ : cubicCuspAlgebra))

theorem cubicCuspNormalization_isIntegral (P : Polynomial (Polynomial ℝ)) :
    IsIntegral cubicCuspAlgebra P := by
  have ha : IsIntegral cubicCuspAlgebra (cubicCuspRemainder P) :=
    isIntegral_algebraMap (x := (⟨_,cubicCuspRemainder_mem P⟩ : cubicCuspAlgebra))
  have hb : IsIntegral cubicCuspAlgebra (Polynomial.C (P.coeff 1)) :=
    isIntegral_algebraMap (x := (⟨_,cubicCuspAlgebra_constant _⟩ : cubicCuspAlgebra))
  rw [cubicCuspRemainder_decomposition P]
  exact ha.add (hb.mul cubicCuspMiddle_isIntegral)

theorem cubicCuspNormalization_normal : IsIntegrallyClosed (Polynomial (Polynomial ℝ)) :=
  inferInstance

theorem cubicCuspNormalization_integralClosure :
    IsIntegralClosure (Polynomial (Polynomial ℝ)) cubicCuspAlgebra
      (FractionRing (Polynomial (Polynomial ℝ))) := by
  refine ⟨IsFractionRing.injective _ _,?_⟩
  intro z
  constructor
  · intro hz
    exact IsIntegrallyClosed.isIntegral_iff.mp (hz.tower_top (A := Polynomial (Polynomial ℝ)))
  · rintro ⟨P,rfl⟩
    exact IsIntegral.map (A := cubicCuspAlgebra)
      (IsScalarTower.toAlgHom cubicCuspAlgebra (Polynomial (Polynomial ℝ))
        (FractionRing (Polynomial (Polynomial ℝ)))) (cubicCuspNormalization_isIntegral P)

theorem cubicCuspAlgebra_clearDenominator (P : Polynomial (Polynomial ℝ)) :
    P*Polynomial.X^(2 : ℕ) ∈ cubicCuspAlgebra := by
  rw [cubicCuspAlgebra_mem,Polynomial.coeff_mul_X_pow']
  simp

set_option maxHeartbeats 800000 in
theorem cubicCuspNormalization_commonFractionField :
    IsFractionRing cubicCuspAlgebra (FractionRing (Polynomial (Polynomial ℝ))) := by
  apply IsFractionRing.of_field (R := cubicCuspAlgebra)
  intro z
  obtain ⟨P,Q,_,rfl⟩ := IsFractionRing.div_surjective (Polynomial (Polynomial ℝ)) z
  refine ⟨⟨P*Polynomial.X^(2 : ℕ),cubicCuspAlgebra_clearDenominator P⟩,
    ⟨Q*Polynomial.X^(2 : ℕ),cubicCuspAlgebra_clearDenominator Q⟩,?_⟩
  change algebraMap (Polynomial (Polynomial ℝ)) _ P / algebraMap (Polynomial (Polynomial ℝ)) _ Q=
    algebraMap (Polynomial (Polynomial ℝ)) _ (P*Polynomial.X^(2 : ℕ)) /
      algebraMap (Polynomial (Polynomial ℝ)) _ (Q*Polynomial.X^(2 : ℕ))
  have hX : algebraMap (Polynomial (Polynomial ℝ)) (FractionRing (Polynomial (Polynomial ℝ)))
      (Polynomial.X^(2 : ℕ)) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    exact pow_ne_zero _ Polynomial.X_ne_zero
  rw [map_mul,map_mul,mul_div_mul_right _ _ hX]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
