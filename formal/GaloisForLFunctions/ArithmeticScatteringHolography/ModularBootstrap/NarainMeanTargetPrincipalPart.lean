import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanTargetDecomposition
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Fixed-product arithmetic principal parts

All negative Laurent coefficients are inherited from the universal dilated mean, so fixed-product target families have identical full arithmetic principal parts.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Every arithmetic principal coefficient is inherited from the dilated unit-height mean. -/
theorem laurentCoeff_narainMellinMean_eq_universal (Y Z : Height) (p : Resonance)
    {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (narainMellinMean Y Z) p.val ℓ =
      laurentCoeff (fun u => narainMeanTargetDilation Y Z u *
        narainMellinMean ⟨1, by norm_num [Height]⟩ ⟨1, by norm_num [Height]⟩ u) p.val ℓ := by
  have hM := meromorphic_narainMellinMean Y Z p.val
  have hU := meromorphic_narainMellinMean
    ⟨1, by norm_num [Height]⟩ ⟨1, by norm_num [Height]⟩ p.val
  have hD := (differentiable_narainMeanTargetDilation Y Z).analyticAt p.val
  have hC := analyticAt_narainMeanTargetCorrection_resonance Y Z p
  rw [laurentCoeff_congr hM (narainMellinMean_target_decomposition_germ Y Z p) ℓ,
    laurentCoeff_add (hD.meromorphicAt.mul hU) hC.meromorphicAt,
    laurentCoeff_eq_zero_of_analyticAt hC hℓ, add_zero]

/-- Fixed-product target families have identical full arithmetic principal parts, including multiple poles. -/
theorem laurentCoeff_narainMellinMean_eq_of_target_product
    (Y Z Y' Z' : Height) (p : Resonance) (hprod : Y.val * Z.val = Y'.val * Z'.val)
    {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (narainMellinMean Y Z) p.val ℓ =
      laurentCoeff (narainMellinMean Y' Z') p.val ℓ := by
  rw [laurentCoeff_narainMellinMean_eq_universal Y Z p hℓ,
    laurentCoeff_narainMellinMean_eq_universal Y' Z' p hℓ]
  have hd : narainMeanTargetDilation Y Z = narainMeanTargetDilation Y' Z' := by
    funext u
    rw [narainMeanTargetDilation_eq_product, narainMeanTargetDilation_eq_product, hprod]
  rw [hd]

#print axioms laurentCoeff_narainMellinMean_eq_universal
#print axioms laurentCoeff_narainMellinMean_eq_of_target_product
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
