import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicNormSelector
import AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin

/-!
# Actual dyadic local Artin kernel for the SST quaternion field

The completed Hensel witness is promoted to a unit of the genuine finite-place
tensor algebra.  Finite local class field theory then identifies its determinant
norm with the kernel of the actual local Artin map.  Thus the literal SST unit
`u` has trivial Artin symbol at every contracted dyadic place of the
biquadratic layer.
-/

namespace RHTower

noncomputable section

open scoped NumberField TensorProduct
open GlobalClassFieldTheory.Reciprocity

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance deningerQ8ActualTwoAdicLocalArtinLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance deningerQ8ActualTwoAdicLocalArtinLocalInst2 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst3 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst4 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst5 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst6 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst7 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst8 : NumberField K2 := NumberField.mk
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst9 : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst10 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst11 : IsGalois K2 K3 :=
  IsGalois.tower_top_of_isGalois ℚ K2 K3
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst12 : IsCyclic Gal(K3/K2) := by
  apply isCyclic_of_prime_card (p := 2)
  rw [IsGalois.card_aut_eq_finrank,
    deningerQ8RootNumberNegOneTopField_finrank_over_second]
noncomputable local instance deningerQ8ActualTwoAdicLocalArtinLocalInst13 : IsAbelianGalois K2 K3 :=
  IsAbelianGalois.of_isCyclic K2 K3

/-- The literal completed dyadic unit is in the actual finite-place tensor-norm
kernel for `K3 / K2`. -/
theorem q8BiquadTwoAdicU_finitePlaceTensorNormClass_eq_one
    (place : NumberField.FinitePlace K2)
    (hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal) :
    finitePlaceTensorNormClass (K := K2) (L := K3)
        place.maximalIdeal (q8BiquadTwoAdicUCompletionUnit place) = 1 := by
  rw [finitePlaceTensorNormClass_eq_one_iff]
  exact exists_q8BiquadTwoAdicU_completedTopScalarExtensionUnitNorm place hplace

/-- Genuine local reciprocity: the selected dyadic unit has trivial Artin
symbol in the actual quadratic extension `K3 / K2`. -/
theorem q8BiquadTwoAdicU_chosenFinitePlaceArtin_eq_one
    (place : NumberField.FinitePlace K2)
    (hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal) :
    chosenFinitePlaceArtinMonoidHom (K := K2) (L := K3)
        place.maximalIdeal (q8BiquadTwoAdicUCompletionUnit place) = 1 := by
  have hclass := q8BiquadTwoAdicU_finitePlaceTensorNormClass_eq_one place hplace
  have hmem : q8BiquadTwoAdicUCompletionUnit place ∈
      chosenFinitePlaceLocalNormSubgroup (K := K2) (L := K3)
        place.maximalIdeal := by
    exact (QuotientGroup.eq_one_iff
      (N := chosenFinitePlaceLocalNormSubgroup (K := K2) (L := K3)
        place.maximalIdeal)
      (q8BiquadTwoAdicUCompletionUnit place)).mp hclass
  rw [← chosenFinitePlaceArtinMonoidHom_ker] at hmem
  exact hmem

end
end RHTower
