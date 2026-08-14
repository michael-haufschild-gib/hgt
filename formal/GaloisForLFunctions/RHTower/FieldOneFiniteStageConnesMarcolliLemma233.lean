import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliFourierCovariance
import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatDenseRange
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Connes--Marcolli Lemma 2.33

The algebraic finite-stage Fourier transform is extended uniquely through the
dense half-density image to a unitary operator on the canonical split
idele-class L² space.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open Function IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators ComplexConjugate TensorProduct FourierTransform

def fieldOneFiniteStageBruhatFourierLinearEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageBruhatSchwartz S ≃ₗ[ℂ]
      FieldOneFiniteStageBruhatSchwartz S :=
  TensorProduct.congr
    (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).symm.toLinearEquiv
    (fieldOneFiniteStageFiniteBruhatFourierLinearEquiv S)

@[simp] theorem fieldOneFiniteStageBruhatFourierLinearEquiv_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierLinearEquiv S (f ⊗ₜ[ℂ] phi) =
      (𝓕⁻ f) ⊗ₜ[ℂ]
        fieldOneFiniteStageFiniteBruhatFourierBruhat S phi := by
  rfl

theorem fieldOneFiniteStageBruhatFourierLinearEquiv_eq
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierLinearEquiv S x = fieldOneFiniteStageBruhatFourierEndomorphism S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f phi => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem fieldOneFiniteStageBruhatSourceInner_eq_halfDensity_inner
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSourceInner S x y =
      inner ℂ (fieldOneFiniteStageBruhatHalfDensityLinearMap S x)
        (fieldOneFiniteStageBruhatHalfDensityLinearMap S y) := by
  rw [fieldOneFiniteStageBruhatSourceInner]
  change (∫ z,
      star (fieldOneFiniteStageBruhatSplitHalfDensity S x z) *
        fieldOneFiniteStageBruhatSplitHalfDensity S y z
      ∂fieldOneFiniteStageSplitProductHaarMeasure S) =
    ∫ z, inner ℂ (fieldOneFiniteStageBruhatHalfDensityL2 S x z)
      (fieldOneFiniteStageBruhatHalfDensityL2 S y z)
      ∂fieldOneFiniteStageSplitProductHaarMeasure S
  apply integral_congr_ae
  filter_upwards [fieldOneFiniteStageBruhatHalfDensityL2_ae S x,
    fieldOneFiniteStageBruhatHalfDensityL2_ae S y] with z hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply']
  change conj (fieldOneFiniteStageBruhatSplitHalfDensity S x z) *
      fieldOneFiniteStageBruhatSplitHalfDensity S y z = _
  rfl

theorem fieldOneFiniteStageBruhatHalfDensity_fourier_norm
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    ‖fieldOneFiniteStageBruhatHalfDensityLinearMap S
        (fieldOneFiniteStageBruhatFourierLinearEquiv S x)‖ =
      ‖fieldOneFiniteStageBruhatHalfDensityLinearMap S x‖ := by
  have hinner :
      inner ℂ (fieldOneFiniteStageBruhatHalfDensityLinearMap S
          (fieldOneFiniteStageBruhatFourierLinearEquiv S x))
          (fieldOneFiniteStageBruhatHalfDensityLinearMap S
            (fieldOneFiniteStageBruhatFourierLinearEquiv S x)) =
        inner ℂ (fieldOneFiniteStageBruhatHalfDensityLinearMap S x)
          (fieldOneFiniteStageBruhatHalfDensityLinearMap S x) := by
    rw [← fieldOneFiniteStageBruhatSourceInner_eq_halfDensity_inner,
      fieldOneFiniteStageBruhatFourierLinearEquiv_eq,
      fieldOneFiniteStage_connesMarcolli_lemma_2_33_sourceInner,
      fieldOneFiniteStageBruhatSourceInner_eq_halfDensity_inner]
  have hsquare :
      ‖fieldOneFiniteStageBruhatHalfDensityLinearMap S
          (fieldOneFiniteStageBruhatFourierLinearEquiv S x)‖ ^ 2 =
        ‖fieldOneFiniteStageBruhatHalfDensityLinearMap S x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    have hre := congrArg Complex.re hinner
    norm_cast at hre
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

def fieldOneFiniteStageConnesMarcolliFourierUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageSplitProductL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageSplitProductL2 S :=
  (fieldOneFiniteStageBruhatFourierLinearEquiv S).extendOfIsometry
    (fieldOneFiniteStageBruhatHalfDensityLinearMap S)
    (fieldOneFiniteStageBruhatHalfDensityLinearMap S)
    (fieldOneFiniteStageBruhatHalfDensityLinearMap_denseRange S)
    (fieldOneFiniteStageBruhatHalfDensityLinearMap_denseRange S)
    (fieldOneFiniteStageBruhatHalfDensity_fourier_norm S)

@[simp] theorem fieldOneFiniteStageConnesMarcolliFourierUnitary_halfDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageConnesMarcolliFourierUnitary S
        (fieldOneFiniteStageBruhatHalfDensityLinearMap S x) =
      fieldOneFiniteStageBruhatHalfDensityLinearMap S
        (fieldOneFiniteStageBruhatFourierLinearEquiv S x) := by
  exact LinearEquiv.extendOfIsometry_eq
    (fieldOneFiniteStageBruhatFourierLinearEquiv S)
    (fieldOneFiniteStageBruhatHalfDensityLinearMap S)
    (fieldOneFiniteStageBruhatHalfDensityLinearMap S)
    (fieldOneFiniteStageBruhatHalfDensityLinearMap_denseRange S)
    (fieldOneFiniteStageBruhatHalfDensityLinearMap_denseRange S)
    (fieldOneFiniteStageBruhatHalfDensity_fourier_norm S) x

theorem fieldOneFiniteStage_connesMarcolli_lemma_2_33
    (S : Finset (HeightOneSpectrum ℤ)) :
    ∃! U : FieldOneFiniteStageSplitProductL2 S ≃ₗᵢ[ℂ]
        FieldOneFiniteStageSplitProductL2 S,
      ∀ x : FieldOneFiniteStageBruhatSchwartz S,
        U (fieldOneFiniteStageBruhatHalfDensityLinearMap S x) =
          fieldOneFiniteStageBruhatHalfDensityLinearMap S
            (fieldOneFiniteStageBruhatFourierLinearEquiv S x) := by
  refine ⟨fieldOneFiniteStageConnesMarcolliFourierUnitary S,
    fieldOneFiniteStageConnesMarcolliFourierUnitary_halfDensity S, ?_⟩
  intro U hU
  apply LinearIsometryEquiv.ext
  intro z
  refine (fieldOneFiniteStageBruhatHalfDensityLinearMap_denseRange S).induction ?_
    (isClosed_eq U.continuous
      (fieldOneFiniteStageConnesMarcolliFourierUnitary S).continuous) z
  · rintro _ ⟨x, rfl⟩
    rw [hU, fieldOneFiniteStageConnesMarcolliFourierUnitary_halfDensity]


end
end GaloisForLFunctions.RHTower

