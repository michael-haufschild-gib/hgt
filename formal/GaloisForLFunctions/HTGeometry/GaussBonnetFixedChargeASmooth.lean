import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAParameters
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceALogarithm
import GaloisForLFunctions.HTGeometry.ThermalAmplificationFluctuations
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differentiability of the actual fixed-charge coexistence path

Prove differentiability from the explicit logarithmic kernel and positive
quadratic radical. No derivative of the auxiliary arcsine angle is used,
so zero coupling and zero electric charge remain included.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

private theorem ratio_differentiable : Differentiable ℝ thermalRatio :=
  fun τ => (thermalRatio_hasDerivAt τ).differentiableAt

theorem egbCoexistenceALogKernel_differentiable : Differentiable ℝ egbCoexistenceALogKernel := by
  have hz := ratio_differentiable
  have hn : ∀ τ, thermalRatio τ - 1 ≠ 0 := fun τ => sub_ne_zero.mpr (ne_of_lt (thermalRatio_lt_one τ))
  have hlog := hz.log (fun τ => (thermalRatio_pos τ).ne')
  have hformula : egbCoexistenceALogKernel = fun τ =>
      (3 * (thermalRatio τ + 1) * (thermalRatio τ ^ (2 : ℕ) + 1) * (log (thermalRatio τ) / (thermalRatio τ - 1)) -
        4 * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1)) / (thermalRatio τ - 1) ^ (2 : ℕ) :=
    funext egbCoexistenceALogKernel_logarithmic_formula
  rw [hformula]
  exact (((((hz.add_const 1).const_mul 3).mul ((hz.pow 2).add_const 1)).mul
    (hlog.div (hz.sub_const 1) hn)).sub ((((hz.pow 2).add hz).add_const 1).const_mul 4)).div
      ((hz.sub_const 1).pow 2) (fun τ => pow_ne_zero 2 (hn τ))

theorem egbCoexistenceShape_differentiable : Differentiable ℝ egbCoexistenceShape :=
  ((ratio_differentiable.pow 2).add (ratio_differentiable.const_mul 4)).add_const 1

theorem egbCoexistenceAQuadraticA_differentiable : Differentiable ℝ egbCoexistenceAQuadraticA :=
  (egbCoexistenceALogKernel_differentiable.const_mul 4).mul ((ratio_differentiable.pow 2).add_const 1)

theorem egbCoexistenceAQuadraticC_differentiable : Differentiable ℝ egbCoexistenceAQuadraticC :=
  (ratio_differentiable.pow 2).mul ((ratio_differentiable.pow 2).add_const 1)

theorem egbFixedChargeABase_differentiable : Differentiable ℝ egbFixedChargeABase :=
  egbCoexistenceShape_differentiable.mul ((ratio_differentiable.pow 2).add_const 1)

theorem egbFixedChargeALinearCorrection_differentiable : Differentiable ℝ egbFixedChargeALinearCorrection :=
  (((ratio_differentiable.pow 2).const_mul 4).mul egbCoexistenceALogKernel_differentiable).sub
    ((ratio_differentiable.const_mul 8).mul (((ratio_differentiable.pow 2).add ratio_differentiable).add_const 1))

theorem egbFixedChargeAQuadraticB_differentiable (φ : ℝ) : Differentiable ℝ (fun τ => egbFixedChargeAQuadraticB τ φ) :=
  egbFixedChargeABase_differentiable.sub (egbFixedChargeALinearCorrection_differentiable.const_mul (egbFixedChargeAFraction φ))

theorem egbFixedChargeADiscriminant_differentiable (φ : ℝ) : Differentiable ℝ (fun τ => egbFixedChargeADiscriminant τ φ) :=
  ((egbFixedChargeAQuadraticB_differentiable φ).pow 2).add
    (((egbCoexistenceAQuadraticA_differentiable.const_mul 4).mul_const (egbFixedChargeAFraction φ)).mul
      egbCoexistenceAQuadraticC_differentiable)

theorem egbFixedChargeAWeight_differentiable (φ : ℝ) : Differentiable ℝ (fun τ => egbFixedChargeAWeight τ φ) := by
  have hs := (egbFixedChargeADiscriminant_differentiable φ).sqrt (fun τ => (egbFixedChargeADiscriminant_pos τ φ).ne')
  exact (egbCoexistenceAQuadraticC_differentiable.const_mul 2).div
    ((egbFixedChargeAQuadraticB_differentiable φ).add hs) (fun τ => by
      have hB := egbFixedChargeAQuadraticB_pos τ φ
      positivity)

theorem egbFixedChargeACouplingWeight_differentiable (φ : ℝ) : Differentiable ℝ (fun τ => egbFixedChargeACouplingWeight τ φ) :=
  (egbFixedChargeAWeight_differentiable φ).const_mul (egbFixedChargeAFraction φ)

theorem egbFixedChargeADenominator_differentiable (φ : ℝ) : Differentiable ℝ (fun τ => egbFixedChargeADenominator τ φ) :=
  egbCoexistenceShape_differentiable.add (((egbFixedChargeACouplingWeight_differentiable φ).const_mul 4).mul
    egbCoexistenceALogKernel_differentiable)

theorem egbFixedChargeATemperatureWeight_differentiable (φ : ℝ) : Differentiable ℝ (fun τ => egbFixedChargeATemperatureWeight τ φ) :=
  ((ratio_differentiable.add_const 1).const_mul 4).div (egbFixedChargeADenominator_differentiable φ)
    (fun τ => (egbFixedChargeADenominator_pos τ φ).ne')

theorem egbFixedChargeAPressureWeight_differentiable (φ : ℝ) : Differentiable ℝ (fun τ => egbFixedChargeAPressureWeight τ φ) :=
  ((((ratio_differentiable.pow 2).add_const 1).const_mul 3).add
    (((egbFixedChargeACouplingWeight_differentiable φ).const_mul 4).mul
      (egbCoexistenceALogKernel_differentiable.const_sub 2))).div
        ((egbFixedChargeADenominator_differentiable φ).mul ((ratio_differentiable.pow 2).add_const 1))
          (fun τ => by have h := egbFixedChargeADenominator_pos τ φ; positivity)

theorem egbFixedChargeALargeRadius_differentiable (w φ : ℝ) : Differentiable ℝ (egbFixedChargeALargeRadius w φ) :=
  (differentiable_const (exp w)).div
    ((egbFixedChargeAWeight_differentiable φ).sqrt (fun τ => (egbFixedChargeAWeight_pos τ φ).ne'))
      (fun τ => (sqrt_pos.mpr (egbFixedChargeAWeight_pos τ φ)).ne')

theorem egbFixedChargeASmallRadius_differentiable (w φ : ℝ) : Differentiable ℝ (egbFixedChargeASmallRadius w φ) :=
  ratio_differentiable.mul (egbFixedChargeALargeRadius_differentiable w φ)

theorem egbFixedChargeALogScale_differentiable (w φ : ℝ) : Differentiable ℝ (egbFixedChargeALogScale w φ) :=
  (egbFixedChargeALargeRadius_differentiable w φ).log (fun τ => (egbFixedChargeALargeRadius_pos w φ τ).ne')

theorem egbFixedChargeATemperature_differentiable (w φ : ℝ) : Differentiable ℝ (egbFixedChargeATemperature w φ) :=
  (egbFixedChargeATemperatureWeight_differentiable φ).div
    ((egbFixedChargeALargeRadius_differentiable w φ).const_mul (4 * Real.pi))
      (fun τ => by have h := egbFixedChargeALargeRadius_pos w φ τ; positivity)

theorem egbFixedChargeAPressure_differentiable (w φ : ℝ) : Differentiable ℝ (egbFixedChargeAPressure w φ) :=
  (egbFixedChargeAPressureWeight_differentiable φ).div
    (((egbFixedChargeALargeRadius_differentiable w φ).pow 2).const_mul (8 * Real.pi))
      (fun τ => by have h := egbFixedChargeALargeRadius_pos w φ τ; positivity)

end GaloisForLFunctions.HTGeometry
