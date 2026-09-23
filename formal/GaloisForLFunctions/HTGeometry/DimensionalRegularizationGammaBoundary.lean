import GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale
import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Dimensional-regularization Gamma boundaries

In `D = 4 - 2*epsilon`, the massless one-loop bubble and one-mass triangle have Gamma kernels

`Gamma(epsilon) * Gamma(1-epsilon)^(2 : ℕ) / Gamma(2-2*epsilon)`

and

`Gamma(1+epsilon) * Gamma(-epsilon)^(2 : ℕ) / Gamma(1-2*epsilon)`.

These are equations (C.1) and (C.2) of M. Wilhelm, *Amplitudes, Form Factors and the
Dilatation Operator in N=4 SYM Theory*, arXiv:1410.6309.  The general dimensional-regularization
framework is also given by Z. Bern, L. Dixon, and D. Kosower, *Dimensionally Regulated One-Loop
Integrals*, arXiv:hep-ph/9212308.

Gauss multiplication and Euler reflection show that each kernel is a nonzero DA gauge times one
half-shift Gamma factor.  Hence each kernel is hypertranscendental in the regulator.  Their
surviving half-shift factors differ by one integer translate, however, so the quotient of the two
HT kernels is differentially algebraic.  Arbitrary elementary exponential scale/readout factors
do not change either conclusion.

This is an observability statement about the exact regulator response: the two loop observables
are individually HT but carry the same translation-orbit charge.  It is not a claim about time
evolution or about the Laurent expansion at `epsilon = 0`.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Gamma-dependent part of the dimensionally regulated massless scalar bubble. -/
def masslessBubbleGammaMero : meroField Set.univ :=
  gammaNatScaleMero 1 0 * gammaNegativeNatScaleMero 1 1 ^ (2 : ℕ) /
    gammaNegativeNatScaleMero 2 2

/-- Nonzero DA gauge left by Gauss/reflection reduction of the bubble kernel. -/
def masslessBubbleGammaGaugeMero : meroField Set.univ :=
  (gammaNegativeNatScaleGaussGaugeMero 2 2)⁻¹ *
    gammaReflectionGaugeMero 1 *
      (gammaReflectionGaugeMero (3 / 2))⁻¹

/-- **Exact bubble orbit normal form.**  The only non-DA factor is `Gamma(epsilon-1/2)`. -/
theorem masslessBubbleGammaMero_normalForm :
    masslessBubbleGammaMero =
      masslessBubbleGammaGaugeMero * gammaShiftMero (-1 / 2) := by
  rw [masslessBubbleGammaMero, gammaNatScaleMero_one,
    gammaNegativeNatScaleMero_one,
    gammaNegativeNatScaleMero_gauss (show 0 < 2 by norm_num) (2 : ℂ)]
  have hprod : gammaNegativeNatScaleGaussProductMero 2 2 =
      gammaNegativeShiftMero 1 * gammaNegativeShiftMero (3 / 2) := by
    norm_num [gammaNegativeNatScaleGaussProductMero,
      Finset.prod_range_succ]
  rw [hprod, gammaNegativeShiftMero_reflection 1,
    gammaNegativeShiftMero_reflection (3 / 2)]
  have hg0 : gammaNegativeNatScaleGaussGaugeMero 2 2 ≠ 0 :=
    gammaNegativeNatScaleGaussGaugeMero_ne_zero (show 0 < 2 by norm_num) 2
  have hr1 : gammaReflectionGaugeMero 1 ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero 1
  have hr32 : gammaReflectionGaugeMero (3 / 2) ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero (3 / 2)
  have hg0s : gammaShiftMero 0 ≠ 0 := gammaShiftMero_ne_zero 0
  have hgm12 : gammaShiftMero (-1 / 2) ≠ 0 := gammaShiftMero_ne_zero (-1 / 2)
  rw [masslessBubbleGammaGaugeMero]
  field_simp [hg0, hr1, hr32, hg0s, hgm12]
  ring

theorem masslessBubbleGammaGaugeMero_ne_zero :
    masslessBubbleGammaGaugeMero ≠ 0 := by
  rw [masslessBubbleGammaGaugeMero]
  exact mul_ne_zero
    (mul_ne_zero
      (inv_ne_zero (gammaNegativeNatScaleGaussGaugeMero_ne_zero
        (show 0 < 2 by norm_num) 2))
      (gammaReflectionGaugeMero_ne_zero 1))
    (inv_ne_zero (gammaReflectionGaugeMero_ne_zero (3 / 2)))

theorem differentialAlgebraicOver_masslessBubbleGammaGaugeMero :
    DifferentialAlgebraicOver (RatFunc ℂ) masslessBubbleGammaGaugeMero := by
  rw [masslessBubbleGammaGaugeMero]
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_mul
      (HTGeometry.differentialAlgebraicOver_inv
        (differentialAlgebraicOver_gammaNegativeNatScaleGaussGaugeMero 2 2))
      (differentialAlgebraicOver_gammaReflectionGaugeMero 1))
    (HTGeometry.differentialAlgebraicOver_inv
      (differentialAlgebraicOver_gammaReflectionGaugeMero (3 / 2)))

/-- The exact massless bubble Gamma kernel is HT in the dimensional regulator. -/
theorem hypertranscendentalOver_masslessBubbleGammaMero :
    HypertranscendentalOver (RatFunc ℂ) masslessBubbleGammaMero := by
  rw [masslessBubbleGammaMero_normalForm, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    differentialAlgebraicOver_masslessBubbleGammaGaugeMero
    masslessBubbleGammaGaugeMero_ne_zero).2
      (by simpa using
        (hypertranscendentalOver_gammaNatScaleMero
          (n := 1) (show 0 < 1 by norm_num) (-1 / 2)))

/-- Gamma-dependent part of the dimensionally regulated one-mass scalar triangle. -/
def masslessTriangleGammaMero : meroField Set.univ :=
  gammaNatScaleMero 1 1 * gammaNegativeNatScaleMero 1 0 ^ (2 : ℕ) /
    gammaNegativeNatScaleMero 2 1

/-- Nonzero DA gauge left by Gauss/reflection reduction of the triangle kernel. -/
def masslessTriangleGammaGaugeMero : meroField Set.univ :=
  (gammaNegativeNatScaleGaussGaugeMero 2 1)⁻¹ *
    gammaReflectionGaugeMero 0 ^ (2 : ℕ) *
      (gammaReflectionGaugeMero (1 / 2))⁻¹ *
        (gammaReflectionGaugeMero 1)⁻¹ *
          reducedVenezianoAmplitudeMero 0 1

/-- **Exact triangle orbit normal form.**  The only non-DA factor is
`Gamma(epsilon+1/2)`. -/
theorem masslessTriangleGammaMero_normalForm :
    masslessTriangleGammaMero =
      masslessTriangleGammaGaugeMero * gammaShiftMero (1 / 2) := by
  rw [masslessTriangleGammaMero, gammaNatScaleMero_one,
    gammaNegativeNatScaleMero_one,
    gammaNegativeNatScaleMero_gauss (show 0 < 2 by norm_num) (1 : ℂ)]
  have hprod : gammaNegativeNatScaleGaussProductMero 2 1 =
      gammaNegativeShiftMero (1 / 2) * gammaNegativeShiftMero 1 := by
    norm_num [gammaNegativeNatScaleGaussProductMero,
      Finset.prod_range_succ]
  rw [hprod, gammaNegativeShiftMero_reflection 0,
    gammaNegativeShiftMero_reflection (1 / 2),
    gammaNegativeShiftMero_reflection 1]
  have hG : gammaNegativeNatScaleGaussGaugeMero 2 1 ≠ 0 :=
    gammaNegativeNatScaleGaussGaugeMero_ne_zero (show 0 < 2 by norm_num) 1
  have hr0 : gammaReflectionGaugeMero 0 ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero 0
  have hr12 : gammaReflectionGaugeMero (1 / 2) ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero (1 / 2)
  have hr1 : gammaReflectionGaugeMero 1 ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero 1
  have hg0 : gammaShiftMero 0 ≠ 0 := gammaShiftMero_ne_zero 0
  have hg1 : gammaShiftMero 1 ≠ 0 := gammaShiftMero_ne_zero 1
  have hghalf : gammaShiftMero (1 / 2) ≠ 0 := gammaShiftMero_ne_zero (1 / 2)
  rw [masslessTriangleGammaGaugeMero, reducedVenezianoAmplitudeMero]
  norm_num
  field_simp [hG, hr0, hr12, hr1, hg0, hg1, hghalf]

theorem masslessTriangleGammaGaugeMero_ne_zero :
    masslessTriangleGammaGaugeMero ≠ 0 := by
  have hred : reducedVenezianoAmplitudeMero 0 1 ≠ 0 := by
    rw [reducedVenezianoAmplitudeMero]
    exact div_ne_zero (gammaShiftMero_ne_zero 0) (gammaShiftMero_ne_zero (0 + 1))
  rw [masslessTriangleGammaGaugeMero]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (inv_ne_zero (gammaNegativeNatScaleGaussGaugeMero_ne_zero
            (show 0 < 2 by norm_num) 1))
          (pow_ne_zero 2 (gammaReflectionGaugeMero_ne_zero 0)))
        (inv_ne_zero (gammaReflectionGaugeMero_ne_zero (1 / 2))))
      (inv_ne_zero (gammaReflectionGaugeMero_ne_zero 1)))
    hred

theorem differentialAlgebraicOver_masslessTriangleGammaGaugeMero :
    DifferentialAlgebraicOver (RatFunc ℂ) masslessTriangleGammaGaugeMero := by
  have hred : DifferentialAlgebraicOver (RatFunc ℂ)
      (reducedVenezianoAmplitudeMero 0 1) :=
    (differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
      0 1).2 ⟨1, by norm_num⟩
  rw [masslessTriangleGammaGaugeMero]
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_mul
      (HTGeometry.differentialAlgebraicOver_mul
        (HTGeometry.differentialAlgebraicOver_mul
          (HTGeometry.differentialAlgebraicOver_inv
            (differentialAlgebraicOver_gammaNegativeNatScaleGaussGaugeMero 2 1))
          (HTGeometry.differentialAlgebraicOver_pow
            (differentialAlgebraicOver_gammaReflectionGaugeMero 0) 2))
        (HTGeometry.differentialAlgebraicOver_inv
          (differentialAlgebraicOver_gammaReflectionGaugeMero (1 / 2))))
      (HTGeometry.differentialAlgebraicOver_inv
        (differentialAlgebraicOver_gammaReflectionGaugeMero 1)))
    hred

/-- The exact one-mass triangle Gamma kernel is HT in the dimensional regulator. -/
theorem hypertranscendentalOver_masslessTriangleGammaMero :
    HypertranscendentalOver (RatFunc ℂ) masslessTriangleGammaMero := by
  rw [masslessTriangleGammaMero_normalForm, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    differentialAlgebraicOver_masslessTriangleGammaGaugeMero
    masslessTriangleGammaGaugeMero_ne_zero).2
      (by simpa using
        (hypertranscendentalOver_gammaNatScaleMero
          (n := 1) (show 0 < 1 by norm_num) (1 / 2)))

/-- **Positive common-orbit cancellation law.**  Although the bubble and triangle kernels are
individually HT, their quotient is DA because their residual half-shift Gamma factors differ by
one integer translate. -/
theorem differentialAlgebraicOver_masslessTriangleGammaMero_div_masslessBubbleGammaMero :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (masslessTriangleGammaMero / masslessBubbleGammaMero) := by
  have hratio : gammaShiftMero (1 / 2) / gammaShiftMero (-1 / 2) =
      (reducedVenezianoAmplitudeMero (-1 / 2) 1)⁻¹ := by
    rw [reducedVenezianoAmplitudeMero]
    norm_num
  have hratioDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaShiftMero (1 / 2) / gammaShiftMero (-1 / 2)) := by
    rw [hratio]
    exact HTGeometry.differentialAlgebraicOver_inv
      ((differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
        (-1 / 2) 1).2 ⟨1, by norm_num⟩)
  rw [masslessTriangleGammaMero_normalForm,
    masslessBubbleGammaMero_normalForm]
  have heq :
      (masslessTriangleGammaGaugeMero * gammaShiftMero (1 / 2)) /
          (masslessBubbleGammaGaugeMero * gammaShiftMero (-1 / 2)) =
        (masslessTriangleGammaGaugeMero / masslessBubbleGammaGaugeMero) *
          (gammaShiftMero (1 / 2) / gammaShiftMero (-1 / 2)) := by
    field_simp [masslessBubbleGammaGaugeMero_ne_zero,
      gammaShiftMero_ne_zero (-1 / 2)]
  rw [heq]
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_div
      differentialAlgebraicOver_masslessTriangleGammaGaugeMero
      differentialAlgebraicOver_masslessBubbleGammaGaugeMero)
    hratioDA

/-- Bubble kernel including an arbitrary elementary exponential scale/readout gauge. -/
def masslessBubbleOneLoopMero (lambda : ℂ) : meroField Set.univ :=
  masslessBubbleGammaMero * physicalExponentialMero lambda

/-- Triangle kernel including an arbitrary elementary exponential scale/readout gauge. -/
def masslessTriangleOneLoopMero (lambda : ℂ) : meroField Set.univ :=
  masslessTriangleGammaMero * physicalExponentialMero lambda

theorem hypertranscendentalOver_masslessBubbleOneLoopMero (lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (masslessBubbleOneLoopMero lambda) := by
  rw [masslessBubbleOneLoopMero,
    HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_physicalExponentialMero lambda)
      (physicalExponentialMero_ne_zero lambda)]
  exact hypertranscendentalOver_masslessBubbleGammaMero

theorem hypertranscendentalOver_masslessTriangleOneLoopMero (lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (masslessTriangleOneLoopMero lambda) := by
  rw [masslessTriangleOneLoopMero,
    HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_physicalExponentialMero lambda)
      (physicalExponentialMero_ne_zero lambda)]
  exact hypertranscendentalOver_masslessTriangleGammaMero

/-- No rational or finite-Laurent regulator ansatz can equal the exact exponential-dressed bubble
response.  This includes every fixed finite truncation whose regulator dependence lies in
`C(epsilon)`. -/
theorem masslessBubbleOneLoopMero_ne_ratFuncModel (lambda : ℂ) (r : RatFunc ℂ) :
    masslessBubbleOneLoopMero lambda ≠
      algebraMap (RatFunc ℂ) (meroField Set.univ) r := by
  intro heq
  apply hypertranscendentalOver_masslessBubbleOneLoopMero lambda
  rw [heq]
  exact HTGeometry.differentialAlgebraicOver_algebraMap r

/-- No rational or finite-Laurent regulator ansatz can equal the exact exponential-dressed
one-mass triangle response. -/
theorem masslessTriangleOneLoopMero_ne_ratFuncModel (lambda : ℂ) (r : RatFunc ℂ) :
    masslessTriangleOneLoopMero lambda ≠
      algebraMap (RatFunc ℂ) (meroField Set.univ) r := by
  intro heq
  apply hypertranscendentalOver_masslessTriangleOneLoopMero lambda
  rw [heq]
  exact HTGeometry.differentialAlgebraicOver_algebraMap r

/-- The common-orbit cancellation survives arbitrary exponential scale/readout gauges. -/
theorem differentialAlgebraicOver_masslessTriangleOneLoopMero_div_masslessBubbleOneLoopMero
    (lambdaTriangle lambdaBubble : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (masslessTriangleOneLoopMero lambdaTriangle /
        masslessBubbleOneLoopMero lambdaBubble) := by
  rw [masslessTriangleOneLoopMero, masslessBubbleOneLoopMero]
  have heq :
      (masslessTriangleGammaMero * physicalExponentialMero lambdaTriangle) /
          (masslessBubbleGammaMero * physicalExponentialMero lambdaBubble) =
        (masslessTriangleGammaMero / masslessBubbleGammaMero) *
          (physicalExponentialMero lambdaTriangle /
            physicalExponentialMero lambdaBubble) := by
    field_simp [physicalExponentialMero_ne_zero lambdaBubble]
  rw [heq]
  exact HTGeometry.differentialAlgebraicOver_mul
    differentialAlgebraicOver_masslessTriangleGammaMero_div_masslessBubbleGammaMero
    (HTGeometry.differentialAlgebraicOver_div
      (differentialAlgebraicOver_physicalExponentialMero lambdaTriangle)
      (differentialAlgebraicOver_physicalExponentialMero lambdaBubble))

end

end GaloisForLFunctions
