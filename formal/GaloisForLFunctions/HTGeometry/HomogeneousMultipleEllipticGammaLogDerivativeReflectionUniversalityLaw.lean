import GaloisForLFunctions.HTGeometry.HomogeneousMultipleEllipticGammaScaleReflectionUniversalityLaw

/-!
# Homogeneous multiple elliptic-Gamma logarithmic-derivative reflection universality

Restoring the base period does more than make the multiple elliptic-Gamma value scale invariant.
Its logarithmic derivative becomes a covector of homogeneous weight `-1`: simultaneous nonzero
scaling of every period and the argument multiplies it by the inverse scale. Reflection through
the physical period sum acts on the same covector by the rank-parity sign.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι]

local instance homogeneousMultipleEllipticGammaLogDerivativeUnivDomain :
    IsDomain (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTUnivDomain

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexAlgebraAnalytic :
    Algebra ℂ (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraAnalytic

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexAlgebraMero :
    Algebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraMero

local instance homogeneousMultipleEllipticGammaLogDerivativeMeroDifferential :
    Differential (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroDifferential

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexDifferential :
    Differential ℂ :=
  multipleEllipticGammaHTComplexDifferential

local instance homogeneousMultipleEllipticGammaLogDerivativeMeroCharZero :
    CharZero (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroCharZero

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexDifferentialAlgebra

local instance homogeneousMultipleEllipticGammaLogDerivativeCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  multipleEllipticGammaHTCoordinateDifferential

local instance homogeneousMultipleEllipticGammaLogDerivativeCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTCoordinateDifferentialAlgebra

/-- The parity-dependent normalized multiple elliptic-Gamma product is differentiable at every
point where its backward product is nonzero. The assumption is needed only in even rank, where
the backward product is the denominator. -/
theorem differentiableAt_multipleEllipticGammaProduct_of_backward_ne_zero
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) {z : ℂ}
    (hzB : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    DifferentiableAt ℂ (multipleEllipticGammaProduct τ) z := by
  change DifferentiableAt ℂ
    (fun w => if Even (Fintype.card ι) then
      multipleEllipticGammaForwardProduct τ w /
        multipleEllipticGammaBackwardProduct τ w
    else
      multipleEllipticGammaForwardProduct τ w *
        multipleEllipticGammaBackwardProduct τ w) z
  by_cases hcard : Even (Fintype.card ι)
  · simp only [hcard, if_true]
    exact
      (differentiable_multipleEllipticGammaForwardProduct hτ).differentiableAt.div
        (differentiable_multipleEllipticGammaBackwardProduct hτ).differentiableAt hzB
  · simp only [hcard, if_false]
    exact
      (differentiable_multipleEllipticGammaForwardProduct hτ).differentiableAt.mul
        (differentiable_multipleEllipticGammaBackwardProduct hτ).differentiableAt

/-- The homogeneous logarithmic derivative is the normalized logarithmic derivative multiplied
by the inverse base period. -/
theorem logDeriv_homogeneousMultipleEllipticGammaProduct_eq
    (ω₀ : ℂ) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im) (z : ℂ)
    (hzB : multipleEllipticGammaBackwardProduct
      (fun i => ω i / ω₀) (z / ω₀) ≠ 0) :
    logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z =
      logDeriv (multipleEllipticGammaProduct (fun i => ω i / ω₀)) (z / ω₀) *
        (1 / ω₀) := by
  change logDeriv
      (multipleEllipticGammaProduct (fun i => ω i / ω₀) ∘ fun w : ℂ => w / ω₀) z = _
  have hg : DifferentiableAt ℂ (fun w : ℂ => w / ω₀) z := by
    fun_prop
  have hchain := logDeriv_comp
    (f := multipleEllipticGammaProduct (fun i => ω i / ω₀))
    (g := fun w : ℂ => w / ω₀) (x := z)
    (differentiableAt_multipleEllipticGammaProduct_of_backward_ne_zero hω hzB) hg
  simpa only [Function.comp_apply, deriv_div_const, deriv_id''] using hchain

/-- **Homogeneous weight-minus-one law.** Simultaneously scaling every period and the argument
by a nonzero scalar multiplies the physical logarithmic derivative by the inverse scalar. -/
theorem logDeriv_homogeneousMultipleEllipticGammaProduct_scale
    (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (hω₀ : ω₀ ≠ 0)
    (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i / ω₀).im) (z : ℂ)
    (hzB : multipleEllipticGammaBackwardProduct
      (fun i => ω i / ω₀) (z / ω₀) ≠ 0) :
    logDeriv
        (homogeneousMultipleEllipticGammaProduct (c * ω₀) (fun i => c * ω i))
        (c * z) =
      c⁻¹ * logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z := by
  have hscaled : ∀ i, 0 < ((c * ω i) / (c * ω₀)).im := by
    intro i
    rw [mul_div_mul_left (ω i) ω₀ hc]
    exact hω i
  rw [logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      (c * ω₀) (fun i => c * ω i) hscaled (c * z) (by
        simpa only [mul_div_mul_left _ _ hc] using hzB)]
  rw [logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      ω₀ ω hω z hzB]
  simp_rw [mul_div_mul_left _ _ hc]
  field_simp

/-- **Physical-period logarithmic reflection law.** Reflection through the unnormalized period
sum acts on the homogeneous logarithmic derivative by the rank-parity sign. -/
theorem logDeriv_homogeneousMultipleEllipticGammaProduct_reflection
    (ω₀ : ℂ) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im) (z : ℂ)
    (hzF : multipleEllipticGammaForwardProduct (fun i => ω i / ω₀) (z / ω₀) ≠ 0)
    (hzB : multipleEllipticGammaBackwardProduct (fun i => ω i / ω₀) (z / ω₀) ≠ 0) :
    logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω)
        ((∑ i, ω i) - z) =
      multipleEllipticGammaLogSign ι *
        logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z := by
  have hcenter :
      ((∑ i, ω i) - z) / ω₀ =
        (∑ i, ω i / ω₀) - z / ω₀ := by
    rw [sub_div, Finset.sum_div]
  obtain ⟨hrF, hrB⟩ :=
    multipleEllipticGammaProducts_reflection_ne_zero hzF hzB
  rw [logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      ω₀ ω hω ((∑ i, ω i) - z) (by
        rw [hcenter]
        exact hrB),
    logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      ω₀ ω hω z hzB,
    hcenter,
    logDeriv_multipleEllipticGammaProduct_reflection hω hzF hzB]
  ring

/-- **Homogeneous multiple elliptic-Gamma log-derivative universality law.** A rank-three minor
forces hypertranscendence of the product and its logarithmic derivative, while the restored
physical logarithmic derivative has homogeneous weight `-1` and parity reflection through the
physical period sum. -/
theorem homogeneousMultipleEllipticGamma_logDerivativeScaleReflectionUniversality
    [DecidableEq ι] (ω₀ : ℂ) (hω₀ : ω₀ ≠ 0) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor (fun i => ω i / ω₀)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero (fun i => ω i / ω₀) hω) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero (fun i => ω i / ω₀) hω) ∧
      (∀ (c : ℂ), c ≠ 0 → ∀ z : ℂ,
        multipleEllipticGammaBackwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        logDeriv
            (homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i))
            (c * z) =
          c⁻¹ * logDeriv
            (homogeneousMultipleEllipticGammaProduct ω₀ ω) z) ∧
      ∀ z : ℂ,
        multipleEllipticGammaForwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        multipleEllipticGammaBackwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω)
            ((∑ i, ω i) - z) =
          multipleEllipticGammaLogSign ι *
            logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z := by
  have hbase :=
    homogeneousMultipleEllipticGamma_scaleReflectionHypertranscendenceUniversality
      ω₀ ω hω hminor
  refine ⟨hbase.1, hbase.2.1, ?_, ?_⟩
  · intro c hc z hzB
    exact logDeriv_homogeneousMultipleEllipticGammaProduct_scale
      c hc ω₀ hω₀ ω hω z hzB
  · intro z hzF hzB
    exact logDeriv_homogeneousMultipleEllipticGammaProduct_reflection
      ω₀ ω hω z hzF hzB

end

end GaloisForLFunctions
