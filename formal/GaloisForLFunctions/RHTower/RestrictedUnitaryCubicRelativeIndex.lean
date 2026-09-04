import GaloisForLFunctions.HTGeometry.TwoProjectionHilbertSchmidtEnergy
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.RHTower.FrankensteinCCMRoutePBaseCubicGreenSourceBridge
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall

/-!
# Restricted-unitary cubic relative index

This module starts from the actual critical ideal boundary: a self-adjoint difference of two
orthogonal projections is only assumed Hilbert--Schmidt.  Its cubic power is nevertheless
Schatten one and splits exactly into the two oriented positive projection channels.  The scalar
source side is the literal natural-number von Mangoldt carrier of the Route-P base budget.

No divisor, zero ordinate, RH hypothesis, axiom, or finite computation occurs below.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Difference of two orthogonal polarizations. -/
def restrictedProjectionDisplacement (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  R - P

/-- First odd nuclear polynomial at the Hilbert--Schmidt boundary. -/
def restrictedProjectionCubicDefect (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  restrictedProjectionDisplacement R P ^ 3

/-- Positive channel in which `R` exits the `P` polarization. -/
def restrictedProjectionPositiveChannel (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  R * (1 - P) * R

/-- A difference of self-adjoint polarizations is self-adjoint. -/
theorem adjoint_restrictedProjectionDisplacement
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionDisplacement R P) =
      restrictedProjectionDisplacement R P := by
  rw [restrictedProjectionDisplacement, ContinuousLinearMap.adjoint.map_sub, hR, hP]

/-- Two Hilbert--Schmidt factors make the square nuclear; the ideal law then makes the cubic
nuclear without strengthening the displacement to Schatten one. -/
theorem restrictedProjectionCubicDefect_memSchattenClass_one
    (R P : H →L[ℂ] H)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    MemSchattenClass 1 (restrictedProjectionCubicDefect R P) := by
  have hsqRect :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hDelta hDelta
  have hsq : MemSchattenClass 1
      ((restrictedProjectionDisplacement R P) ∘L
        restrictedProjectionDisplacement R P) :=
    (memRectSchattenClass_iff_memSchattenClass
      1 (restrictedProjectionDisplacement R P ∘L
        restrictedProjectionDisplacement R P)).mp hsqRect
  have hcube := memSchattenClass_one_comp_right hsq
    (restrictedProjectionDisplacement R P)
  simpa [restrictedProjectionCubicDefect, pow_succ, ContinuousLinearMap.mul_def] using hcube

/-- Cubing preserves self-adjointness of the projection displacement. -/
theorem adjoint_restrictedProjectionCubicDefect
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionCubicDefect R P) =
      restrictedProjectionCubicDefect R P := by
  rw [restrictedProjectionCubicDefect, show (restrictedProjectionDisplacement R P) ^ 3 =
      ((restrictedProjectionDisplacement R P) ∘L
          restrictedProjectionDisplacement R P) ∘L
        restrictedProjectionDisplacement R P by
      simp [pow_succ, ContinuousLinearMap.mul_def]]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictedProjectionDisplacement R P hR hP]
  ext x
  rfl

omit [CompleteSpace H] in
/-- Exact positive-channel decomposition `(R-P)^3 = R(1-P)R - P(1-R)P`. -/
theorem restrictedProjectionCubicDefect_eq_channels
    (R P : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hP : IsIdempotentElem P) :
    restrictedProjectionCubicDefect R P =
      restrictedProjectionPositiveChannel R P -
        restrictedProjectionPositiveChannel P R := by
  change (R - P) ^ 3 = R * (1 - P) * R - P * (1 - R) * P
  have hRR : R * R = R := hR
  have hPP : P * P = P := hP
  noncomm_ring [hRR, hPP]

/-- Orientation reversal negates the cubic defect exactly. -/
theorem restrictedProjectionCubicDefect_swap
    (R P : H →L[ℂ] H) :
    restrictedProjectionCubicDefect P R = -restrictedProjectionCubicDefect R P := by
  rw [restrictedProjectionCubicDefect, restrictedProjectionCubicDefect,
    restrictedProjectionDisplacement, restrictedProjectionDisplacement]
  noncomm_ring

/-- The natural-number source weight is exactly the unsquared von Mangoldt mass divided by the
cubic logarithmic clock. -/
theorem routePPrimeGammaBaseCubicWeight_eq_vonMangoldt (n : ℕ) :
    routePPrimeGammaBaseCubicWeight n =
      finiteVonMangoldtRealWeight n / (4 * Real.log n ^ 3) := by
  rw [routePPrimeGammaBaseCubicWeight, routePPrimeGammaCubicWeight,
    vonMangoldtInverseLogPowerWeight]
  norm_num
  ring

/-- Exact source identity and strict subunit bound for the complete cubic Route-P budget. -/
theorem restrictedUnitaryCubic_sourceBudget_closed :
    (∑' n : ℕ, routePPrimeGammaBaseCubicWeight n) =
        routePPrimitiveBaseCauchyCubicTraceBudget ∧
      routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  exact ⟨tsum_routePPrimeGammaBaseCubicWeight_eq_budget,
    routePPrimitiveBaseCauchyCubicTraceBudget_lt_one⟩

/-- Hypothesis-free certificate for the projection algebra and literal source identities proved
in this module.  Quantification retains the full infinite-dimensional Hilbert-space statement. -/
theorem restrictedUnitaryCubicRelativeIndex_algebra_closed :
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (R P : H →L[ℂ] H),
      IsIdempotentElem R → IsIdempotentElem P →
      ContinuousLinearMap.adjoint R = R → ContinuousLinearMap.adjoint P = P →
      (restrictedProjectionDisplacement R P).IsHilbertSchmidt →
      ContinuousLinearMap.adjoint (restrictedProjectionDisplacement R P) =
          restrictedProjectionDisplacement R P ∧
        ContinuousLinearMap.adjoint (restrictedProjectionCubicDefect R P) =
          restrictedProjectionCubicDefect R P ∧
        MemSchattenClass 1 (restrictedProjectionCubicDefect R P) ∧
        restrictedProjectionCubicDefect R P =
          restrictedProjectionPositiveChannel R P -
            restrictedProjectionPositiveChannel P R) ∧
    (∀ n, routePPrimeGammaBaseCubicWeight n =
      finiteVonMangoldtRealWeight n / (4 * Real.log n ^ 3)) ∧
    (∑' n : ℕ, routePPrimeGammaBaseCubicWeight n) =
      routePPrimitiveBaseCauchyCubicTraceBudget ∧
    routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  refine ⟨?_, routePPrimeGammaBaseCubicWeight_eq_vonMangoldt, ?_, ?_⟩
  · intro H _ _ _ R P hR hP hRadj hPadj hDelta
    exact ⟨adjoint_restrictedProjectionDisplacement R P hRadj hPadj,
      adjoint_restrictedProjectionCubicDefect R P hRadj hPadj,
      restrictedProjectionCubicDefect_memSchattenClass_one R P hDelta,
      restrictedProjectionCubicDefect_eq_channels R P hR hP⟩
  · exact tsum_routePPrimeGammaBaseCubicWeight_eq_budget
  · exact routePPrimitiveBaseCauchyCubicTraceBudget_lt_one

end RHTower
