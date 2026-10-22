import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeGammaExteriorReflectionProjector
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmExteriorCayleyAbelGreenLanding

/-!
# Fixed-center prime--Gamma exterior reflection energy

The nearest-integer exterior reporter is useful zero-side but its center depends on the divisor.
This module removes that source-provenance defect.  Two adjacent critical features are fixed first,
before divisor expansion.  The mixed prime/Cayley reflection projector then selects line-reflected
pairs, while the Cayley--Abel boundary supplies the transverse Green factor.  The reflected
projector term is exactly the norm square of the fixed-center normalized exterior coefficient.

Thus a reflection-closed finite packet is the Cesaro limit of fixed-feature oriented determinants
and lands in a positive exterior energy.  Both adjacent orientations are retained.  This is an
unconditional fixed-feature divisor landing compatible with the existing prime--Gamma formulas.
Identifying every clocked finite approximant with a pre-divisor source expression and proving its
arithmetic upper bound remain separate; no zero-density conclusion is asserted.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One fixed real-centered critical Cauchy feature evaluated at a Xi divisor point. -/
def xiFixedCriticalFeatureValue (t : ℝ) (rho : XiDivisorSupport) : ℂ :=
  criticalFeatureCauchyKernelTest t (xiSpectralPointSupport rho)

/-- Fixed-center adjacent Pluecker coordinate on a divisor point and its line reflection. -/
theorem xiFixedCriticalFeaturePluecker_eq_adjacentDet
    (t : ℝ) (rho : XiDivisorSupport) :
    xiFixedCriticalFeatureValue t rho *
          xiFixedCriticalFeatureValue (t + 1) (xiZeroLineConjEquiv rho) -
        xiFixedCriticalFeatureValue t (xiZeroLineConjEquiv rho) *
          xiFixedCriticalFeatureValue (t + 1) rho =
      adjacentCriticalFeatureEvaluationDet t (xiSpectralPointSupport rho)
        (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) := by
  rw [xiFixedCriticalFeatureValue, xiFixedCriticalFeatureValue,
    xiFixedCriticalFeatureValue, xiFixedCriticalFeatureValue,
    xiSpectralPointSupport_lineConj_boundaryClosure]
  rw [adjacentCriticalFeatureEvaluationDet]
  rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
  rfl

/-- Fixed-center adjacent exterior coefficient at one Abel radius. -/
def xiFixedAdjacentCayleyAbelCoefficient
    (R t : ℝ) (rho : XiDivisorSupport) : ℂ :=
  xiExteriorCayleyAbelGreenMultiplier R rho *
    adjacentCriticalFeatureEvaluationDet t (xiSpectralPointSupport rho)
      (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho)

/-- The fixed-center coefficient vanishes identically on the critical line. -/
theorem xiFixedAdjacentCayleyAbelCoefficient_eq_zero_of_onLine
    (R t : ℝ) (rho : XiDivisorSupport) (hline : (rho : ℂ).re = 1 / 2) :
    xiFixedAdjacentCayleyAbelCoefficient R t rho = 0 := by
  have hy : (xiSpectralPointSupport rho).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
  rw [xiFixedAdjacentCayleyAbelCoefficient,
    adjacentCriticalFeatureEvaluationDet_eq_zero_of_im_eq_zero _ _
      (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) hy,
    mul_zero]

/-- At the Abel boundary, critical-line reflection negates the transverse Green coordinate. -/
theorem xiExteriorCayleyAbelGreenMultiplier_lineConj_one_eq_neg
    (rho : XiDivisorSupport) :
    xiExteriorCayleyAbelGreenMultiplier 1 (xiZeroLineConjEquiv rho) =
      -xiExteriorCayleyAbelGreenMultiplier 1 rho := by
  by_cases hline : (rho : ℂ).re = 1 / 2
  · have hrefLine : ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ).re = 1 / 2 := by
      rw [xiZeroLineConjEquiv_apply]
      norm_num [hline]
    rw [xiExteriorCayleyAbelGreenMultiplier, xiExteriorCayleyAbelGreenMultiplier]
    norm_num [xiHorizontalSourceCayleyPhase, sourceCayleyAbelGreenMultiplier,
      GaloisForLFunctions.HTGeometry.realCayley, hline, hrefLine]
  · have href : ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ).re ≠ 1 / 2 := by
      rw [xiZeroLineConjEquiv_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      intro h
      apply hline
      linarith
    rw [xiExteriorCayleyAbelGreenMultiplier_one_eq_inv_im _ href,
      xiExteriorCayleyAbelGreenMultiplier_one_eq_inv_im rho hline,
      xiSpectralPointSupport_lineConj_boundaryClosure]
    simp

/-- Reflecting the spectral point reverses the adjacent Pluecker orientation. -/
theorem adjacentCriticalFeatureEvaluationDet_lineConj_eq_neg
    (t : ℝ) (rho : XiDivisorSupport) :
    adjacentCriticalFeatureEvaluationDet t
        (xiSpectralPointSupport (xiZeroLineConjEquiv rho))
        (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier
          (xiZeroLineConjEquiv rho)) =
      -adjacentCriticalFeatureEvaluationDet t (xiSpectralPointSupport rho)
        (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) := by
  rw [adjacentCriticalFeatureEvaluationDet, adjacentCriticalFeatureEvaluationDet]
  simp [xiSpectralPointSupport_lineConj_boundaryClosure]

/-- Both sign reversals cancel: the boundary coefficient is reflection-invariant. -/
theorem xiFixedAdjacentCayleyAbelCoefficient_lineConj_one_eq
    (t : ℝ) (rho : XiDivisorSupport) :
    xiFixedAdjacentCayleyAbelCoefficient 1 t (xiZeroLineConjEquiv rho) =
      xiFixedAdjacentCayleyAbelCoefficient 1 t rho := by
  rw [xiFixedAdjacentCayleyAbelCoefficient,
    xiFixedAdjacentCayleyAbelCoefficient,
    xiExteriorCayleyAbelGreenMultiplier_lineConj_one_eq_neg,
    adjacentCriticalFeatureEvaluationDet_lineConj_eq_neg]
  ring

/-- Every boundary coefficient is purely imaginary. -/
theorem xiFixedAdjacentCayleyAbelCoefficient_one_re_eq_zero
    (t : ℝ) (rho : XiDivisorSupport) :
    (xiFixedAdjacentCayleyAbelCoefficient 1 t rho).re = 0 := by
  by_cases hline : (rho : ℂ).re = 1 / 2
  · rw [xiFixedAdjacentCayleyAbelCoefficient_eq_zero_of_onLine 1 t rho hline]
    simp
  · rw [xiFixedAdjacentCayleyAbelCoefficient,
      xiExteriorCayleyAbelGreenMultiplier_one_eq_inv_im rho hline,
      adjacentCriticalFeatureEvaluationDet_eq_area]
    simp [Complex.mul_re, Complex.mul_im]

/-- For a purely imaginary complex number, minus its square is its real norm square. -/
theorem neg_sq_eq_ofReal_normSq_of_re_eq_zero
    (z : ℂ) (hz : z.re = 0) :
    -z ^ (2 : ℕ) = (Complex.normSq z : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two, hz]

/-- One selected reflected projector term is exactly a positive norm square. -/
theorem xiFixedAdjacent_reflectedProjectorTerm_eq_normSq
    (t : ℝ) (rho : XiDivisorSupport) :
    xiExteriorCayleyAbelGreenMultiplier 1 rho *
        xiExteriorCayleyAbelGreenMultiplier 1 (xiZeroLineConjEquiv rho) *
        (xiFixedCriticalFeatureValue t rho *
            xiFixedCriticalFeatureValue (t + 1) (xiZeroLineConjEquiv rho) -
          xiFixedCriticalFeatureValue t (xiZeroLineConjEquiv rho) *
            xiFixedCriticalFeatureValue (t + 1) rho) ^ (2 : ℕ) =
      (Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 t rho) : ℂ) := by
  rw [xiExteriorCayleyAbelGreenMultiplier_lineConj_one_eq_neg,
    xiFixedCriticalFeaturePluecker_eq_adjacentDet]
  rw [show xiExteriorCayleyAbelGreenMultiplier 1 rho *
        -xiExteriorCayleyAbelGreenMultiplier 1 rho *
        adjacentCriticalFeatureEvaluationDet t (xiSpectralPointSupport rho)
          (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) ^ (2 : ℕ) =
      -(xiFixedAdjacentCayleyAbelCoefficient 1 t rho) ^ (2 : ℕ) by
        rw [xiFixedAdjacentCayleyAbelCoefficient]
        ring]
  exact neg_sq_eq_ofReal_normSq_of_re_eq_zero _
    (xiFixedAdjacentCayleyAbelCoefficient_one_re_eq_zero t rho)

/-- Fixed-feature, Green-normalized oriented determinant at one prime/Cayley clock triple. -/
def xiFixedAdjacentPrimeCayleyExteriorDeterminant
    (S : Finset XiDivisorSupport) (t : ℝ) (a b c : ℕ) : ℂ :=
  xiPrimeCayleyExteriorReflectionDeterminant S
    (xiExteriorCayleyAbelGreenMultiplier 1)
    (xiFixedCriticalFeatureValue t)
    (xiFixedCriticalFeatureValue (t + 1)) a b c

/-- Exact fixed-center divisor landing: triple dephasing is half the sum of positive exterior
norm squares.  Reflection closure counts the two orientations of every free orbit.  Fixed feature
rows have existing prime--Gamma polarizations, but this theorem does not identify the clocked
finite packet with a pre-divisor arithmetic trace. -/
theorem tendsto_xiFixedAdjacentPrimeCayleyExteriorDeterminant
    (S : Finset XiDivisorSupport)
    (hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S) (t : ℝ) :
    Tendsto
      (fun N : ℕ => (((N : ℝ)⁻¹ : ℂ) ^ (3 : ℕ)) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiFixedAdjacentPrimeCayleyExteriorDeterminant S t a b c)
      atTop
      (nhds ((1 / 2 : ℂ) * ∑ rho ∈ S,
        (Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 t rho) : ℂ))) := by
  have hlim := tendsto_xiPrimeCayleyExteriorReflectionDeterminant S hclosed
    (xiExteriorCayleyAbelGreenMultiplier 1)
    (xiFixedCriticalFeatureValue t)
    (xiFixedCriticalFeatureValue (t + 1))
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    congr 1
    apply Finset.sum_congr rfl
    intro rho hrho
    exact (xiFixedAdjacent_reflectedProjectorTerm_eq_normSq t rho).symm

/-- Complete fixed-center two-orientation exterior energy. -/
def xiFixedCenterExteriorEnergy (t : ℝ) (rho : XiDivisorSupport) : ℝ :=
  Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 t rho) +
    Complex.normSq (xiFixedAdjacentCayleyAbelCoefficient 1 (t - 1) rho)

/-- Fixed-center energy is four times the existing transverse adjacent-feature energy. -/
theorem xiFixedCenterExteriorEnergy_eq_transverseEnergy
    (t : ℝ) (rho : XiDivisorSupport) :
    xiFixedCenterExteriorEnergy t rho =
      4 * orientedAdjacentCriticalFeatureTransverseEnergy t
        (xiSpectralPointSupport rho)
        (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) := by
  let z := xiSpectralPointSupport rho
  let hz : |z.im| < 1 / 2 :=
    abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho
  by_cases hline : (rho : ℂ).re = 1 / 2
  · have hy : z.im = 0 := (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
    rw [xiFixedCenterExteriorEnergy,
      xiFixedAdjacentCayleyAbelCoefficient_eq_zero_of_onLine 1 t rho hline,
      xiFixedAdjacentCayleyAbelCoefficient_eq_zero_of_onLine 1 (t - 1) rho hline,
      Complex.normSq_zero, zero_add,
      orientedAdjacentCriticalFeatureTransverseEnergy_eq_zero_of_im_eq_zero t hz hy,
      mul_zero]
  · rw [xiFixedCenterExteriorEnergy,
      xiFixedAdjacentCayleyAbelCoefficient,
      xiFixedAdjacentCayleyAbelCoefficient,
      xiExteriorCayleyAbelGreenMultiplier_one_eq_inv_im rho hline,
      Complex.normSq_mul, Complex.normSq_mul]
    simp only [Complex.normSq_ofReal]
    rw [← mul_add]
    rw [← four_mul_orientedAdjacentCriticalFeatureExteriorEnergy_eq t z hz]
    rw [orientedAdjacentCriticalFeatureTransverseEnergy]
    ring

/-- Uniform off-line quantum for a fixed source center covering the point's height cell. -/
theorem four_mul_transverseQuantum_le_xiFixedCenterExteriorEnergy
    (t : ℝ) (rho : XiDivisorSupport)
    (ht : |(xiSpectralPointSupport rho).re - t| ≤ 1 / 2)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    4 * (96 / 145 : ℝ) ^ (2 : ℕ) ≤ xiFixedCenterExteriorEnergy t rho := by
  have hy : (xiSpectralPointSupport rho).im ≠ 0 :=
    fun h => hoff ((xiSpectralPointSupport_im_eq_zero_iff rho).1 h)
  have hquantum := orientedAdjacentCriticalFeatureTransverseEnergy_ge t
    (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) ht hy
  rw [xiFixedCenterExteriorEnergy_eq_transverseEnergy]
  nlinarith

end

end RHTower
