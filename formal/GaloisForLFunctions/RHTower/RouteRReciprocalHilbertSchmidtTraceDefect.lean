import GaloisForLFunctions.RHTower.XiGlobalReflectionDefectEnergy
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm

/-!
# Route R's complete reciprocal Hilbert--Schmidt trace defect

The canonical reciprocal Xi divisor operator `T` has two quadratic traces.  Its positive trace is
the complete Hermitian reciprocal mass, while its holomorphic trace is the central reciprocal
moment read from the prime--Gamma source.  This file places both values on the same operator and
proves

`mass - source = (1/2) * ‖T - T†‖_HS²`.

It also identifies the source value exactly with `-XiC''(0) / XiC(0)` and expands the defect as the
sum of the explicit zero-height terms `2 Im(α)² / ‖α‖⁴`.  Thus equality of the two traces,
vanishing of the skew Hilbert--Schmidt norm, self-adjointness, and RH are the same endpoint.

These are target/source identifications, not an annihilation theorem.  The remaining Route R
producer must prove the reverse mass inequality from pre-divisor source structure.
-/

open Complex
open scoped ComplexInnerProductSpace

namespace RHTower

noncomputable section

/-- The holomorphic reciprocal-square trace is the exact centered Xi second-logarithmic-derivative
value. -/
theorem xiCentralReciprocalMoment_zero_eq_neg_XiC_secondDeriv_div :
    xiCentralReciprocalMoment 0 = -deriv (deriv XiC) 0 / XiC 0 := by
  have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 0
  rw [analyticTraceMoments_normalizedPrimeArchSource_zero_eq_Xi_ratio] at hsource
  rw [← hsource]
  have h2 : deriv (deriv XiC) 0 = ((deriv (deriv Xi) 0 : ℝ) : ℂ) := by
    simpa using XiC_secondDeriv_ofReal 0
  have h0 : XiC 0 = ((Xi 0 : ℝ) : ℂ) := by
    simpa using XiC_ofReal 0
  rw [h2, h0]
  push_cast
  rfl

private lemma norm_inv_sq_sub_re_inv_sq (a : ℂ) :
    ‖a⁻¹‖ ^ (2 : ℕ) - (a⁻¹ ^ (2 : ℕ)).re = 2 * a.im ^ (2 : ℕ) / ‖a‖ ^ (4 : ℕ) := by
  have hbase (z : ℂ) : ‖z‖ ^ (2 : ℕ) - (z ^ (2 : ℕ)).re = 2 * z.im ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [pow_two, Complex.mul_re]
    ring
  rw [hbase, Complex.inv_im, div_pow]
  have hnorm : ‖a‖ ^ (4 : ℕ) = Complex.normSq a ^ (2 : ℕ) := by
    calc
      ‖a‖ ^ (4 : ℕ) = (‖a‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = Complex.normSq a ^ (2 : ℕ) := by rw [Complex.sq_norm]
  rw [hnorm]
  ring

/-- Kernel of the skew part `T - T†` of the reciprocal divisor operator. -/
def xiReciprocalSkewKernel : XiZeroCopy × XiZeroCopy → ℂ :=
  xiReciprocalDiagonalKernel -
    HilbertSchmidt.hsAdjoint xiReciprocalDiagonalKernel

theorem xiReciprocalSkewKernel_eq_diagMul :
    xiReciprocalSkewKernel = HilbertSchmidt.diagMul (fun q =>
      xiReciprocalCoordinate q - (starRingEnd ℂ) (xiReciprocalCoordinate q)) := by
  funext p
  rcases p with ⟨q, r⟩
  by_cases hqr : q = r
  · subst r
    simp [xiReciprocalSkewKernel, xiReciprocalDiagonalKernel, xiReciprocalCoordinate,
      HilbertSchmidt.hsAdjoint, HilbertSchmidt.diagMul]
  · have hrq : r ≠ q := Ne.symm hqr
    simp [xiReciprocalSkewKernel, xiReciprocalDiagonalKernel,
      HilbertSchmidt.hsAdjoint, HilbertSchmidt.diagMul, hqr, hrq]

theorem isHS_xiReciprocalSkewKernel : HilbertSchmidt.IsHS xiReciprocalSkewKernel :=
  HilbertSchmidt.isHS_sub isHS_xiReciprocalDiagonalKernel
    (HilbertSchmidt.isHS_hsAdjoint isHS_xiReciprocalDiagonalKernel)

/-- Kernel Hilbert--Schmidt energy of the skew part is the global reflection-defect energy. -/
theorem hsNormSq_xiReciprocalSkewKernel :
    HilbertSchmidt.hsNormSq xiReciprocalSkewKernel =
      xiGlobalReflectionDefectEnergy := by
  rw [xiReciprocalSkewKernel_eq_diagMul,
    HilbertSchmidt.hsNormSq_diagMul_infinite, xiGlobalReflectionDefectEnergy]

/-- The kernel skew part represents the literal operator difference `T - T†`. -/
theorem xiReciprocalOperator_sub_adjoint_eq_toOperator_skewKernel :
    xiReciprocalOperator - ContinuousLinearMap.adjoint xiReciprocalOperator =
      HilbertSchmidt.toOperator isHS_xiReciprocalSkewKernel := by
  rw [xiReciprocalOperator,
    HilbertSchmidt.adjoint_toOperator isHS_xiReciprocalDiagonalKernel]
  exact HilbertSchmidt.toOperator_sub isHS_xiReciprocalDiagonalKernel
    (HilbertSchmidt.isHS_hsAdjoint isHS_xiReciprocalDiagonalKernel)

/-- Operator Hilbert--Schmidt energy of `T - T†` is the complete reflection defect. -/
theorem hsNormSq_xiReciprocalOperator_sub_adjoint :
    ContinuousLinearMap.hsNormSq
        (xiReciprocalOperator - ContinuousLinearMap.adjoint xiReciprocalOperator) =
      xiGlobalReflectionDefectEnergy := by
  rw [xiReciprocalOperator_sub_adjoint_eq_toOperator_skewKernel,
    HilbertSchmidt.hsNormSq_toOperator isHS_xiReciprocalSkewKernel,
    hsNormSq_xiReciprocalSkewKernel]

/-- Hermitian reciprocal mass is exactly the Hilbert--Schmidt mass of the canonical operator. -/
theorem xiReciprocalHermitianMass_eq_operator_hsNormSq :
    xiReciprocalHermitianMass =
      ContinuousLinearMap.hsNormSq xiReciprocalOperator := by
  rw [xiReciprocalOperator,
    HilbertSchmidt.hsNormSq_toOperator isHS_xiReciprocalDiagonalKernel,
    xiReciprocalHermitianMass, xiReciprocalDiagonalKernel,
    HilbertSchmidt.hsNormSq_diagMul_infinite]
  rfl

/-- Positive operator trace `Tr(T†T)` is the Hermitian reciprocal mass. -/
theorem opTrace_adjoint_comp_xiReciprocalOperator :
    ContinuousLinearMap.opTrace
        (ContinuousLinearMap.adjoint xiReciprocalOperator ∘L xiReciprocalOperator) =
      (xiReciprocalHermitianMass : ℂ) := by
  calc
    ContinuousLinearMap.opTrace
        (ContinuousLinearMap.adjoint xiReciprocalOperator ∘L xiReciprocalOperator) =
        ContinuousLinearMap.hsInner xiReciprocalOperator xiReciprocalOperator :=
      ContinuousLinearMap.opTrace_adjoint_comp_self xiReciprocalOperator
    _ = (ContinuousLinearMap.hsNormSq xiReciprocalOperator : ℂ) :=
      HTGeometry.hsInner_self_eq_ofReal_hsNormSq
        (HilbertSchmidt.isHilbertSchmidt_toOperator isHS_xiReciprocalDiagonalKernel)
    _ = (xiReciprocalHermitianMass : ℂ) := by
      rw [xiReciprocalHermitianMass_eq_operator_hsNormSq]

/-- Holomorphic operator trace `Tr(T²)` is the central reciprocal moment. -/
theorem opTrace_sq_xiReciprocalOperator :
    ContinuousLinearMap.opTrace (xiReciprocalOperator ∘L xiReciprocalOperator) =
      xiCentralReciprocalMoment 0 := by
  rw [xiReciprocalOperator,
    HilbertSchmidt.opTrace_toOperator_comp isHS_xiReciprocalDiagonalKernel
      isHS_xiReciprocalDiagonalKernel]
  rw [← tsum_xiZeroCopyReciprocalSquare_pow 0]
  apply tsum_congr
  intro q
  simp [HilbertSchmidt.hsComp, xiReciprocalDiagonalKernel,
    HilbertSchmidt.diagMul, xiZeroCopyReciprocalSquare]
  rw [← inv_pow]
  rw [pow_two]

/-- Exact scalar defect expanded on the original centered Xi coordinates. -/
theorem xiReciprocalHermitianMass_sub_moment_eq_heightEnergy :
    xiReciprocalHermitianMass - (xiCentralReciprocalMoment 0).re =
      ∑' q : XiZeroCopy,
        2 * (xiSpectralPoint q).im ^ (2 : ℕ) / ‖xiSpectralPoint q‖ ^ (4 : ℕ) := by
  have hH : Summable (fun q : XiZeroCopy => ‖xiReciprocalCoordinate q‖ ^ (2 : ℕ)) := by
    simpa [xiReciprocalCoordinate] using summable_norm_xiSpectralPoint_inv_sq
  have hC : Summable (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q) :=
    summable_xiZeroCopyReciprocalSquare
  have hCre : Summable (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q).re) :=
    hC.mapL Complex.reCLM
  calc
    xiReciprocalHermitianMass - (xiCentralReciprocalMoment 0).re =
        (∑' q : XiZeroCopy, ‖xiReciprocalCoordinate q‖ ^ (2 : ℕ)) -
          ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).re := by
      rw [xiReciprocalHermitianMass, ← Complex.re_tsum hC,
        show (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q) =
            xiCentralReciprocalMoment 0 by
          simpa using tsum_xiZeroCopyReciprocalSquare_pow 0]
    _ = ∑' q : XiZeroCopy,
        (‖xiReciprocalCoordinate q‖ ^ (2 : ℕ) - (xiZeroCopyReciprocalSquare q).re) := by
      rw [hH.tsum_sub hCre]
    _ = ∑' q : XiZeroCopy,
        2 * (xiSpectralPoint q).im ^ (2 : ℕ) / ‖xiSpectralPoint q‖ ^ (4 : ℕ) := by
      apply tsum_congr
      intro q
      simpa [xiReciprocalCoordinate, xiZeroCopyReciprocalSquare] using
        norm_inv_sq_sub_re_inv_sq (xiSpectralPoint q)

/-- **Route R C30 operator normal form.**  Hermitian minus holomorphic source trace is half the
squared Hilbert--Schmidt norm of `T - T†`. -/
theorem xiReciprocalHermitianMass_sub_source_eq_half_hsNormSq_skew :
    xiReciprocalHermitianMass - primeArchCentralCurvature =
      (1 / 2 : ℝ) * ContinuousLinearMap.hsNormSq
        (xiReciprocalOperator - ContinuousLinearMap.adjoint xiReciprocalOperator) := by
  rw [hsNormSq_xiReciprocalOperator_sub_adjoint,
    xiGlobalReflectionDefectEnergy_eq_mass_sub_source]
  ring

/-- Vanishing of the one canonical skew Hilbert--Schmidt defect is exactly RH. -/
theorem hsNormSq_xiReciprocalOperator_sub_adjoint_eq_zero_iff_rh :
    ContinuousLinearMap.hsNormSq
        (xiReciprocalOperator - ContinuousLinearMap.adjoint xiReciprocalOperator) = 0 ↔
      RiemannHypothesis := by
  rw [hsNormSq_xiReciprocalOperator_sub_adjoint,
    xiGlobalReflectionDefectEnergy_eq_zero_iff_rh]

/-- Equality of positive and holomorphic operator traces is exactly RH. -/
theorem xiReciprocalHermitianMass_complex_eq_moment_iff_rh :
    (xiReciprocalHermitianMass : ℂ) = xiCentralReciprocalMoment 0 ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply xiReciprocalHermitianMass_eq_primeArchCentralCurvature_iff_rh.mp
    rw [primeArchCentralCurvature_eq_moment_re]
    simpa using congrArg Complex.re h
  · intro hRH
    have hreal := xiReciprocalHermitianMass_eq_primeArchCentralCurvature_iff_rh.mpr hRH
    rw [primeArchCentralCurvature_eq_moment_re] at hreal
    apply Complex.ext
    · simpa using hreal
    · simp [xiCentralReciprocalMoment_im_eq_zero]

/-- Exact completed-Xi scalar endpoint: the Hermitian mass equals `-XiC''(0)/XiC(0)` precisely
under RH. -/
theorem xiReciprocalHermitianMass_complex_eq_XiC_ratio_iff_rh :
    (xiReciprocalHermitianMass : ℂ) =
        -deriv (deriv XiC) 0 / XiC 0 ↔ RiemannHypothesis := by
  rw [← xiCentralReciprocalMoment_zero_eq_neg_XiC_secondDeriv_div]
  exact xiReciprocalHermitianMass_complex_eq_moment_iff_rh

end
end RHTower
