import GaloisForLFunctions.RHTower.HedenmalmThetaSourceCompressedInverseDeterminant
import GaloisForLFunctions.RHTower.HedenmalmThetaSeriesExpansion
import GaloisForLFunctions.RHTower.XiFirstDividedSourceNumericalSector

/-!
# Prime-translation anomaly and exact Jordan multiplicity

This module closes the sole dependency left open by the prime-translation card: it identifies the
full algebraic size of each source-inverse root space with the analytic Xi multiplicity.  It also
records the literal positive-integer semigroup law for the normalized translations.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmPrimeTranslation

open HedenmalmQuantile

/-! ## The literal ordinary-integer action -/

/-- The normalized shifts form the ordinary positive-integer multiplicative action
`T_m T_n = T_(mn)`. -/
theorem integerShift_mul (f : ℝ → ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    integerShift (m * n) f = integerShift m (integerShift n f) := by
  funext x
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hmR.ne' hnR.ne']
  have hrpow : (((m * n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Nat.cast_mul, Real.mul_rpow hmR.le hnR.le]
  rw [integerShift, integerShift, integerShift, hlog, hrpow]
  push_cast
  ring_nf

/-! ## Exact analytic and algebraic multiplicity -/

end HedenmalmPrimeTranslation

namespace HedenmalmThetaSource

open Module.End

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Multiplication by the nonzero normalization `XiC(0)^{-1}` does not change local analytic
order, so the source determinant and `XiC` have exactly the same local divisor. -/
theorem analyticOrderAt_thetaSourceEntireDet2_eq_XiC (z : ℂ) :
    analyticOrderAt thetaSourceEntireDet2 z = analyticOrderAt XiC z := by
  have hfun : thetaSourceEntireDet2 =
      (fun w : ℂ ↦ (XiC 0)⁻¹ * XiC w) := by
    funext w
    rw [thetaSourceEntireDet2_eq_XiC_normalized]
    exact div_eq_inv_mul (XiC w) (XiC 0)
  rw [hfun]
  change analyticOrderAt ((fun _ : ℂ ↦ (XiC 0)⁻¹) * XiC) z = _
  rw [analyticOrderAt_mul (analyticAt_const) (XiC_analytic z (Set.mem_univ z))]
  have hconst : analyticOrderAt (fun _ : ℂ ↦ (XiC 0)⁻¹) z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero XiC_zero_ne))
  rw [hconst, zero_add]

/-- **Exact Xi/source-operator multiplicity law.**  At every centered Xi zero, analytic order is
the finrank of the full generalized eigenspace of the source inverse at `-z⁻¹`. -/
theorem analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_thetaKernelOperator
    {z : ℂ} (hXi : XiC z = 0) :
    analyticOrderAt XiC z =
      (Module.finrank ℂ (maxGenEigenspace
        (thetaKernelOperator : Module.End ℂ ThetaH) (-z⁻¹)) : ℕ∞) := by
  have hdet : thetaSourceEntireDet2 z = 0 :=
    (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero z).2 hXi
  rw [← analyticOrderAt_thetaSourceEntireDet2_eq_XiC z]
  exact analyticOrderAt_thetaSourceEntireDet2_eq_algebraicMultiplicity hdet

/-- At a divisor support, the generalized source eigenspace retains every Xi multiplicity copy. -/
theorem finrank_maxGenEigenspace_thetaKernelOperator_eq_xiSupportMultiplicity
    (rho : XiDivisorSupport) :
    Module.finrank ℂ (maxGenEigenspace
      (thetaKernelOperator : Module.End ℂ ThetaH)
        (-(xiSpectralPointSupport rho)⁻¹)) = xiSupportMultiplicity rho := by
  have hXi : XiC (xiSpectralPointSupport rho) = 0 :=
    XiC_xiSpectralPointSupport_eq_zero rho
  have halg :=
    analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_thetaKernelOperator hXi
  have horder := XiC_analyticOrderAt_support rho
  have hcast :
      (Module.finrank ℂ (maxGenEigenspace
        (thetaKernelOperator : Module.End ℂ ThetaH)
          (-(xiSpectralPointSupport rho)⁻¹)) : ℕ∞) =
        (xiSupportMultiplicity rho : ℕ∞) := halg.symm.trans horder
  exact ENat.coe_inj.mp hcast

/-- The source-equation uniqueness used for geometric multiplicity one, specialized to the actual
theta source and paired with the exact algebraic multiplicity. -/
theorem thetaSource_geometricUniqueness_and_fullAlgebraicMultiplicity
    (rho : XiDivisorSupport) :
    (∀ {c : ℂ} {u v u' v' : ℝ → ℂ},
      (∀ x, HasDerivAt u (u' x) x) →
      (∀ x, HasDerivAt v (v' x) x) →
      (∀ x, -Complex.I * u' x + xiSpectralPointSupport rho * u x =
        c * (thetaSource.k x : ℂ)) →
      (∀ x, -Complex.I * v' x + xiSpectralPointSupport rho * v x =
        c * (thetaSource.k x : ℂ)) →
      Tendsto (fun x => (u x - v x) *
        HedenmalmQuantile.sourceChar (xiSpectralPointSupport rho) x) atBot (nhds 0) →
      ∀ x, u x = v x) ∧
    Module.finrank ℂ (maxGenEigenspace
      (thetaKernelOperator : Module.End ℂ ThetaH)
        (-(xiSpectralPointSupport rho)⁻¹)) = xiSupportMultiplicity rho := by
  constructor
  · intro c u v u' v' hu hv heu hev hbot
    exact HedenmalmPrimeTranslation.eq_of_sourceEquation thetaSource
      hu hv heu hev hbot
  · exact finrank_maxGenEigenspace_thetaKernelOperator_eq_xiSupportMultiplicity rho

end HedenmalmThetaSource

end

end RHTower
