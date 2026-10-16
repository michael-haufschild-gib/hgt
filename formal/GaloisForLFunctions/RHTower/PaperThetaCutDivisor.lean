import GaloisForLFunctions.RHTower.PaperThetaCutSourceEquation
import GaloisForLFunctions.RHTower.XiHedenmalmThetaJetSource

/-! # Divisor-faithful compact theta currents at every complex parameter

The movable interior charge has the full analytic Xi multiplicity at every
Xi point. The construction therefore admits all parameters in the literal
BV space without losing the divisor in the passage through the singular
quantile coordinate. No confinement or sign premise is used.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped SchwartzMap

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem differentiable_cutCharge (a : ℝ) : Differentiable ℂ (fun z => cutCharge z a) := by
  simp_rw [cutCharge_eq]
  exact ((((differentiable_const I).mul differentiable_id).neg.mul XiC_differentiable).mul
    (Complex.differentiable_exp.comp (by fun_prop))).div_const _

/-- Finite cut gauges cannot change any nonzero spectral multiplicity. -/
theorem analyticOrderAt_cutCharge {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    analyticOrderAt (fun w => cutCharge w a) z = analyticOrderAt XiC z := by
  let g : ℂ → ℂ := fun w =>
    -(I*w) * Complex.exp (-(I*w)*(a : ℂ)) / (thetaSource.k a : ℂ)
  have hg : AnalyticAt ℂ g z := by
    dsimp [g]
    fun_prop
  have hg0 : g z ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero I_ne_zero hz))
      (Complex.exp_ne_zero _)) (by exact_mod_cast (thetaSource.pos_k a).ne')
  have he : (fun w => cutCharge w a) = g * XiC := by
    funext w
    rw [cutCharge_eq]
    dsimp [g]
    ring
  rw [he, analyticOrderAt_mul hg (XiC_differentiable.analyticAt z),
    hg.analyticOrderAt_eq_zero.mpr hg0, zero_add]

/-- The actual interior current retains every Xi multiplicity, including repeated zeros. -/
theorem analyticOrderAt_cutCharge_support (rho : XiDivisorSupport) (a : ℝ) :
    analyticOrderAt (fun z => cutCharge z a) (xiSpectralPointSupport rho) =
      (xiSupportMultiplicity rho : ℕ∞) := by
  have hz : xiSpectralPointSupport rho ≠ 0 := by
    intro hzero
    have h := XiC_xiSpectralPoint_eq_zero
      (⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ : XiZeroCopy)
    change XiC (xiSpectralPointSupport rho) = 0 at h
    exact XiC_zero_ne (hzero ▸ h)
  rw [analyticOrderAt_cutCharge hz, XiC_analyticOrderAt_support]
  rfl

/-- Unconditional construction of the compact BV parametrix and its complete weak current. -/
theorem thetaCutParametrix_current (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    BoundedVariationOn (cutQuantileMode z c) (Icc (0 : ℝ) 1) ∧
    IntervalIntegrable (cutSourceDensity z c) volume 0 1 ∧
    cutQuantileMode z c 0 = -1 ∧ cutQuantileMode z c 1 = -1 ∧
    ∀ φ : 𝓢(ℝ, ℂ),
      (∫ t in (0 : ℝ)..1, cutQuantileMode z c t * deriv φ t) =
        φ 0 - φ 1 - (∫ t in (0 : ℝ)..1, cutSourceDensity z c t * φ t) -
          (-(I*z)*XiC z*Complex.exp (-(I*z)*(thetaSource.quantileFun c.val : ℂ)) /
            (thetaSource.k (thetaSource.quantileFun c.val) : ℂ)) * φ c.val := by
  refine ⟨boundedVariationOn_cutQuantileMode z c,
    intervalIntegrable_cutSourceDensity z c,
    (cutQuantileMode_endpoints z c).1, (cutQuantileMode_endpoints z c).2, ?_⟩
  intro φ
  rw [cutQuantileMode_source_current, cutCharge_eq]

end RHTower.PaperThetaEndpoint
