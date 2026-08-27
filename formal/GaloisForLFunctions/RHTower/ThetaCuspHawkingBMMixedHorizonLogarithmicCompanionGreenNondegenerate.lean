import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonLogarithmicCompanionGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonSturmOpticalForm

/-!
# Nondegeneracy of the mixed BM logarithmic Green basis

On physical mixed parameters, the Gauss exponent balance makes the integrating factor
`sqrt(1-t)/t^N`. The exact regular and principal logarithmic companion jets obey the same
divergence-form equation, so their normalized Wronskian is constant on the radial interior.
Horizon asymptotics fix that constant and exclude every interior conjugate point.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Principal mixed Xi Wronskian in the physical Sturm integrating-factor normalization. -/
def d4BMXiMixedHorizonPrincipalNormalizedWronskian
    (n k : ℕ) (q : XiZeroCopy) (t : ℝ) : ℂ :=
  (d4BMMixedHorizonSturmP n k t : ℂ) *
    (d4HypergeometricResonantRegularBranchValue
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)) t *
        d4BMXiMixedHorizonLogarithmicCompanionFirstDerivative n k q t -
      d4HypergeometricResonantRegularBranchFirstDerivative
          (d4BMMixedHorizonFrobeniusOrder n k)
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)) t *
        d4BMXiMixedHorizonLogarithmicCompanionValue n k q t)

/-- In the regular/logarithmic Wronskian, every explicit logarithm cancels. -/
theorem d4HypergeometricResonantLogarithmicCompanion_wronskian_eq_logFree
    (N : ℕ) (a b z p : ℂ) :
    p *
        (d4HypergeometricResonantRegularBranchValue N a b z *
            d4HypergeometricResonantLogarithmicCompanionFirstDerivative N a b z -
          d4HypergeometricResonantRegularBranchFirstDerivative N a b z *
            d4HypergeometricResonantLogarithmicCompanionValue N a b z) =
      p *
        (d4HypergeometricResonantRegularBranchValue N a b z *
            d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b z -
          d4HypergeometricResonantRegularBranchFirstDerivative N a b z *
            d4HypergeometricResonantCompanionAnalyticValue N a b z +
          d4HypergeometricResonantFrobeniusLogCoefficient N a b *
            d4HypergeometricResonantRegularBranchValue N a b z ^ 2 * z⁻¹) := by
  simp only [d4HypergeometricResonantLogarithmicCompanionValue,
    d4HypergeometricResonantLogarithmicCompanionFirstDerivative,
    Pi.add_apply, Pi.mul_apply]
  ring

/-- Complex Xi mixed Gauss drift is the same universal real Sturm drift. -/
theorem d4BMXiMixedHorizon_hypergeometricDrift_eq
    (n k : ℕ) (q : XiZeroCopy) (t : ℝ) :
    -(d4BMMixedHorizonFrobeniusOrder n k : ℂ) -
        (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q) +
          d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q) + 1) *
          (t : ℂ) =
      (d4BMMixedHorizonSturmDrift n k t : ℂ) := by
  rw [d4BMMixedHorizonComplexA, d4BMMixedHorizonComplexB,
    d4BMCausalHypergeometricA_plusMinus,
    d4BMCausalHypergeometricB_plusMinus]
  simp [d4BMMixedHorizonSturmDrift,
    d4BMMixedHorizonFrobeniusOrder]
  ring

/-- Inside the unit disk, the derivative of the resonant regular branch is the exact
product-rule derivative of its Frobenius factorization. -/
theorem d4HypergeometricResonantRegularBranchFirstDerivative_eq_pow_mul_factor
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    d4HypergeometricResonantRegularBranchFirstDerivative N a b z =
      (((N + 1 : ℕ) : ℂ) * z ^ N *
          (d4HypergeometricResonantRegularFactorSeries N a b).sum z +
        z ^ (N + 1) *
          (((d4HypergeometricResonantRegularFactorSeries N a b).derivSeries.sum z) 1)) := by
  let F := fun w : ℂ =>
    (d4HypergeometricResonantRegularFactorSeries N a b).sum w
  let Fd := fun w : ℂ =>
    (((d4HypergeometricResonantRegularFactorSeries N a b).derivSeries.sum w) 1)
  have hzF : ‖z‖ₑ <
      (d4HypergeometricResonantRegularFactorSeries N a b).radius := by
    rw [d4HypergeometricResonantRegularFactorSeries_radius_eq_one N a b ha hb]
    exact hz
  have hF : HasDerivAt F (Fd z) z := by
    change HasDerivAt
      (d4HypergeometricResonantRegularFactorSeries N a b).sum
      (((d4HypergeometricResonantRegularFactorSeries N a b).derivSeries.sum z) 1) z
    exact ((d4HypergeometricResonantRegularFactorSeries N a b).hasFDerivAt_sum hzF).hasDerivAt
  have hproduct := (hasDerivAt_pow (N + 1) z).mul hF
  have hzmem : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    simpa only [Metric.mem_eball, edist_zero_right] using hz
  have hevent :
      d4HypergeometricResonantRegularBranchValue N a b =ᶠ[𝓝 z]
        (fun w => w ^ (N + 1)) * F := by
    filter_upwards [Metric.isOpen_eball.mem_nhds hzmem] with w hw
    change d4HypergeometricResonantRegularBranchValue N a b w =
      w ^ (N + 1) * F w
    exact d4HypergeometricResonantRegularBranchValue_eq_pow_mul_factor N a b w ha hb
      (by simpa only [Metric.mem_eball, edist_zero_right] using hw)
  have hbranch := hasDerivAt_d4HypergeometricResonantRegularBranchValue
    N a b z ha hb hz
  have hunique := hbranch.unique (hproduct.congr_of_eventuallyEq hevent)
  simpa [F, Fd, Nat.cast_add, Nat.cast_one] using hunique

/-- Shifted regular Gauss factor has the Frobenius normalization `F(0)=1`. -/
theorem d4HypergeometricResonantRegularFactorSeries_sum_zero
    (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) :
    (d4HypergeometricResonantRegularFactorSeries N a b).sum 0 = 1 := by
  have hr : ‖(0 : ℂ)‖ₑ <
      (d4HypergeometricResonantRegularFactorSeries N a b).radius := by
    rw [d4HypergeometricResonantRegularFactorSeries_radius_eq_one N a b ha hb]
    simp
  have hs := (ordinaryHypergeometric_hasSum_value_first_second
    (d4HypergeometricResonantShiftedA N a)
    (d4HypergeometricResonantShiftedA N b)
    (d4HypergeometricResonantShiftedC N) 0 hr).1
  have hz := HasSum.hasSum_at_zero (𝕜 := ℂ)
    (fun j => ordinaryHypergeometricFormalCoefficient
      (d4HypergeometricResonantShiftedA N a)
      (d4HypergeometricResonantShiftedA N b)
      (d4HypergeometricResonantShiftedC N) j)
  have heq := hs.unique (by
    simpa [smul_eq_mul, mul_comm] using hz)
  simpa [d4HypergeometricResonantRegularFactorSeries,
    ordinaryHypergeometricFormalCoefficient,
    ordinaryHypergeometricCoefficient] using heq

/-- Analytic part of the normalized logarithmic companion has horizon value one. -/
theorem d4HypergeometricResonantCompanionAnalyticValue_zero
    (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) :
    d4HypergeometricResonantCompanionAnalyticValue N a b 0 = 1 := by
  have hr : ‖(0 : ℂ)‖ₑ <
      (d4HypergeometricResonantCompanionAnalyticSeries N a b).radius :=
    lt_of_lt_of_le (by simp)
      (d4HypergeometricResonantCompanionAnalyticSeries_radius_ge_one N a b ha hb)
  have hs := (scalarSeries_hasSum_value_first_second
    (d4HypergeometricResonantCompanionAnalyticCoefficient N a b) 0
    (by simpa [d4HypergeometricResonantCompanionAnalyticSeries] using hr)).1
  have hz := HasSum.hasSum_at_zero (𝕜 := ℂ)
    (d4HypergeometricResonantCompanionAnalyticCoefficient N a b)
  have heq := hs.unique (by
    simpa [smul_eq_mul, mul_comm] using hz)
  simpa [d4HypergeometricResonantCompanionAnalyticValue,
    d4HypergeometricResonantCompanionAnalyticSeries,
    d4HypergeometricResonantCompanionAnalyticCoefficient,
    d4HypergeometricResonantTruncationCoefficient,
    ordinaryHypergeometricCoefficient] using heq

/-- Principal normalized regular/companion Wronskian has zero derivative in radial interior. -/
theorem hasDerivAt_d4BMXiMixedHorizonPrincipalNormalizedWronskian
    (n k : ℕ) (q : XiZeroCopy) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q) 0 t := by
  let N := d4BMMixedHorizonFrobeniusOrder n k
  let a := d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q)
  let b := d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)
  let U := fun x : ℝ => d4HypergeometricResonantRegularBranchValue N a b x
  let Ud := fun x : ℝ => d4HypergeometricResonantRegularBranchFirstDerivative N a b x
  let Udd := fun x : ℝ => d4HypergeometricResonantRegularBranchSecondDerivative N a b x
  let Y := fun x : ℝ => d4HypergeometricResonantLogarithmicCompanionValue N a b x
  let Yd := fun x : ℝ => d4HypergeometricResonantLogarithmicCompanionFirstDerivative N a b x
  let Ydd := fun x : ℝ => d4HypergeometricResonantLogarithmicCompanionSecondDerivative N a b x
  let p := d4BMMixedHorizonSturmP n k
  let w := d4BMMixedHorizonSturmWeight n k
  let drift := d4BMMixedHorizonSturmDrift n k
  have ht : ‖(t : ℂ)‖ₑ < 1 := enorm_ofReal_lt_one ht0 ht1
  have htslit : (t : ℂ) ∈ Complex.slitPlane := by
    simpa [Complex.slitPlane] using ht0
  have hpR := hasDerivAt_d4BMMixedHorizonSturmP n k ht0 ht1
  have hp : HasDerivAt (fun x : ℝ => (p x : ℂ))
      ((w t * drift t : ℝ) : ℂ) t := by
    simpa [p, w, drift] using hpR.ofReal_comp
  have hU : HasDerivAt U (Ud t) t := by
    simpa [U, Ud] using
      (hasDerivAt_d4HypergeometricResonantRegularBranchValue
        N a b (t : ℂ)
        (by simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
        (by simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q)
        ht).comp_ofReal
  have hUd : HasDerivAt Ud (Udd t) t := by
    simpa [Ud, Udd] using
      (hasDerivAt_d4HypergeometricResonantRegularBranchFirstDerivative
        N a b (t : ℂ)
        (by simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
        (by simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q)
        ht).comp_ofReal
  have hY : HasDerivAt Y (Yd t) t := by
    simpa [Y, Yd] using
      (hasDerivAt_d4HypergeometricResonantLogarithmicCompanionValue
        N a b (t : ℂ)
        (by simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
        (by simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q)
        ht htslit).comp_ofReal
  have hYd : HasDerivAt Yd (Ydd t) t := by
    simpa [Yd, Ydd] using
      (hasDerivAt_d4HypergeometricResonantLogarithmicCompanionFirstDerivative
        N a b (t : ℂ)
        (by simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
        (by simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q)
        ht htslit).comp_ofReal
  have hUe0 := d4HypergeometricResonantRegularBranch_analyticEulerEquation
    N a b (t : ℂ)
    (by simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
    (by simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q) ht
  have hYe0 := d4HypergeometricResonantLogarithmicCompanion_analyticEulerODE
    N a b (t : ℂ)
    (by simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q)
    (by simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q)
    ht htslit
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hdrift :
      -(N : ℂ) - (a + b + 1) * (t : ℂ) = (drift t : ℂ) := by
    simpa [N, a, b, drift] using
      d4BMXiMixedHorizon_hypergeometricDrift_eq n k q t
  have hUe :
      ((t * (1 - t) : ℝ) : ℂ) * Udd t +
          (drift t : ℂ) * Ud t - a * b * U t = 0 := by
    have hfactor : (t : ℂ) *
        (((t * (1 - t) : ℝ) : ℂ) * Udd t +
          (drift t : ℂ) * Ud t - a * b * U t) = 0 := by
      rw [← hUe0]
      simp [N, a, b, U, Ud, Udd]
      rw [← hdrift]
      ring
    exact (mul_eq_zero.mp hfactor).resolve_left htC
  have hYe :
      ((t * (1 - t) : ℝ) : ℂ) * Ydd t +
          (drift t : ℂ) * Yd t - a * b * Y t = 0 := by
    have hfactor : (t : ℂ) *
        (((t * (1 - t) : ℝ) : ℂ) * Ydd t +
          (drift t : ℂ) * Yd t - a * b * Y t) = 0 := by
      rw [← hYe0]
      simp [N, a, b, Y, Yd, Ydd]
      rw [← hdrift]
      ring
    exact (mul_eq_zero.mp hfactor).resolve_left htC
  have hwpR : w t * (t * (1 - t)) = p t := by
    dsimp [w, p]
    rw [d4BMMixedHorizonSturmWeight]
    field_simp [ne_of_gt ht0, ne_of_gt (sub_pos.mpr ht1)]
  have hwp : (w t : ℂ) * (((t * (1 - t) : ℝ) : ℂ)) = (p t : ℂ) := by
    exact_mod_cast hwpR
  have htprod : (((t * (1 - t) : ℝ) : ℂ)) =
      (t : ℂ) * (1 - (t : ℂ)) := by
    push_cast
    ring
  rw [htprod] at hUe hYe hwp
  have hUdiv :
      ((w t * drift t : ℝ) : ℂ) * Ud t +
          (p t : ℂ) * Udd t - (w t : ℂ) * (a * b) * U t = 0 := by
    rw [← hwp]
    push_cast
    linear_combination (w t : ℂ) * hUe
  have hYdiv :
      ((w t * drift t : ℝ) : ℂ) * Yd t +
          (p t : ℂ) * Ydd t - (w t : ℂ) * (a * b) * Y t = 0 := by
    rw [← hwp]
    push_cast
    linear_combination (w t : ℂ) * hYe
  have hzero :
      ((w t * drift t : ℝ) : ℂ) * (U t * Yd t - Ud t * Y t) +
        (p t : ℂ) *
          ((Ud t * Yd t + U t * Ydd t) -
            (Udd t * Y t + Ud t * Yd t)) = 0 := by
    linear_combination U t * hYdiv - Y t * hUdiv
  have hW := hp.mul ((hU.mul hYd).sub (hUd.mul hY))
  have hW0 := hW.congr_deriv hzero
  simpa [d4BMXiMixedHorizonPrincipalNormalizedWronskian,
    N, a, b, U, Ud, Udd, Y, Yd, Ydd, p, w, drift,
    d4BMXiMixedHorizonLogarithmicCompanionValue,
    d4BMXiMixedHorizonLogarithmicCompanionFirstDerivative] using! hW0

/-- Principal normalized Wronskian is constant on connected radial interior. -/
theorem d4BMXiMixedHorizonPrincipalNormalizedWronskian_eq_of_mem_Ioo
    (n k : ℕ) (q : XiZeroCopy) {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q x =
      d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q y := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro t ht
    exact (hasDerivAt_d4BMXiMixedHorizonPrincipalNormalizedWronskian
      n k q ht.1 ht.2).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hasDerivAt_d4BMXiMixedHorizonPrincipalNormalizedWronskian
      n k q ht.1 ht.2).deriv
  · exact hx
  · exact hy

/-- On the radial interior, the normalized Wronskian has a log-free normal form extending
continuously to the horizon. -/
theorem d4BMXiMixedHorizonPrincipalNormalizedWronskian_eq_horizonNormalForm
    (n k : ℕ) (q : XiZeroCopy) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    let N := d4BMMixedHorizonFrobeniusOrder n k
    let a := d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q)
    let b := d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)
    let F := fun z : ℂ => (d4HypergeometricResonantRegularFactorSeries N a b).sum z
    let Fd := fun z : ℂ =>
      (((d4HypergeometricResonantRegularFactorSeries N a b).derivSeries.sum z) 1)
    let H := d4HypergeometricResonantCompanionAnalyticValue N a b
    let Hd := d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b
    let C := d4HypergeometricResonantFrobeniusLogCoefficient N a b
    d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q t =
      (Real.sqrt (1 - t) : ℂ) *
        ((t : ℂ) * F t * Hd t -
          ((((N + 1 : ℕ) : ℂ) * F t + (t : ℂ) * Fd t) * H t) +
          C * (t : ℂ) ^ (N + 1) * F t ^ 2) := by
  dsimp only
  let N := d4BMMixedHorizonFrobeniusOrder n k
  let a := d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q)
  let b := d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)
  have ha : 0 < (d4HypergeometricResonantShiftedA N a).re := by
    simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q
  have hb : 0 < (d4HypergeometricResonantShiftedA N b).re := by
    simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q
  have ht : ‖(t : ℂ)‖ₑ < 1 := enorm_ofReal_lt_one ht0 ht1
  rw [d4BMXiMixedHorizonPrincipalNormalizedWronskian]
  simp only [d4BMXiMixedHorizonLogarithmicCompanionValue,
    d4BMXiMixedHorizonLogarithmicCompanionFirstDerivative]
  rw [d4HypergeometricResonantLogarithmicCompanion_wronskian_eq_logFree]
  rw [d4HypergeometricResonantRegularBranchValue_eq_pow_mul_factor N a b
      (t : ℂ) ha hb ht,
    d4HypergeometricResonantRegularBranchFirstDerivative_eq_pow_mul_factor
      N a b (t : ℂ) ha hb ht]
  rw [d4BMMixedHorizonSturmP]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  push_cast
  field_simp [htC]
  ring

/-- The horizon normalization fixes the constant Wronskian to `-(N+1)`. -/
theorem tendsto_d4BMXiMixedHorizonPrincipalNormalizedWronskian_nhdsGT_zero
    (n k : ℕ) (q : XiZeroCopy) :
    Tendsto (d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q)
      (𝓝[>] 0)
      (𝓝 (-((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℂ))) := by
  let N := d4BMMixedHorizonFrobeniusOrder n k
  let a := d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q)
  let b := d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q)
  let F := fun z : ℂ => (d4HypergeometricResonantRegularFactorSeries N a b).sum z
  let Fd := fun z : ℂ =>
    (((d4HypergeometricResonantRegularFactorSeries N a b).derivSeries.sum z) 1)
  let H := d4HypergeometricResonantCompanionAnalyticValue N a b
  let Hd := d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b
  let C := d4HypergeometricResonantFrobeniusLogCoefficient N a b
  let G := fun t : ℝ =>
    (Real.sqrt (1 - t) : ℂ) *
      ((t : ℂ) * F t * Hd t -
        ((((N + 1 : ℕ) : ℂ) * F t + (t : ℂ) * Fd t) * H t) +
        C * (t : ℂ) ^ (N + 1) * F t ^ 2)
  have ha : 0 < (d4HypergeometricResonantShiftedA N a).re := by
    simpa [N, a] using d4BMXiMixedHorizonResonantShiftedA_re_pos n k q
  have hb : 0 < (d4HypergeometricResonantShiftedA N b).re := by
    simpa [N, b] using d4BMXiMixedHorizonResonantShiftedB_re_pos n k q
  have hF0 : F 0 = 1 := by
    simpa [F] using d4HypergeometricResonantRegularFactorSeries_sum_zero N a b ha hb
  have hH0 : H 0 = 1 := by
    simpa [H] using d4HypergeometricResonantCompanionAnalyticValue_zero N a b ha hb
  have hFcontC : ContinuousAt F 0 := by
    have hr : ‖(0 : ℂ)‖ₑ <
        (d4HypergeometricResonantRegularFactorSeries N a b).radius := by
      rw [d4HypergeometricResonantRegularFactorSeries_radius_eq_one N a b ha hb]
      simp
    exact ((d4HypergeometricResonantRegularFactorSeries N a b).hasFDerivAt_sum hr).continuousAt
  have hFdcontC : ContinuousAt Fd 0 := by
    let p := d4HypergeometricResonantRegularFactorSeries N a b
    let d := p.derivSeries
    have hp : ‖(0 : ℂ)‖ₑ < p.radius := by
      dsimp [p]
      rw [d4HypergeometricResonantRegularFactorSeries_radius_eq_one N a b ha hb]
      simp
    have hd : ‖(0 : ℂ)‖ₑ < d.radius :=
      lt_of_lt_of_le hp p.radius_le_radius_derivSeries
    have hderiv := d.hasFDerivAt_sum hd
    have heval := hderiv.clm_apply (hasFDerivAt_const (1 : ℂ) (0 : ℂ))
    simpa [Fd, p, d] using heval.continuousAt
  have hHcontC : ContinuousAt H 0 := by
    simpa [H] using
      (hasDerivAt_d4HypergeometricResonantCompanionAnalyticValue
        N a b 0 ha hb (by simp)).continuousAt
  have hHdcontC : ContinuousAt Hd 0 := by
    simpa [Hd] using
      (hasDerivAt_d4HypergeometricResonantCompanionAnalyticFirstDerivative
        N a b 0 ha hb (by simp)).continuousAt
  have hcoe : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt
  have hFcont : ContinuousAt (fun t : ℝ => F t) 0 :=
    by simpa only [Function.comp_def] using
      hFcontC.comp_of_eq hcoe (by norm_num : ((0 : ℝ) : ℂ) = 0)
  have hFdcont : ContinuousAt (fun t : ℝ => Fd t) 0 :=
    by simpa only [Function.comp_def] using
      hFdcontC.comp_of_eq hcoe (by norm_num : ((0 : ℝ) : ℂ) = 0)
  have hHcont : ContinuousAt (fun t : ℝ => H t) 0 :=
    by simpa only [Function.comp_def] using
      hHcontC.comp_of_eq hcoe (by norm_num : ((0 : ℝ) : ℂ) = 0)
  have hHdcont : ContinuousAt (fun t : ℝ => Hd t) 0 :=
    by simpa only [Function.comp_def] using
      hHdcontC.comp_of_eq hcoe (by norm_num : ((0 : ℝ) : ℂ) = 0)
  have hsqrtR : ContinuousAt (fun t : ℝ => Real.sqrt (1 - t)) 0 :=
    Real.continuous_sqrt.continuousAt.comp (continuousAt_const.sub continuousAt_id)
  have hsqrt : ContinuousAt (fun t : ℝ => (Real.sqrt (1 - t) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp hsqrtR
  have hGcont : ContinuousAt G 0 := by
    dsimp only [G]
    exact hsqrt.mul
      (((hcoe.mul hFcont).mul hHdcont).sub
        (((continuousAt_const.mul hFcont).add (hcoe.mul hFdcont)).mul hHcont) |>.add
        ((continuousAt_const.mul (hcoe.pow (N + 1))).mul (hFcont.pow 2)))
  have hG0 : G 0 = -(((N + 1 : ℕ) : ℂ)) := by
    simp [G, hF0, hH0]
  have hGt : Tendsto G (𝓝[>] 0) (𝓝 (-(((N + 1 : ℕ) : ℂ)))) := by
    rw [← hG0]
    exact hGcont.continuousWithinAt
  have hevent :
      d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q =ᶠ[𝓝[>] 0] G := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    simpa [G, N, a, b, F, Fd, H, Hd, C] using
      (d4BMXiMixedHorizonPrincipalNormalizedWronskian_eq_horizonNormalForm
        n k q ht.1 ht.2)
  simpa [N] using hGt.congr' hevent.symm

/-- Exact Abel constant of the physical principal regular/logarithmic Wronskian. -/
theorem d4BMXiMixedHorizonPrincipalNormalizedWronskian_eq_neg_order_add_one
    (n k : ℕ) (q : XiZeroCopy) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q t =
      -((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℂ) := by
  have hevent :
      d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q =ᶠ[𝓝[>] 0]
        fun _ => d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact d4BMXiMixedHorizonPrincipalNormalizedWronskian_eq_of_mem_Ioo
      n k q hx ⟨ht0, ht1⟩
  have hconstant :
      Tendsto (d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q)
        (𝓝[>] 0)
        (𝓝 (d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q t)) :=
    tendsto_const_nhds.congr' hevent.symm
  exact tendsto_nhds_unique hconstant
    (tendsto_d4BMXiMixedHorizonPrincipalNormalizedWronskian_nhdsGT_zero n k q)

/-- Principal-sheet Green denominator is the leading coefficient divided by the Sturm
integrating factor, times the normalized Wronskian. -/
theorem d4BMXiMixedHorizonPrincipalEndpointGreenDenominator_eq_normalizedWronskian
    (n k : ℕ) (q : XiZeroCopy) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet
        (d4BMMixedHorizonFrobeniusOrder n k)
        (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
        (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
        Complex.log (t : ℂ) =
      (((t * (1 - t) : ℝ) : ℂ) /
          (d4BMMixedHorizonSturmP n k t : ℂ)) *
        d4BMXiMixedHorizonPrincipalNormalizedWronskian n k q t := by
  have hpR : d4BMMixedHorizonSturmP n k t ≠ 0 :=
    ne_of_gt (d4BMMixedHorizonSturmP_pos_and_weight_pos n k ht0 ht1).1
  have hpC : (d4BMMixedHorizonSturmP n k t : ℂ) ≠ 0 := by exact_mod_cast hpR
  unfold d4HypergeometricResonantEndpointGreenDenominatorOnSheet
  rw [d4BMXiMixedHorizonPrincipalNormalizedWronskian]
  simp only [d4BMXiMixedHorizonLogarithmicCompanionValue,
    d4BMXiMixedHorizonLogarithmicCompanionFirstDerivative,
    d4HypergeometricResonantLogarithmicCompanionOnSheet,
    d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet,
    d4HypergeometricResonantLogarithmicCompanionValue,
    d4HypergeometricResonantLogarithmicCompanionFirstDerivative,
    Pi.add_apply, Pi.mul_apply]
  push_cast
  field_simp [hpC]

/-- Physical principal Green denominator never vanishes in the radial interior. -/
theorem d4BMXiMixedHorizonPrincipalEndpointGreenDenominator_ne_zero
    (n k : ℕ) (q : XiZeroCopy) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet
        (d4BMMixedHorizonFrobeniusOrder n k)
        (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
        (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
        Complex.log (t : ℂ) ≠ 0 := by
  rw [d4BMXiMixedHorizonPrincipalEndpointGreenDenominator_eq_normalizedWronskian
    n k q ht0 ht1,
    d4BMXiMixedHorizonPrincipalNormalizedWronskian_eq_neg_order_add_one
      n k q ht0 ht1]
  apply mul_ne_zero
  · apply div_ne_zero
    · exact_mod_cast mul_ne_zero (ne_of_gt ht0) (ne_of_gt (sub_pos.mpr ht1))
    · exact_mod_cast
        ne_of_gt (d4BMMixedHorizonSturmP_pos_and_weight_pos n k ht0 ht1).1
  · intro hzero
    have hre := congrArg Complex.re hzero
    have hN : 0 ≤ (d4BMMixedHorizonFrobeniusOrder n k : ℝ) := Nat.cast_nonneg _
    norm_num at hre
    linarith

/-- Actual Xi principal-sheet endpoint Green kernel has unit diagonal derivative jump without a
nondegeneracy premise. -/
theorem d4BMXiMixedHorizonPrincipalEndpointGreenKernel_derivativeJump_diagonal
    (n k : ℕ) (q : XiZeroCopy) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (t : ℂ) * (1 - (t : ℂ)) *
        (d4HypergeometricResonantRightEndpointGreenKernelFirstDerivativeOnSheet
            (d4BMMixedHorizonFrobeniusOrder n k)
            (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
            (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
            Complex.log (t : ℂ) (t : ℂ) -
          d4HypergeometricResonantLeftEndpointGreenKernelFirstDerivativeOnSheet
            (d4BMMixedHorizonFrobeniusOrder n k)
            (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
            (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
            Complex.log (t : ℂ) (t : ℂ)) = 1 := by
  exact d4HypergeometricResonantEndpointGreenKernel_derivativeJump_diagonal
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
    Complex.log (t : ℂ)
    (d4BMXiMixedHorizonPrincipalEndpointGreenDenominator_ne_zero
      n k q ht0 ht1)

end

end RHTower
