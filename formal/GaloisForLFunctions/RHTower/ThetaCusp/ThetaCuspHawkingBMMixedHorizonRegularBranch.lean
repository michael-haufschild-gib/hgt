import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicRegularSolution
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonUnitWronskianMonodromy

/-!
# Exact regular branch at the resonant mixed BM horizon

At the mixed Birmingham--Mokhtari frequency, the original hypergeometric parameter is
`c = -N`. The analytic exponent-zero series is obstructed at order `N`, but the second
Frobenius branch is an honest convergent Gauss solution:

`u(z) = z^(N+1) ₂F₁(a+N+1, b+N+1; N+2; z)`.

This module constructs that branch, proves two actual derivatives and the literal mixed BM
radial equation, and verifies its leading horizon normalization. The parameters `a,b` are the
original hypergeometric parameters of the differential operator, not the half-shifted BM
connection exponents.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set Filter Topology Nat FormalMultilinearSeries Polynomial

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Shifted first parameter of the regular exponent-`N+1` mixed-horizon branch. -/
def d4BMMixedHorizonShiftedRegularA (n k : ℕ) (chi : ℂ) : ℂ :=
  d4BMMixedHorizonComplexA n k chi +
    (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ)

/-- Shifted second parameter of the regular exponent-`N+1` mixed-horizon branch. -/
def d4BMMixedHorizonShiftedRegularB (n k : ℕ) (chi : ℂ) : ℂ :=
  d4BMMixedHorizonComplexB n k chi +
    (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ)

/-- Positive denominator parameter of the shifted regular Gauss series. -/
def d4BMMixedHorizonShiftedRegularC (n k : ℕ) : ℂ :=
  (d4BMMixedHorizonFrobeniusOrder n k + 2 : ℕ)

/-- Shifted mixed-horizon parameters avoid every nonpositive integer when `chi.re ≠ 0`. -/
theorem d4BMMixedHorizonShiftedRegularParameters_ne_negNat
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    (j : ℂ) ≠ -d4BMMixedHorizonShiftedRegularA n k chi ∧
      (j : ℂ) ≠ -d4BMMixedHorizonShiftedRegularB n k chi ∧
      (j : ℂ) ≠ -d4BMMixedHorizonShiftedRegularC n k := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [d4BMMixedHorizonShiftedRegularA, d4BMMixedHorizonComplexA,
      d4BMCausalHypergeometricA_plusMinus] at him
    simp [Complex.mul_im] at him
    exact hchi (by linarith)
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [d4BMMixedHorizonShiftedRegularB, d4BMMixedHorizonComplexB,
      d4BMCausalHypergeometricB_plusMinus] at him
    simp [Complex.mul_im] at him
    exact hchi (by linarith)
  · intro h
    have hre := congrArg Complex.re h
    rw [d4BMMixedHorizonShiftedRegularC] at hre
    norm_num at hre
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hc : 0 < ((d4BMMixedHorizonFrobeniusOrder n k + 2 : ℕ) : ℝ) := by
      positivity
    linarith

/-- Formal Gauss series multiplying the regular Frobenius power. -/
def d4BMMixedHorizonRegularHypergeometricSeries
    (n k : ℕ) (chi : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ
    (d4BMMixedHorizonShiftedRegularA n k chi)
    (d4BMMixedHorizonShiftedRegularB n k chi)
    (d4BMMixedHorizonShiftedRegularC n k)

/-- Exact radius one of the shifted regular Gauss series. -/
theorem d4BMMixedHorizonRegularHypergeometricSeries_radius_eq_one
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (d4BMMixedHorizonRegularHypergeometricSeries n k chi).radius = 1 := by
  rw [d4BMMixedHorizonRegularHypergeometricSeries]
  apply ordinaryHypergeometricSeries_radius_eq_one
  exact d4BMMixedHorizonShiftedRegularParameters_ne_negNat n k chi hchi

/-- Analytic factor in the regular exponent-`N+1` branch. -/
def d4BMMixedHorizonRegularHypergeometricFactor
    (n k : ℕ) (chi z : ℂ) : ℂ :=
  (d4BMMixedHorizonRegularHypergeometricSeries n k chi).sum z

/-- First derivative-series value of the analytic regular factor. -/
def d4BMMixedHorizonRegularHypergeometricFactorDerivative
    (n k : ℕ) (chi z : ℂ) : ℂ :=
  (((d4BMMixedHorizonRegularHypergeometricSeries n k chi).derivSeries.sum z) 1)

/-- Second derivative-series value of the analytic regular factor. -/
def d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative
    (n k : ℕ) (chi z : ℂ) : ℂ :=
  ((((d4BMMixedHorizonRegularHypergeometricSeries n k chi).derivSeries.derivSeries.sum z)
    1) 1)

@[simp]
theorem d4BMMixedHorizonRegularHypergeometricFactor_zero
    (n k : ℕ) (chi : ℂ) :
    d4BMMixedHorizonRegularHypergeometricFactor n k chi 0 = 1 := by
  change ordinaryHypergeometric
    (d4BMMixedHorizonShiftedRegularA n k chi)
    (d4BMMixedHorizonShiftedRegularB n k chi)
    (d4BMMixedHorizonShiftedRegularC n k) 0 = 1
  exact ordinaryHypergeometric_zero _ _ _

/-- Analytic regular factor has its exact first derivative throughout the unit disk. -/
theorem hasDerivAt_d4BMMixedHorizonRegularHypergeometricFactor
    (n k : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMMixedHorizonRegularHypergeometricFactor n k chi)
      (d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z) z := by
  let p := d4BMMixedHorizonRegularHypergeometricSeries n k chi
  have hzp : ‖z‖ₑ < p.radius := by
    rw [d4BMMixedHorizonRegularHypergeometricSeries_radius_eq_one n k chi hchi]
    exact hz
  change HasDerivAt p.sum ((p.derivSeries.sum z) 1) z
  exact (p.hasFDerivAt_sum hzp).hasDerivAt

/-- First derivative of the analytic regular factor has its exact derivative-series value. -/
theorem hasDerivAt_d4BMMixedHorizonRegularHypergeometricFactorDerivative
    (n k : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi)
      (d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative n k chi z) z := by
  let p := d4BMMixedHorizonRegularHypergeometricSeries n k chi
  let q := p.derivSeries
  have hzp : ‖z‖ₑ < p.radius := by
    rw [d4BMMixedHorizonRegularHypergeometricSeries_radius_eq_one n k chi hchi]
    exact hz
  have hzq : ‖z‖ₑ < q.radius :=
    lt_of_lt_of_le hzp p.radius_le_radius_derivSeries
  have hq := q.hasFDerivAt_sum hzq
  have heval := hq.clm_apply (hasFDerivAt_const (1 : ℂ) z)
  change HasDerivAt (fun w : ℂ => (q.sum w) 1)
    (((q.derivSeries.sum z) 1) 1) z
  simpa using heval.hasDerivAt

/-- Exact regular exponent-`N+1` mixed-horizon solution. -/
def d4BMMixedHorizonRegularBranch
    (n k : ℕ) (chi z : ℂ) : ℂ :=
  z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) *
    d4BMMixedHorizonRegularHypergeometricFactor n k chi z

/-- Exact first jet of the regular mixed-horizon branch. -/
def d4BMMixedHorizonRegularBranchDerivative
    (n k : ℕ) (chi z : ℂ) : ℂ :=
  (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ) *
      z ^ d4BMMixedHorizonFrobeniusOrder n k *
        d4BMMixedHorizonRegularHypergeometricFactor n k chi z +
    z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) *
      d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z

/-- Exact second jet of the regular mixed-horizon branch. -/
def d4BMMixedHorizonRegularBranchSecondDerivative
    (n k : ℕ) (chi z : ℂ) : ℂ :=
  (d4BMMixedHorizonFrobeniusOrder n k : ℂ) *
      (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ) *
      z ^ (d4BMMixedHorizonFrobeniusOrder n k - 1) *
        d4BMMixedHorizonRegularHypergeometricFactor n k chi z +
    2 * (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ) *
      z ^ d4BMMixedHorizonFrobeniusOrder n k *
        d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z +
    z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) *
      d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative n k chi z

/-- The mixed regular branch first jet is its actual derivative. -/
theorem hasDerivAt_d4BMMixedHorizonRegularBranch
    (n k : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMMixedHorizonRegularBranch n k chi)
      (d4BMMixedHorizonRegularBranchDerivative n k chi z) z := by
  have hpow := hasDerivAt_pow (d4BMMixedHorizonFrobeniusOrder n k + 1) z
  have hfactor := hasDerivAt_d4BMMixedHorizonRegularHypergeometricFactor
    n k chi z hchi hz
  refine (hpow.mul hfactor).congr_deriv ?_
  rw [d4BMMixedHorizonRegularBranchDerivative]
  simp

/-- The mixed regular branch second jet differentiates its first jet. -/
theorem hasDerivAt_d4BMMixedHorizonRegularBranchDerivative
    (n k : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMMixedHorizonRegularBranchDerivative n k chi)
      (d4BMMixedHorizonRegularBranchSecondDerivative n k chi z) z := by
  let N := d4BMMixedHorizonFrobeniusOrder n k
  have hfactor := hasDerivAt_d4BMMixedHorizonRegularHypergeometricFactor
    n k chi z hchi hz
  have hfactor' := hasDerivAt_d4BMMixedHorizonRegularHypergeometricFactorDerivative
    n k chi z hchi hz
  have hfirst := ((hasDerivAt_pow N z).mul hfactor).const_mul (N + 1 : ℂ)
  have hsecond := (hasDerivAt_pow (N + 1) z).mul hfactor'
  have hsum := hfirst.add hsecond
  change HasDerivAt
    (fun w : ℂ =>
      (N + 1 : ℂ) * w ^ N *
          d4BMMixedHorizonRegularHypergeometricFactor n k chi w +
        w ^ (N + 1) *
          d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi w)
    ((N : ℂ) * (N + 1 : ℂ) * z ^ (N - 1) *
          d4BMMixedHorizonRegularHypergeometricFactor n k chi z +
        2 * (N + 1 : ℂ) * z ^ N *
          d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z +
        z ^ (N + 1) *
          d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative n k chi z) z
  have hderiv :
      (N + 1 : ℂ) *
          ((N : ℂ) * z ^ (N - 1) *
              d4BMMixedHorizonRegularHypergeometricFactor n k chi z +
            z ^ N *
              d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z) +
        (((N + 1 : ℕ) : ℂ) * z ^ (N + 1 - 1) *
            d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z +
          z ^ (N + 1) *
            d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative n k chi z) =
      (N : ℂ) * (N + 1 : ℂ) * z ^ (N - 1) *
            d4BMMixedHorizonRegularHypergeometricFactor n k chi z +
          2 * (N + 1 : ℂ) * z ^ N *
            d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z +
          z ^ (N + 1) *
            d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative n k chi z := by
    simp
    ring
  have hsum' := hsum.congr_deriv hderiv
  apply hsum'.congr_of_eventuallyEq
  filter_upwards with w
  simp
  ring

/-- Frobenius power shift converts the shifted Gauss equation to the original equation at
`c=-N`. -/
theorem hypergeometric_resonantRegularBranch_jet_eq_zero
    (N : ℕ) (hN : 0 < N) (a b z F dF ddF : ℂ)
    (hshifted :
      z * (1 - z) * ddF +
          ((N + 2 : ℕ) -
            ((a + (N + 1 : ℕ)) + (b + (N + 1 : ℕ)) + 1) * z) * dF -
        (a + (N + 1 : ℕ)) * (b + (N + 1 : ℕ)) * F = 0) :
    z * (1 - z) *
          ((N : ℂ) * (N + 1 : ℂ) * z ^ (N - 1) * F +
            2 * (N + 1 : ℂ) * z ^ N * dF + z ^ (N + 1) * ddF) +
        (-(N : ℂ) - (a + b + 1) * z) *
          ((N + 1 : ℂ) * z ^ N * F + z ^ (N + 1) * dF) -
      a * b * (z ^ (N + 1) * F) = 0 := by
  have hpowN : z ^ N = z ^ (N - 1) * z := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have hpowN1 : z ^ (N + 1) = z ^ (N - 1) * z ^ (2 : ℕ) := by
    rw [← pow_add]
    congr 1
    omega
  push_cast at hshifted ⊢
  rw [hpowN, hpowN1]
  linear_combination z ^ (N - 1) * z ^ (2 : ℕ) * hshifted

/-- The analytic factor satisfies its shifted Gauss equation in the unit disk. -/
theorem d4BMMixedHorizonRegularHypergeometricFactor_jet_eq_zero
    (n k : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) *
          d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative n k chi z +
        (d4BMMixedHorizonShiftedRegularC n k -
          (d4BMMixedHorizonShiftedRegularA n k chi +
            d4BMMixedHorizonShiftedRegularB n k chi + 1) * z) *
          d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z -
      d4BMMixedHorizonShiftedRegularA n k chi *
        d4BMMixedHorizonShiftedRegularB n k chi *
          d4BMMixedHorizonRegularHypergeometricFactor n k chi z = 0 := by
  let a := d4BMMixedHorizonShiftedRegularA n k chi
  let b := d4BMMixedHorizonShiftedRegularB n k chi
  let c := d4BMMixedHorizonShiftedRegularC n k
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -c := by
    intro j
    exact (d4BMMixedHorizonShiftedRegularParameters_ne_negNat n k chi hchi j).2.2
  have hzr : ‖z‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
    change ‖z‖ₑ < (d4BMMixedHorizonRegularHypergeometricSeries n k chi).radius
    rw [d4BMMixedHorizonRegularHypergeometricSeries_radius_eq_one n k chi hchi]
    exact hz
  have hode := ordinaryHypergeometric_standardGaussODE a b c z hc hzr
  simpa only [a, b, c,
    d4BMMixedHorizonRegularHypergeometricFactor,
    d4BMMixedHorizonRegularHypergeometricFactorDerivative,
    d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative,
    d4BMMixedHorizonRegularHypergeometricSeries,
    ordinaryHypergeometricFirstDerivativeSeriesValue,
    ordinaryHypergeometricSecondDerivativeSeriesValue] using hode

/-- Exact regular exponent-`N+1` branch solves the literal complex-momentum mixed BM equation. -/
theorem d4BMMixedHorizonRegularBranch_jet_eq_zero
    (n k : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) * d4BMMixedHorizonRegularBranchSecondDerivative n k chi z +
        (d4BMCausalRadialC (d4BMCausalPlusMinusFrequency n k chi) -
          (d4BMMixedHorizonComplexA n k chi +
            d4BMMixedHorizonComplexB n k chi + 1) * z) *
          d4BMMixedHorizonRegularBranchDerivative n k chi z -
      d4BMMixedHorizonComplexA n k chi *
        d4BMMixedHorizonComplexB n k chi *
          d4BMMixedHorizonRegularBranch n k chi z = 0 := by
  let N := d4BMMixedHorizonFrobeniusOrder n k
  have hN : 0 < N := by
    simp [N, d4BMMixedHorizonFrobeniusOrder]
  have hfactor := d4BMMixedHorizonRegularHypergeometricFactor_jet_eq_zero
    n k chi z hchi hz
  rw [d4BMMixedHorizonShiftedRegularA,
    d4BMMixedHorizonShiftedRegularB,
    d4BMMixedHorizonShiftedRegularC] at hfactor
  have htransform := hypergeometric_resonantRegularBranch_jet_eq_zero
    N hN (d4BMMixedHorizonComplexA n k chi)
      (d4BMMixedHorizonComplexB n k chi) z
      (d4BMMixedHorizonRegularHypergeometricFactor n k chi z)
      (d4BMMixedHorizonRegularHypergeometricFactorDerivative n k chi z)
      (d4BMMixedHorizonRegularHypergeometricFactorSecondDerivative n k chi z)
      hfactor
  rw [d4BMMixedHorizonRegularBranch,
    d4BMMixedHorizonRegularBranchDerivative,
    d4BMMixedHorizonRegularBranchSecondDerivative,
    d4BMCausalRadialC_plusMinus_eq_negNat]
  simpa [N, d4BMMixedHorizonFrobeniusOrder] using htransform

/-- Every Xi fibre carries the exact resonant regular mixed-horizon solution. -/
theorem d4BMXiMixedHorizonRegularBranch_jet_eq_zero
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) *
          d4BMMixedHorizonRegularBranchSecondDerivative n k
            (d4BMXiMixedHorizonAngularMomentum q) z +
        (d4BMCausalRadialC
            (d4BMCausalPlusMinusFrequency n k (d4BMXiMixedHorizonAngularMomentum q)) -
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q) +
            d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q) + 1) * z) *
          d4BMMixedHorizonRegularBranchDerivative n k
            (d4BMXiMixedHorizonAngularMomentum q) z -
      d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q) *
        d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMMixedHorizonRegularBranch n k
            (d4BMXiMixedHorizonAngularMomentum q) z = 0 := by
  exact d4BMMixedHorizonRegularBranch_jet_eq_zero n k _ z
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz

/-- The exact regular branch has leading horizon coefficient one. -/
theorem tendsto_d4BMMixedHorizonRegularBranch_div_pow_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun z : ℂ => d4BMMixedHorizonRegularBranch n k chi z /
        z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1))
      (𝓝[≠] 0) (𝓝 1) := by
  have hcont : ContinuousAt
      (d4BMMixedHorizonRegularHypergeometricFactor n k chi) 0 :=
    (hasDerivAt_d4BMMixedHorizonRegularHypergeometricFactor n k chi 0 hchi
      (by simp)).continuousAt
  have heq :
      (fun z : ℂ => d4BMMixedHorizonRegularBranch n k chi z /
        z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1)) =ᶠ[𝓝[≠] 0]
      d4BMMixedHorizonRegularHypergeometricFactor n k chi := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [d4BMMixedHorizonRegularBranch]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hz)
  have ht : Tendsto
      (d4BMMixedHorizonRegularHypergeometricFactor n k chi)
      (𝓝[≠] 0) (𝓝 1) := by
    have ht0 : Tendsto
        (d4BMMixedHorizonRegularHypergeometricFactor n k chi)
        (𝓝[≠] 0)
        (𝓝 (d4BMMixedHorizonRegularHypergeometricFactor n k chi 0)) :=
      hcont.continuousWithinAt.tendsto
    simpa using ht0
  exact ht.congr' heq.symm

/-- Exact regular branch divided by its leading horizon Wronskian `N+1`. -/
def d4BMMixedHorizonExactUnitWronskianRegularBranch
    (n k : ℕ) (chi z : ℂ) : ℂ :=
  d4BMMixedHorizonRegularBranch n k chi z /
    (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ)

/-- Complex monodromy coefficient in the exact unit-Wronskian branch normalization. -/
def d4BMMixedHorizonComplexUnitWronskianMonodromyJump
    (n k : ℕ) (chi : ℂ) : ℂ :=
  (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ) *
    d4BMMixedHorizonComplexMonodromyJump n k chi

/-- Raw and unit-Wronskian coefficients give the same exact hypergeometric monodromy mode. -/
theorem d4BMMixedHorizonComplexMonodromy_raw_eq_exactUnitWronskian
    (n k : ℕ) (chi z : ℂ) :
    d4BMMixedHorizonComplexMonodromyJump n k chi *
        d4BMMixedHorizonRegularBranch n k chi z =
      d4BMMixedHorizonComplexUnitWronskianMonodromyJump n k chi *
        d4BMMixedHorizonExactUnitWronskianRegularBranch n k chi z := by
  rw [d4BMMixedHorizonComplexUnitWronskianMonodromyJump,
    d4BMMixedHorizonExactUnitWronskianRegularBranch]
  have hN : (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (d4BMMixedHorizonFrobeniusOrder n k)
  field_simp [hN]

/-- Actual Xi-fibre logarithmic monodromy mode on the exact resonant regular branch. -/
def d4BMXiMixedHorizonExactMonodromyMode
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  d4BMXiMixedHorizonComplexMonodromyJump n k q *
    d4BMMixedHorizonRegularBranch n k
      (d4BMXiMixedHorizonAngularMomentum q) z

/-- First jet of the exact Xi-fibre monodromy mode. -/
def d4BMXiMixedHorizonExactMonodromyModeDerivative
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  d4BMXiMixedHorizonComplexMonodromyJump n k q *
    d4BMMixedHorizonRegularBranchDerivative n k
      (d4BMXiMixedHorizonAngularMomentum q) z

/-- Second jet of the exact Xi-fibre monodromy mode. -/
def d4BMXiMixedHorizonExactMonodromyModeSecondDerivative
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  d4BMXiMixedHorizonComplexMonodromyJump n k q *
    d4BMMixedHorizonRegularBranchSecondDerivative n k
      (d4BMXiMixedHorizonAngularMomentum q) z

/-- Exact Xi-fibre logarithmic monodromy mode solves the literal homogeneous mixed BM equation. -/
theorem d4BMXiMixedHorizonExactMonodromyMode_jet_eq_zero
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) * d4BMXiMixedHorizonExactMonodromyModeSecondDerivative n k q z +
        (d4BMCausalRadialC
            (d4BMCausalPlusMinusFrequency n k (d4BMXiMixedHorizonAngularMomentum q)) -
          (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q) +
            d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q) + 1) * z) *
          d4BMXiMixedHorizonExactMonodromyModeDerivative n k q z -
      d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q) *
        d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMXiMixedHorizonExactMonodromyMode n k q z = 0 := by
  have hbranch := d4BMXiMixedHorizonRegularBranch_jet_eq_zero n k q z hz
  rw [d4BMXiMixedHorizonExactMonodromyMode,
    d4BMXiMixedHorizonExactMonodromyModeDerivative,
    d4BMXiMixedHorizonExactMonodromyModeSecondDerivative]
  linear_combination d4BMXiMixedHorizonComplexMonodromyJump n k q * hbranch

/-- The exact Xi-fibre monodromy mode has the corrected nonzero Frobenius jump as its leading
horizon coefficient. -/
theorem tendsto_d4BMXiMixedHorizonExactMonodromyMode_div_pow_zero
    (n k : ℕ) (q : XiZeroCopy) :
    Tendsto
      (fun z : ℂ => d4BMXiMixedHorizonExactMonodromyMode n k q z /
        z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1))
      (𝓝[≠] 0)
      (𝓝 (d4BMXiMixedHorizonComplexMonodromyJump n k q)) := by
  have hbranch := tendsto_d4BMMixedHorizonRegularBranch_div_pow_zero n k
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)
  have ht := (tendsto_const_nhds.mul hbranch :
    Tendsto
      (fun z : ℂ => d4BMXiMixedHorizonComplexMonodromyJump n k q *
        (d4BMMixedHorizonRegularBranch n k
          (d4BMXiMixedHorizonAngularMomentum q) z /
            z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1)))
      (𝓝[≠] 0)
      (𝓝 (d4BMXiMixedHorizonComplexMonodromyJump n k q * 1)))
  simpa [d4BMXiMixedHorizonExactMonodromyMode, mul_div_assoc] using ht

end

end RHTower
