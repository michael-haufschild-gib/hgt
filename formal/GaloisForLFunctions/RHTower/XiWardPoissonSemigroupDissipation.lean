import GaloisForLFunctions.RHTower.XiWardTriangularSourceRectangle
import GaloisForLFunctions.HTGeometry.MollifierL2Contraction
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel

/-!
# Poisson-semigroup dissipation of finite Ward packets

Increasing the positive real observation shift is not an unrelated second
probe.  Every Lorentzian Ward column at width `sigma + D` is exactly the
Poisson-`D` mollification of the column at width `sigma`.  The same holds
for finite Schwarz-paired packets.  Young's probability-kernel contraction
therefore makes the Ward annulus a globally nonnegative quadratic form,
despite its individual cross-kernel entries changing sign at long distance.

This removes a padding obstruction from the source-rectangle route: adding a
positive common real shift loses energy by a literal source-independent
contraction, not by a divisor-dependent sign choice.
-/

open Complex Set intervalIntegral
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem wardLorentzianHalf_eq_pi_mul_halfPlanePoisson
    (x beta t : ℝ) :
    wardLorentzianHalf x beta t =
      Real.pi * halfPlanePoisson x (t + beta) := by
  unfold wardLorentzianHalf halfPlanePoisson
  by_cases hpi : Real.pi = 0
  · exact (Real.pi_ne_zero hpi).elim
  field_simp

theorem mollify_halfPlanePoisson_wardLorentzianHalf
    {D x : ℝ} (hD : 0 < D) (hx : 0 < x) (beta t : ℝ) :
    mollify (halfPlanePoisson D) (wardLorentzianHalf x beta) t =
      wardLorentzianHalf (x + D) beta t := by
  rw [mollify_eq_lineConvolution]
  unfold lineConvolution
  simp_rw [wardLorentzianHalf_eq_pi_mul_halfPlanePoisson]
  rw [show (fun u : ℝ =>
      halfPlanePoisson D u *
        (Real.pi * halfPlanePoisson x (t - u + beta))) =
      (fun u : ℝ => Real.pi *
        (halfPlanePoisson x ((t + beta) - u) *
          halfPlanePoisson D (u - 0))) by
    funext u
    have harg : t - u + beta = t + beta - u := by ring
    rw [harg, sub_zero]
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_poisson_shift_product hx hD (t + beta) 0]
  simp

theorem integrable_halfPlanePoisson_mul_wardLorentzianHalf_shift
    {D x : ℝ} (hD : 0 < D) (hx : 0 < x) (beta t : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ =>
      halfPlanePoisson D u * wardLorentzianHalf x beta (t - u)) := by
  have h :=
    (integrable_poisson_shift_product hx hD (t + beta) 0).const_mul Real.pi
  convert h using 1
  funext u
  rw [wardLorentzianHalf_eq_pi_mul_halfPlanePoisson]
  ring_nf

theorem mollify_halfPlanePoisson_wardReflectedLorentzianProfile
    {D x : ℝ} (hD : 0 < D) (hx : 0 < x) (beta t : ℝ) :
    mollify (halfPlanePoisson D) (wardReflectedLorentzianProfile x beta) t =
      wardReflectedLorentzianProfile (x + D) beta t := by
  rw [mollify_eq_lineConvolution]
  unfold lineConvolution wardReflectedLorentzianProfile
  rw [show (fun u : ℝ =>
      halfPlanePoisson D u *
        (2 * wardLorentzianHalf x beta (t - u) +
          2 * wardLorentzianHalf x (-beta) (t - u))) =
      (fun u : ℝ =>
        2 * (halfPlanePoisson D u * wardLorentzianHalf x beta (t - u)) +
        2 * (halfPlanePoisson D u *
          wardLorentzianHalf x (-beta) (t - u))) by
    funext u
    ring]
  rw [MeasureTheory.integral_add
      ((integrable_halfPlanePoisson_mul_wardLorentzianHalf_shift
        hD hx beta t).const_mul 2)
      ((integrable_halfPlanePoisson_mul_wardLorentzianHalf_shift
        hD hx (-beta) t).const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [show (∫ u : ℝ,
      halfPlanePoisson D u * wardLorentzianHalf x beta (t - u)) =
        wardLorentzianHalf (x + D) beta t by
      simpa [mollify_eq_lineConvolution, lineConvolution] using
        mollify_halfPlanePoisson_wardLorentzianHalf hD hx beta t,
    show (∫ u : ℝ,
      halfPlanePoisson D u * wardLorentzianHalf x (-beta) (t - u)) =
        wardLorentzianHalf (x + D) (-beta) t by
      simpa [mollify_eq_lineConvolution, lineConvolution] using
        mollify_halfPlanePoisson_wardLorentzianHalf hD hx (-beta) t]

theorem integrable_halfPlanePoisson_mul_wardReflectedLorentzianProfile_shift
    {D x : ℝ} (hD : 0 < D) (hx : 0 < x) (beta t : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ =>
      halfPlanePoisson D u *
        wardReflectedLorentzianProfile x beta (t - u)) := by
  unfold wardReflectedLorentzianProfile
  rw [show (fun u : ℝ =>
      halfPlanePoisson D u *
        (2 * wardLorentzianHalf x beta (t - u) +
          2 * wardLorentzianHalf x (-beta) (t - u))) =
      (fun u : ℝ =>
        2 * (halfPlanePoisson D u * wardLorentzianHalf x beta (t - u)) +
        2 * (halfPlanePoisson D u *
          wardLorentzianHalf x (-beta) (t - u))) by
    funext u
    ring]
  exact
    ((integrable_halfPlanePoisson_mul_wardLorentzianHalf_shift
      hD hx beta t).const_mul 2).add
    ((integrable_halfPlanePoisson_mul_wardLorentzianHalf_shift
      hD hx (-beta) t).const_mul 2)

/-- Real Ward profile of a finite upper packet and its Schwarz mates. -/
def xiWardFinitePairRealProfile
    (sigma : ℝ) (S : Finset XiRightUpperZeroCopy) (t : ℝ) : ℝ :=
  ∑ q ∈ S,
    (xiAntiCausalWardSchwarzPairResponse q
      ((sigma : ℂ) + I * (t : ℂ))).re

theorem xiWardFinitePairRealProfile_eq_reflected_sum
    (sigma : ℝ) (S : Finset XiRightUpperZeroCopy) (t : ℝ) :
    xiWardFinitePairRealProfile sigma S t =
      ∑ q ∈ S, wardReflectedLorentzianProfile
        (sigma + (xiRightCenteredZero q.1).re)
        (xiRightCenteredZero q.1).im t := by
  unfold xiWardFinitePairRealProfile
  simp_rw [re_xiAntiCausalWardSchwarzPairResponse_eq_reflectedProfile]

theorem integrable_sq_xiWardFinitePairRealProfile
    {sigma : ℝ} (hsigma : 0 < sigma)
    (S : Finset XiRightUpperZeroCopy) :
    MeasureTheory.Integrable (fun t : ℝ =>
      xiWardFinitePairRealProfile sigma S t ^ 2) := by
  classical
  let F : XiRightUpperZeroCopy × XiRightUpperZeroCopy → ℝ → ℝ :=
    fun p t =>
      (xiAntiCausalWardSchwarzPairResponse p.1
        ((sigma : ℂ) + I * (t : ℂ))).re *
      (xiAntiCausalWardSchwarzPairResponse p.2
        ((sigma : ℂ) + I * (t : ℂ))).re
  have hF : ∀ p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
      MeasureTheory.Integrable (F p) := by
    intro p
    exact integrable_re_xiAntiCausalWardSchwarzPairResponse_mul
      hsigma p.1 p.2
  have hsum :
      ∀ A : Finset (XiRightUpperZeroCopy × XiRightUpperZeroCopy),
      MeasureTheory.Integrable (fun t : ℝ => ∑ p ∈ A, F p t) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert p A hp ih =>
        refine ((hF p).add ih).congr ?_
        filter_upwards with t
        rw [Pi.add_apply, Finset.sum_insert hp]
  rw [show
      (fun t : ℝ => xiWardFinitePairRealProfile sigma S t ^ 2) =
      (fun t : ℝ => ∑ p ∈ S ×ˢ S, F p t) by
    funext t
    unfold xiWardFinitePairRealProfile F
    rw [pow_two, Finset.sum_mul_sum]
    exact (Finset.sum_product S S (fun p =>
      (xiAntiCausalWardSchwarzPairResponse p.1
        ((sigma : ℂ) + I * (t : ℂ))).re *
      (xiAntiCausalWardSchwarzPairResponse p.2
        ((sigma : ℂ) + I * (t : ℂ))).re)).symm]
  exact hsum (S ×ˢ S)

theorem continuous_wardLorentzianHalf
    {x : ℝ} (hx : 0 < x) (beta : ℝ) :
    Continuous (wardLorentzianHalf x beta) := by
  unfold wardLorentzianHalf
  apply Continuous.div continuous_const (by fun_prop)
  intro t hzero
  have hpos : 0 < x ^ 2 + (t + beta) ^ 2 := by positivity
  linarith

theorem continuous_wardReflectedLorentzianProfile
    {x : ℝ} (hx : 0 < x) (beta : ℝ) :
    Continuous (wardReflectedLorentzianProfile x beta) := by
  unfold wardReflectedLorentzianProfile
  exact (continuous_const.mul (continuous_wardLorentzianHalf hx beta)).add
    (continuous_const.mul (continuous_wardLorentzianHalf hx (-beta)))

theorem measurable_xiWardFinitePairRealProfile
    {sigma : ℝ} (hsigma : 0 < sigma)
    (S : Finset XiRightUpperZeroCopy) :
    Measurable (xiWardFinitePairRealProfile sigma S) := by
  rw [show xiWardFinitePairRealProfile sigma S =
      fun t : ℝ => ∑ q ∈ S, wardReflectedLorentzianProfile
        (sigma + (xiRightCenteredZero q.1).re)
        (xiRightCenteredZero q.1).im t by
    funext t
    exact xiWardFinitePairRealProfile_eq_reflected_sum sigma S t]
  apply Finset.measurable_sum
  intro q hq
  exact (continuous_wardReflectedLorentzianProfile
    (by linarith [xiRightCenteredZero_re_pos q.1])
    (xiRightCenteredZero q.1).im).measurable

/-- Finite Ward packets form an exact Poisson semigroup in common positive
real shift. -/
theorem mollify_halfPlanePoisson_xiWardFinitePairRealProfile
    {sigma D : ℝ} (hsigma : 0 < sigma) (hD : 0 < D)
    (S : Finset XiRightUpperZeroCopy) (t : ℝ) :
    mollify (halfPlanePoisson D) (xiWardFinitePairRealProfile sigma S) t =
      xiWardFinitePairRealProfile (sigma + D) S t := by
  rw [mollify_eq_lineConvolution]
  unfold lineConvolution
  rw [show (fun u : ℝ =>
      halfPlanePoisson D u * xiWardFinitePairRealProfile sigma S (t - u)) =
      (fun u : ℝ => ∑ q ∈ S,
        halfPlanePoisson D u *
          (xiAntiCausalWardSchwarzPairResponse q
            ((sigma : ℂ) + I * ((t - u : ℝ) : ℂ))).re) by
    funext u
    unfold xiWardFinitePairRealProfile
    rw [Finset.mul_sum]]
  have hterm : ∀ q ∈ S, MeasureTheory.Integrable (fun u : ℝ =>
      halfPlanePoisson D u *
        (xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * ((t - u : ℝ) : ℂ))).re) := by
    intro q hq
    rw [show (fun u : ℝ =>
      halfPlanePoisson D u *
        (xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * ((t - u : ℝ) : ℂ))).re) =
      (fun u : ℝ => halfPlanePoisson D u *
        wardReflectedLorentzianProfile
          (sigma + (xiRightCenteredZero q.1).re)
          (xiRightCenteredZero q.1).im (t - u)) by
        funext u
        rw [re_xiAntiCausalWardSchwarzPairResponse_eq_reflectedProfile]]
    exact
      integrable_halfPlanePoisson_mul_wardReflectedLorentzianProfile_shift
        hD (by linarith [xiRightCenteredZero_re_pos q.1])
        (xiRightCenteredZero q.1).im t
  rw [MeasureTheory.integral_finsetSum S hterm]
  unfold xiWardFinitePairRealProfile
  apply Finset.sum_congr rfl
  intro q hq
  rw [show (∫ u : ℝ,
      halfPlanePoisson D u *
        (xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * ((t - u : ℝ) : ℂ))).re) =
      mollify (halfPlanePoisson D)
        (wardReflectedLorentzianProfile
          (sigma + (xiRightCenteredZero q.1).re)
          (xiRightCenteredZero q.1).im) t by
      rw [mollify_eq_lineConvolution]
      unfold lineConvolution
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      rw [re_xiAntiCausalWardSchwarzPairResponse_eq_reflectedProfile],
    mollify_halfPlanePoisson_wardReflectedLorentzianProfile hD
      (by linarith [xiRightCenteredZero_re_pos q.1])]
  rw [re_xiAntiCausalWardSchwarzPairResponse_eq_reflectedProfile]
  congr 1
  ring

theorem xiWardFinitePairRealEnergyAtLine_eq_profile
    (sigma : ℝ) (S : Finset XiRightUpperZeroCopy) :
    xiWardFinitePairRealEnergyAtLine sigma S =
      ∫ t : ℝ, xiWardFinitePairRealProfile sigma S t ^ 2 := by
  rfl

/-- **Global Ward dissipation.** Advancing every Ward width is exactly
Poisson mollification, hence cannot increase total real-line energy. -/
theorem xiWardFinitePairRealEnergyAtLine_add_le
    {sigma D : ℝ} (hsigma : 0 < sigma) (hD : 0 < D)
    (S : Finset XiRightUpperZeroCopy) :
    xiWardFinitePairRealEnergyAtLine (sigma + D) S ≤
      xiWardFinitePairRealEnergyAtLine sigma S := by
  have hconv : MeasureTheory.Integrable (fun t : ℝ =>
      mollify (halfPlanePoisson D)
        (xiWardFinitePairRealProfile sigma S) t ^ 2) := by
    rw [show (fun t : ℝ =>
      mollify (halfPlanePoisson D)
        (xiWardFinitePairRealProfile sigma S) t ^ 2) =
      (fun t : ℝ =>
        xiWardFinitePairRealProfile (sigma + D) S t ^ 2) by
        funext t
        rw [mollify_halfPlanePoisson_xiWardFinitePairRealProfile
          hsigma hD S t]]
    exact integrable_sq_xiWardFinitePairRealProfile (by positivity) S
  have hcontract := integral_sq_mollify_le_of_isProbabilityDensity
    (continuous_halfPlanePoisson hD).measurable
    (measurable_xiWardFinitePairRealProfile hsigma S)
    (fun t => (halfPlanePoisson_pos hD t).le)
    (integrable_halfPlanePoisson hD)
    (integral_halfPlanePoisson hD)
    (integrable_sq_xiWardFinitePairRealProfile hsigma S)
    hconv
  rw [show (∫ t : ℝ,
      mollify (halfPlanePoisson D)
        (xiWardFinitePairRealProfile sigma S) t ^ 2) =
      xiWardFinitePairRealEnergyAtLine (sigma + D) S by
        rw [xiWardFinitePairRealEnergyAtLine_eq_profile]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rw [mollify_halfPlanePoisson_xiWardFinitePairRealProfile
          hsigma hD S t],
    ← xiWardFinitePairRealEnergyAtLine_eq_profile] at hcontract
  exact hcontract

/-- The concrete source-safe ten-unit Ward annulus is globally nonnegative
for every finite Schwarz-paired multiplicity packet. -/
theorem xiWardFinitePairRealEnergyAtLine_fiftyOne_sub_tenShift_nonneg
    (S : Finset XiRightUpperZeroCopy) :
    0 ≤ xiWardFinitePairRealEnergyAtLine (51 / 100) S -
      xiWardFinitePairRealEnergyAtLine (1051 / 100) S := by
  have h := xiWardFinitePairRealEnergyAtLine_add_le
    (sigma := (51 / 100 : ℝ)) (D := 10)
    (by norm_num) (by norm_num) S
  norm_num at h ⊢
  linarith

/-! ## Source-rectangle dissipation interface -/

/-- A single source rectangle pair which renders the same finite Ward packet
on two positive observation lines inherits the Poisson-semigroup contraction.
The conclusion is stated entirely in terms of the source-rectangle energies;
the packet occurs only in the response certificate. -/
theorem xiWardPairedSourceRectangleRealEnergyAtLine_add_le_of_samePacket
    {sigma D : ℝ} (hsigma : 0 < sigma) (hD : 0 < D)
    (S : Finset XiRightUpperZeroCopy) (z₁ z₂ z₁' z₂' : ℂ)
    (hnarrow : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          ((sigma : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q
          ((sigma : ℂ) + I * (t : ℂ)))
    (hwide : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((sigma + D : ℝ) : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q
          (((sigma + D : ℝ) : ℂ) + I * (t : ℂ))) :
    xiWardPairedSourceRectangleRealEnergyAtLine
        (sigma + D) z₁ z₂ z₁' z₂' ≤
      xiWardPairedSourceRectangleRealEnergyAtLine
        sigma z₁ z₂ z₁' z₂' := by
  rw [xiWardPairedSourceRectangleRealEnergyAtLine_eq_finite
      (sigma + D) S z₁ z₂ z₁' z₂' hwide,
    xiWardPairedSourceRectangleRealEnergyAtLine_eq_finite
      sigma S z₁ z₂ z₁' z₂' hnarrow]
  exact xiWardFinitePairRealEnergyAtLine_add_le hsigma hD S

/-- The source annulus is always bounded above by its narrow-line source
energy.  This estimate is pre-divisor and needs no response identity. -/
theorem xiWardPairedSourceRectangleAnnulusEnergy_le_narrow
    (z₁ z₂ z₁' z₂' : ℂ) :
    xiWardPairedSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' ≤
      xiWardPairedSourceRectangleRealEnergyAtLine
        (51 / 100) z₁ z₂ z₁' z₂' := by
  have hwide : 0 ≤
      xiWardPairedSourceRectangleRealEnergyAtLine
        (1051 / 100) z₁ z₂ z₁' z₂' := by
    unfold xiWardPairedSourceRectangleRealEnergyAtLine
    exact MeasureTheory.integral_nonneg fun t => sq_nonneg _
  unfold xiWardPairedSourceRectangleAnnulusEnergy
  linarith

/-- Exact source-side sandwich for the ten-unit Ward annulus.  Its lower
sign follows from Poisson dissipation; its upper side is the literal narrow
Euler--Gamma--von-Mangoldt rectangle energy. -/
theorem xiWardPairedSourceRectangleAnnulusEnergy_mem_Icc_of_samePacket
    (S : Finset XiRightUpperZeroCopy) (z₁ z₂ z₁' z₂' : ℂ)
    (hnarrow : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q
          (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)))
    (hwide : ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ)) z₁ z₂ z₁' z₂' =
        ∑ q ∈ S, xiAntiCausalWardSchwarzPairResponse q
          (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ))) :
    xiWardPairedSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' ∈
      Set.Icc 0
        (xiWardPairedSourceRectangleRealEnergyAtLine
          (51 / 100) z₁ z₂ z₁' z₂') := by
  constructor
  · rw [xiWardPairedSourceRectangleAnnulusEnergy,
      xiWardPairedSourceRectangleRealEnergyAtLine_eq_finite
        (51 / 100) S z₁ z₂ z₁' z₂' hnarrow,
      xiWardPairedSourceRectangleRealEnergyAtLine_eq_finite
        (1051 / 100) S z₁ z₂ z₁' z₂' hwide]
    exact xiWardFinitePairRealEnergyAtLine_fiftyOne_sub_tenShift_nonneg S
  · exact xiWardPairedSourceRectangleAnnulusEnergy_le_narrow z₁ z₂ z₁' z₂'

end

end RHTower
