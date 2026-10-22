import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaResolventLogJet
import GaloisForLFunctions.RHTower.XiMassCriticalSafeEulerGreenWeld

/-!
# Phase-linear weld between the theta resolvent and the Route T mass current

On every legal Euler bottom line, the von Mangoldt Dirichlet series is exactly the
archimedean logarithmic derivative minus the pinned quantile-coordinate row of the fixed theta
source resolvent.  Integrating against the analytic Xi-mass test therefore expresses Route T's
complete prime current as an archimedean face minus one unsquared theta-resolvent wave packet.

The archimedean face is already uniformly bounded.  Hence height-uniform boundedness of this one
phase-linear theta wave packet is equivalent to RH.  No norm, determinant weight, or polarization
is inserted before the exact source identity.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Xi-mass test paired pointwise with the phase-sensitive theta quantile resolvent row. -/
def xiMassThetaQuantileResolventIntegrand
    (a c : ℝ) (tau : ℂ) (x : ℝ) : ℂ :=
  xiMassBottomTest a c tau x *
    pinnedMean
      (thetaComplexResolvent (thetaEsscherResolventParameter c (-x))
        thetaQuantileCoordinate)

/-- Complete phase-linear theta-resolvent wave packet on a legal Euler bottom line. -/
def xiMassThetaQuantileResolventIntegral (a c : ℝ) (tau : ℂ) : ℂ :=
  ∫ x : ℝ, xiMassThetaQuantileResolventIntegrand a c tau x

/-- The bottom Euler coordinate is the centered coordinate of the exterior theta pencil. -/
theorem xiMassBottomEulerPoint_eq_centered_thetaEsscherParameter
    (c x : ℝ) :
    xiMassBottomEulerPoint c x =
      1 / 2 + thetaEsscherResolventParameter c (-x) * Complex.I := by
  rw [xiMassBottomEulerPoint, thetaEsscherResolventParameter]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Pointwise phase-linear weld.**  The literal von Mangoldt series on every legal Euler line is
the archimedean row minus the pinned quantile-coordinate row of the fixed theta resolvent. -/
theorem LSeries_vonMangoldt_eq_arch_sub_thetaQuantileResolventRow
    {c : ℝ} (hhalf : 1 / 2 < c) (x : ℝ) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (xiMassBottomEulerPoint c x) =
      logDeriv archFactor (xiMassBottomEulerPoint c x) -
        pinnedMean
          (thetaComplexResolvent (thetaEsscherResolventParameter c (-x))
            thetaQuantileCoordinate) := by
  let z : ℂ := thetaEsscherResolventParameter c (-x)
  have hcabs : 1 / 2 ≤ |c| := by
    rw [abs_of_pos (lt_trans (by norm_num) hhalf)]
    exact hhalf.le
  have hpencil : IsUnit (thetaSourcePencil z) := by
    exact isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs
      hcabs (-x)
  have hXi : XiC z ≠ 0 := by
    intro hzero
    exact (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).2 hzero hpencil
  have hcoord : xiMassBottomEulerPoint c x = 1 / 2 + z * Complex.I := by
    dsimp only [z]
    exact xiMassBottomEulerPoint_eq_centered_thetaEsscherParameter c x
  have hs : 1 < (1 / 2 + z * Complex.I).re := by
    rw [← hcoord]
    simp only [xiMassBottomEulerPoint, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one]
    linarith
  have hsource : primeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hs,
      ← logDeriv_XiC_eq_relativeResolventTrace hXi]
  have hrow :=
    pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hpencil
  rw [hrow, ← hsource, primeArchSourceRelativeTrace, ← hcoord]
  rw [← mul_assoc]
  have hII : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
    rw [neg_mul_neg, Complex.I_mul_I]
  rw [hII]
  ring

/-- The theta wave-packet integrand is the archimedean bottom integrand minus the prime bottom
integrand.  This identity is pointwise, before integration or norms. -/
theorem xiMassThetaQuantileResolventIntegrand_eq_arch_sub_prime
    {a c : ℝ} (hhalf : 1 / 2 < c) (tau : ℂ) (x : ℝ) :
    xiMassThetaQuantileResolventIntegrand a c tau x =
      xiMassBottomArchIntegrand a c tau x -
        xiMassBottomPrimeIntegrand a c tau x := by
  rw [xiMassThetaQuantileResolventIntegrand, xiMassBottomArchIntegrand,
    xiMassBottomPrimeIntegrand,
    LSeries_vonMangoldt_eq_arch_sub_thetaQuantileResolventRow hhalf]
  ring

/-- The complete theta-resolvent wave packet is genuinely Bochner integrable. -/
theorem integrable_xiMassThetaQuantileResolventIntegrand
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    Integrable (xiMassThetaQuantileResolventIntegrand a c tau) := by
  have hfun : xiMassThetaQuantileResolventIntegrand a c tau =
      fun x => xiMassBottomArchIntegrand a c tau x -
        xiMassBottomPrimeIntegrand a c tau x := by
    funext x
    exact xiMassThetaQuantileResolventIntegrand_eq_arch_sub_prime hhalf tau x
  rw [hfun]
  exact (integrable_xiMassBottomArchIntegrand hhalf hca htau).sub
    (integrable_xiMassBottomPrimeIntegrand hhalf hca htau)

/-- **Integrated phase-linear weld.**  Route T's complete prime current is the uniformly bounded
archimedean face minus one unsquared fixed-theta resolvent wave packet. -/
theorem xiMassBottomPrimeIntegral_eq_arch_sub_thetaQuantileResolventIntegral
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    xiMassBottomPrimeIntegral a c tau =
      xiMassBottomArchIntegral a c tau -
        xiMassThetaQuantileResolventIntegral a c tau := by
  have harch := integrable_xiMassBottomArchIntegrand hhalf hca htau
  have hprime := integrable_xiMassBottomPrimeIntegrand hhalf hca htau
  have htheta := integrable_xiMassThetaQuantileResolventIntegrand hhalf hca htau
  have hpoint : (fun x => xiMassBottomArchIntegrand a c tau x -
      xiMassThetaQuantileResolventIntegrand a c tau x) =
      xiMassBottomPrimeIntegrand a c tau := by
    funext x
    rw [xiMassThetaQuantileResolventIntegrand_eq_arch_sub_prime hhalf]
    ring
  rw [xiMassBottomPrimeIntegral, xiMassBottomArchIntegral,
    xiMassThetaQuantileResolventIntegral, ← integral_sub harch htheta, hpoint]

/-- Height-uniform line bound for the phase-linear theta-resolvent mass wave packet. -/
def XiMassThetaQuantileResolventIntegralLineBound
    (a c sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassThetaQuantileResolventIntegral a c
      ((sigma : ℂ) + (u : ℂ) * Complex.I)‖ ≤ C

/-- Since the archimedean face is uniformly bounded, the theta wave-packet line bound is exactly
the existing Route T prime-current line bound. -/
theorem xiMassBottomPrimeIntegralLineBound_iff_thetaQuantileResolventIntegral
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    (∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassBottomPrimeIntegral a c
        ((sigma : ℂ) + (u : ℂ) * Complex.I)‖ ≤ C) ↔
      XiMassThetaQuantileResolventIntegralLineBound a c sigma := by
  let B : ℝ := xiMassBottomArchUniformBound a sigma
  have harch : ∀ u : ℝ,
      ‖xiMassBottomArchIntegral a c
        ((sigma : ℂ) + (u : ℂ) * Complex.I)‖ ≤ B := by
    intro u
    simpa only [B, xiMassBottomArchIntegral] using
      norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hsigma
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨B + C, fun u hu => ?_⟩
    have hweld := xiMassBottomPrimeIntegral_eq_arch_sub_thetaQuantileResolventIntegral
      hhalf hca (tau := ((sigma : ℂ) + (u : ℂ) * Complex.I)) (by simpa using hsigma)
    have hsolve : xiMassThetaQuantileResolventIntegral a c
        ((sigma : ℂ) + (u : ℂ) * Complex.I) =
      xiMassBottomArchIntegral a c ((sigma : ℂ) + (u : ℂ) * Complex.I) -
        xiMassBottomPrimeIntegral a c ((sigma : ℂ) + (u : ℂ) * Complex.I) := by
      linear_combination hweld
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (harch u) (hC u hu))
  · rintro ⟨C, hC⟩
    refine ⟨B + C, fun u hu => ?_⟩
    rw [xiMassBottomPrimeIntegral_eq_arch_sub_thetaQuantileResolventIntegral
      hhalf hca (by simpa using hsigma)]
    exact (norm_sub_le _ _).trans (add_le_add (harch u) (hC u hu))

/-- **Pure theta-resolvent Route T criterion.**  RH is equivalent to uniform boundedness of one
mass-weighted coherent superposition of safe exterior rows of the fixed theta source resolvent. -/
theorem riemannHypothesis_iff_xiMassThetaQuantileResolventIntegralLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      XiMassThetaQuantileResolventIntegralLineBound a c sigma := by
  exact (riemannHypothesis_iff_xiMassBottomPrimeIntegralLineBound
    hhalf hca hsigma).trans
      (xiMassBottomPrimeIntegralLineBound_iff_thetaQuantileResolventIntegral
        hhalf hca hsigma)

end

end RHTower
