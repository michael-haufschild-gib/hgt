import GaloisForLFunctions.RHTower.FrankensteinEulerMobiusSoninCriticalNormalBridge
import GaloisForLFunctions.RHTower.MobiusFixedCurrentVonMangoldt
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.RHTower.ZetaFisherVariance

/-!
# Euler--Möbius--Sonin safe-chamber critical order

This module removes the fixed-base defect from the existing shared Ward bridge.  At every real
Euler base `sigma > 1`, use the literal critical slope `epsilon = sigma - 1`.  The corresponding
Euler Ward curvature is

`-2 * (sigma - 1)^(2 : ℕ) * deriv infinitePrimeFlux sigma`.

It is strictly positive throughout the Euler chamber and tends to the nonzero value `2` as the
base reaches the critical wall.  The same unfrozen affine source lands in exactly the completed
trace reached by the bilateral Möbius replicas and by a cofinal Sonin family.  Thus one
pre-divisor theorem retains `ORD + ORIENT + COF + LAND`; its order is not lost under critical
normalization.

No order is transported through the singular affine correction here.  That remaining descent is
the RH-bearing step.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Strict positivity of the differentiated Euler current at every real safe base. -/
theorem neg_deriv_infinitePrimeFlux_ofReal_re_pos
    {sigma : ℝ} (hsigma : 1 < sigma) :
    0 < (-deriv infinitePrimeFlux (sigma : ℂ)).re := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : infinitePrimeFlux =ᶠ[nhds (sigma : ℂ)]
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    filter_upwards [hopen.mem_nhds (by simpa using hsigma)] with s hs
    exact infinitePrimeFlux_eq_vonMangoldtLSeries hs
  have hsum := GaloisForLFunctions.HTGeometry.summable_vonMangoldt_logMul_rpow
    (σ := sigma) hsigma
  have hterm : 0 < (Real.log 2 * (ArithmeticFunction.vonMangoldt 2 : ℝ)) *
      (2 : ℝ) ^ (-sigma) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    positivity
  have hnonneg : ∀ n : ℕ, 0 ≤
      (Real.log n * (ArithmeticFunction.vonMangoldt n : ℝ)) *
        (n : ℝ) ^ (-sigma) := by
    intro n
    exact mul_nonneg
      (mul_nonneg (Real.log_natCast_nonneg n) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hpos : 0 < ∑' n : ℕ,
      (Real.log n * (ArithmeticFunction.vonMangoldt n : ℝ)) *
        (n : ℝ) ^ (-sigma) := by
    have hle := hsum.le_tsum 2 (fun n _ => hnonneg n)
    exact lt_of_lt_of_le (by simpa using hterm) hle
  have hmoment := GaloisForLFunctions.HTGeometry.ofReal_tsum_vonMangoldt_logMul_eq
    (σ := sigma) hsigma
  have hderivEq : deriv infinitePrimeFlux (sigma : ℂ) =
      deriv (LSeries fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ) :=
    heq.deriv_eq
  rw [hderivEq]
  have hneg :
      -deriv (LSeries fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ) =
        ((∑' n : ℕ, (Real.log n * (ArithmeticFunction.vonMangoldt n : ℝ)) *
          (n : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
    simpa using hmoment.symm
  rw [hneg]
  simpa using hpos

/-- The safe affine Ward curvature at arbitrary real base and unit slope. -/
theorem eulerAffineFisherScore_deriv_real_one_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    deriv (eulerAffineFisherScore (sigma : ℂ) 1) 0 =
      -2 * deriv infinitePrimeFlux (sigma : ℂ) := by
  have hflux : DifferentiableAt ℂ infinitePrimeFlux (sigma : ℂ) := by
    unfold infinitePrimeFlux
    rw [show (fun z => -logDeriv riemannZeta z) =
        fun z => -deriv riemannZeta z / riemannZeta z by
      funext z
      rw [logDeriv_apply]
      ring]
    exact differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
      (s := (sigma : ℂ)) (by simpa using hsigma)
  have hshift : HasDerivAt (fun u : ℂ => infinitePrimeFlux ((sigma : ℂ) + u))
      (deriv infinitePrimeFlux (sigma : ℂ)) 0 := by
    apply HasDerivAt.comp_const_add (sigma : ℂ) 0
    simpa using hflux.hasDerivAt
  have hdiff : HasDerivAt
      (fun u : ℂ => infinitePrimeFlux (sigma : ℂ) -
        infinitePrimeFlux ((sigma : ℂ) + u))
      (-deriv infinitePrimeFlux (sigma : ℂ)) 0 := by
    exact HasDerivAt.const_sub (infinitePrimeFlux (sigma : ℂ)) hshift
  have hzeta : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  have hoverlap : DifferentiableAt ℂ
      (eulerAffineBoundaryOverlap (sigma : ℂ) 1) 0 := by
    have hzetaDeriv : HasDerivAt riemannZeta (deriv riemannZeta (sigma : ℂ))
        ((sigma : ℂ) + 0) := by
      simpa using
        (differentiableAt_riemannZeta (by
          intro h
          have hre := congrArg Complex.re h
          norm_num at hre
          linarith)).hasDerivAt
    have hq :=
      (HasDerivAt.comp_const_add (sigma : ℂ) 0 hzetaDeriv).div_const
        (riemannZeta (sigma : ℂ))
    have heq : eulerAffineBoundaryOverlap (sigma : ℂ) 1 =
        fun u : ℂ => riemannZeta ((sigma : ℂ) + u) / riemannZeta (sigma : ℂ) := by
      funext u
      simp [eulerAffineBoundaryOverlap]
    rw [heq]
    exact hq.differentiableAt
  have hg : HasDerivAt
      (fun u : ℂ => 2 * (eulerAffineBoundaryOverlap (sigma : ℂ) 1 u *
        (infinitePrimeFlux (sigma : ℂ) - infinitePrimeFlux ((sigma : ℂ) + u))))
      (-2 * deriv infinitePrimeFlux (sigma : ℂ)) 0 := by
    have hmul := hoverlap.hasDerivAt.mul hdiff
    have hzero : infinitePrimeFlux (sigma : ℂ) -
        infinitePrimeFlux ((sigma : ℂ) + (0 : ℂ)) = 0 := by ring
    have hone : eulerAffineBoundaryOverlap (sigma : ℂ) 1 0 = 1 := by
      simp [eulerAffineBoundaryOverlap, hzeta]
    have hscaled := hmul.const_mul (2 : ℂ)
    have hderiv : -2 * deriv infinitePrimeFlux (sigma : ℂ) =
        2 * (deriv (eulerAffineBoundaryOverlap (sigma : ℂ) 1) 0 *
          (infinitePrimeFlux (sigma : ℂ) - infinitePrimeFlux ((sigma : ℂ) + 0)) +
          eulerAffineBoundaryOverlap (sigma : ℂ) 1 0 *
            -deriv infinitePrimeFlux (sigma : ℂ)) := by
      rw [hzero, hone]
      ring
    rw [hderiv]
    exact hscaled
  have hopen : IsOpen {u : ℂ | 1 < ((sigma : ℂ) + u).re} :=
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_const.add continuous_id))
  have heq : eulerAffineFisherScore (sigma : ℂ) 1 =ᶠ[nhds 0]
      fun u : ℂ => 2 * (eulerAffineBoundaryOverlap (sigma : ℂ) 1 u *
        (infinitePrimeFlux (sigma : ℂ) - infinitePrimeFlux ((sigma : ℂ) + u))) := by
    filter_upwards [hopen.mem_nhds (by simpa using hsigma)] with u hu
    rw [eulerAffineFisherScore_eq_current_difference
      (sigma := (sigma : ℂ)) (epsilon := 1) (u := u)
      (by simpa using hsigma) (by simpa using hu)]
    ring
  rw [heq.deriv_eq]
  exact hg.deriv

/-- Exact critical-slope covariance of the safe affine Ward curvature. -/
theorem eulerAffineFisherScore_deriv_real_sub_one_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    deriv (eulerAffineFisherScore (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0 =
      -2 * (((sigma - 1 : ℝ) : ℂ) ^ 2) *
        deriv infinitePrimeFlux (sigma : ℂ) := by
  let epsilon : ℂ := ((sigma - 1 : ℝ) : ℂ)
  have hopen : IsOpen {u : ℂ | 1 < ((sigma : ℂ) + u * epsilon).re} :=
    isOpen_lt continuous_const
      (Complex.continuous_re.comp
        (continuous_const.add (continuous_id.mul continuous_const)))
  have heq : eulerAffineFisherScore (sigma : ℂ) epsilon =ᶠ[nhds 0]
      fun u : ℂ => epsilon •
        eulerAffineFisherScore (sigma : ℂ) 1 (epsilon * u) := by
    filter_upwards [hopen.mem_nhds (by simpa using hsigma)] with u hu
    rw [eulerAffineFisherScore_eq_current_difference
      (sigma := (sigma : ℂ)) (epsilon := epsilon) (u := u)
      (by simpa using hsigma) (by simpa using hu),
      eulerAffineFisherScore_eq_current_difference
        (sigma := (sigma : ℂ)) (epsilon := 1) (u := epsilon * u)
        (by simpa using hsigma) (by simpa [mul_comm, mul_left_comm, mul_assoc] using hu)]
    rw [show epsilon * u = u * epsilon by ring]
    simp only [smul_eq_mul, eulerAffineBoundaryOverlap]
    ring
  change deriv (eulerAffineFisherScore (sigma : ℂ) epsilon) 0 = _
  rw [heq.deriv_eq]
  rw [deriv_fun_const_smul_field, deriv_comp_mul_left]
  simp only [smul_eq_mul, mul_zero]
  rw [eulerAffineFisherScore_deriv_real_one_zero hsigma]
  ring

/-- Critical-slope Ward order is strict at every safe base. -/
theorem eulerAffineFisherScore_deriv_real_sub_one_zero_re_pos
    {sigma : ℝ} (hsigma : 1 < sigma) :
    0 < (deriv
      (eulerAffineFisherScore (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0).re := by
  rw [eulerAffineFisherScore_deriv_real_sub_one_zero hsigma]
  have hflux := neg_deriv_infinitePrimeFlux_ofReal_re_pos hsigma
  have hepsilon : 0 < sigma - 1 := sub_pos.mpr hsigma
  have hepsilon_sq : 0 < (sigma - 1) ^ 2 := sq_pos_of_pos hepsilon
  norm_num [Complex.mul_re, pow_two] at hflux ⊢
  nlinarith

/-- The critical-slope Ward order has nonzero normalized boundary value `2`. -/
theorem tendsto_eulerAffineFisherScore_deriv_real_sub_one_zero :
    Tendsto (fun sigma : ℝ =>
      deriv (eulerAffineFisherScore (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0)
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
  have hcurrent : infinitePrimeFlux = vonMangoldtCurrent := by
    funext s
    simp only [infinitePrimeFlux, vonMangoldtCurrent, logDeriv_apply]
    ring
  have hresidue := tendsto_sub_one_sq_mul_deriv_vonMangoldtCurrent.comp
    tendsto_ofReal_nhdsWithin_ne_one
  rw [← hcurrent] at hresidue
  have hscaled := hresidue.const_mul (-2 : ℂ)
  have hscaled' : Tendsto (fun sigma : ℝ =>
      (-2 : ℂ) * (((sigma : ℂ) - 1) ^ 2 *
        deriv infinitePrimeFlux (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  rw [eulerAffineFisherScore_deriv_real_sub_one_zero hsigma]
  push_cast
  ring

/-! ## Identification with the literal positive Euler Hilbert source -/

theorem eulerPositiveTotal_eq_eulerMass (sigma : ℝ) :
    eulerPositiveTotal sigma = eulerMass sigma := by
  rw [eulerPositiveTotal, eulerMass]
  exact tsum_congr fun n => rfl

theorem eulerPositiveLogMoment_eq_eulerLogPowMass_div
    (k : ℕ) (sigma : ℝ) :
    eulerPositiveLogMoment k sigma =
      eulerLogPowMass k sigma / eulerMass sigma := by
  rw [eulerPositiveLogMoment, eulerLogPowMass, ← tsum_div_const]
  apply tsum_congr
  intro n
  rw [eulerPositiveProbability, eulerPositiveMass,
    eulerPositiveTotal_eq_eulerMass]
  ring

/-- Direct positive-Euler and Bohr-Gibbs charts have the same logarithmic variance. -/
theorem eulerPositiveLogVariance_eq_eulerLogVariance
    (sigma : ℝ) :
    eulerPositiveLogMoment 2 sigma - eulerPositiveLogMoment 1 sigma ^ 2 =
      eulerLogVariance sigma := by
  rw [eulerPositiveLogMoment_eq_eulerLogPowMass_div,
    eulerPositiveLogMoment_eq_eulerLogPowMass_div]
  simp only [eulerLogVariance, eulerLogMean, eulerLogPowMass_one]

/-- The positive derivative of the prime flux is exactly the zeta Fisher metric. -/
theorem neg_deriv_infinitePrimeFlux_eq_zetaFisherMetric
    {sigma : ℝ} (hsigma : 1 < sigma) :
    -deriv infinitePrimeFlux (sigma : ℂ) =
      zetaFisherMetric (sigma : ℂ) := by
  have hneg : DifferentiableAt ℂ
      (fun z : ℂ => -logDeriv riemannZeta z) (sigma : ℂ) := by
    rw [show (fun z : ℂ => -logDeriv riemannZeta z) =
        fun z => -deriv riemannZeta z / riemannZeta z by
      funext z
      rw [logDeriv_apply]
      ring]
    exact differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
      (s := (sigma : ℂ)) (by simpa using hsigma)
  have hlog : DifferentiableAt ℂ (logDeriv riemannZeta) (sigma : ℂ) := by
    simpa using hneg.neg
  have hderivNeg :
      deriv (fun z : ℂ => -logDeriv riemannZeta z) (sigma : ℂ) =
        -deriv (logDeriv riemannZeta) (sigma : ℂ) :=
    hlog.hasDerivAt.neg.deriv
  unfold infinitePrimeFlux zetaFisherMetric
  rw [hderivNeg]
  ring

/-- The critical-slope Ward curvature is twice the literal Gibbs variance. -/
theorem eulerCriticalSlopeWardCurvature_re_eq_two_mul_variance
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (deriv
      (eulerAffineFisherScore (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0).re =
      2 * (sigma - 1) ^ 2 * eulerLogVariance sigma := by
  rw [eulerAffineFisherScore_deriv_real_sub_one_zero hsigma]
  have hmetric := neg_deriv_infinitePrimeFlux_eq_zetaFisherMetric hsigma
  have hderiv : deriv infinitePrimeFlux (sigma : ℂ) =
      -zetaFisherMetric (sigma : ℂ) := by
    linear_combination -hmetric
  rw [hderiv, zetaFisherMetric_ofReal_eq_eulerLogVariance hsigma]
  norm_num [Complex.mul_re, pow_two]

/-- **Physical order identity.**  Pointwise before the critical limit, the norm-square of the
actual positive-integer Fisher tangent is exactly twice the transported affine Ward curvature. -/
theorem norm_eulerPositiveCriticalFisherTangentLp_sq_eq_two_mul_curvature
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositiveCriticalFisherTangentLp sigma hsigma‖ ^ 2 =
      2 * (deriv
        (eulerAffineFisherScore (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0).re := by
  rw [norm_eulerPositiveCriticalFisherTangentLp_sq hsigma,
    eulerPositiveCriticalProjectiveFisherEnergy,
    eulerPositiveLogVariance_eq_eulerLogVariance,
    eulerCriticalSlopeWardCurvature_re_eq_two_mul_variance hsigma]
  ring

/-- **Same-source `ORD + LAND` Hilbert producer.**  The strict Ward order is the norm-square of
the literal positive-integer Fisher tangent; that same tangent reports the affine Euler
coefficient against the actual damped state, and its Gamma--Xi transport is the completed source
trace.  No scalar coefficient is inserted after leaving the Hilbert carrier. -/
theorem eulerPositiveCriticalFisherOrderLanding_producer
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    0 < (deriv
        (eulerAffineFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0).re ∧
      ‖eulerPositiveCriticalFisherTangentLp sigma hsigma‖ ^ 2 =
        2 * (deriv
          (eulerAffineFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0).re ∧
      inner ℂ
          (eulerPositiveCriticalFisherTangentLp sigma hsigma)
          (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
        eulerAffineFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) ∧
      eulerPositiveGammaXiWardHilbertTransportAt sigma u hsigma hu =
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)) := by
  exact ⟨eulerAffineFisherScore_deriv_real_sub_one_zero_re_pos hsigma,
    norm_eulerPositiveCriticalFisherTangentLp_sq_eq_two_mul_curvature hsigma,
    inner_eulerPositiveFisherTangent_dampedState_eq_affineScore hsigma hu,
    eulerPositiveGammaXiWardHilbertTransportAt_eq_continuedSource hsigma hu⟩

/-- **`ORD + ORIENT + COF + LAND` source producer.**  At every safe base, the literal
critical-slope Euler family has strict order and lands in the same completed trace as both
Möbius orientations and a cofinal Sonin incidence.  Its order converges to `2` at the critical
wall rather than disappearing. -/
theorem eulerMobiusSonin_safeChamberCriticalOrder_producer
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    Tendsto (fun sigma : ℝ =>
      deriv (eulerAffineFisherScore (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0)
        (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) ∧
      ∀ sigma : ℝ, ∀ hsigma : 1 < sigma,
        0 < (deriv
          (eulerAffineFisherScore (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0).re ∧
        ‖eulerPositiveCriticalFisherTangentLp sigma hsigma‖ ^ 2 =
          2 * (deriv
            (eulerAffineFisherScore
              (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) 0).re ∧
        ∀ u : ℝ, ∀ hu : -(1 / 2 : ℝ) < u,
          ∃ depth : ℕ → ℕ, StrictMono depth ∧
            eulerAffineGammaXiWardTransportV
                (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
                (eulerAffineFisherScore
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) (u : ℂ) =
              continuedPrimeArchSourceRelativeTrace
                (xiWardCenteredCoordinate
                  (mobiusCriticalBoundaryParameter sigma u : ℂ)) ∧
            Tendsto
              (fun k : ℕ =>
                squarefreeMobiusCofinalReplicaGammaXiWardTransportV
                  (k + 1) sigma u)
              atTop
              (𝓝 (eulerAffineGammaXiWardTransportV
                (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
                (eulerAffineFisherScore
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) (u : ℂ))) ∧
            Tendsto (fun n =>
              soninCofinalMobiusGammaXiWardFixedEulerTransport
                  a c d r hc hcd hr
                  (mobiusCriticalBoundaryParameter sigma u)
                  (by
                    unfold mobiusCriticalBoundaryParameter
                    have hσ : 0 < sigma - 1 := sub_pos.mpr hsigma
                    have hu1 : 0 < 1 + u := by linarith
                    nlinarith [mul_pos hσ hu1]) depth n -
                eulerAffineGammaXiWardTransportV
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
                  (eulerAffineFisherScore
                    (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) (u : ℂ))
              atTop (𝓝 0) := by
  refine ⟨tendsto_eulerAffineFisherScore_deriv_real_sub_one_zero, ?_⟩
  intro sigma hsigma
  refine ⟨eulerAffineFisherScore_deriv_real_sub_one_zero_re_pos hsigma,
    norm_eulerPositiveCriticalFisherTangentLp_sq_eq_two_mul_curvature hsigma, ?_⟩
  intro u hu
  have hσ : 0 < sigma - 1 := sub_pos.mpr hsigma
  have hu1 : 0 < 1 + u := by linarith
  have htarget : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith [mul_pos hσ hu1]
  have hcoord :
      (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) =
        (mobiusCriticalBoundaryParameter sigma u : ℂ) := by
    unfold mobiusCriticalBoundaryParameter
    push_cast
    ring
  have hepsilon : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hσ
  have hshift :
      1 < ((sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ)).re := by
    rw [hcoord]
    simpa using htarget
  have hEuler := eulerAffineGammaXiWardTransportV_eq_continuedSource
    (sigma := (sigma : ℂ)) (epsilon := ((sigma - 1 : ℝ) : ℂ)) (u := (u : ℂ))
    (by simpa using hsigma) hshift hepsilon
  rw [hcoord] at hEuler
  have hMobius : Tendsto
      (fun k : ℕ =>
        squarefreeMobiusCofinalReplicaGammaXiWardTransportV (k + 1) sigma u)
      atTop
      (𝓝 (eulerAffineGammaXiWardTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (eulerAffineFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)) (u : ℂ))) := by
    rw [hEuler]
    exact bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaXiWardTransportV
      hsigma hu
  rcases exists_soninCofinalMobiusGammaXiWardFixedEulerTransport
      a c d r ha hc hcd hda hr harc
      (mobiusCriticalBoundaryParameter sigma u) htarget with
    ⟨depth, hdepth, hSonin⟩
  refine ⟨depth, hdepth, hEuler, hMobius, ?_⟩
  rw [hEuler]
  exact hSonin

end

end RHTower
