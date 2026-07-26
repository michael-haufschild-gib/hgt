import GaloisForLFunctions.RHTower.EulerSquarefreeAffineFisherCutoffWard
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardJuliaTransport
import GaloisForLFunctions.RHTower.ZetaDerivDirichlet

open Complex Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section
namespace RHTower

theorem ofReal_eulerSquareResidualLogMoment_one_eq_infinitePrimeFlux
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (eulerSquareResidualLogMoment 1 sigma : ℂ) =
      infinitePrimeFlux ((2 * sigma : ℝ) : ℂ) := by
  have hsum :=
    summable_eulerSquareResidualLogMoment 1 hsigma
  have htotal : eulerSquareResidualTotal sigma ≠ 0 :=
    (eulerSquareResidualTotal_pos hsigma).ne'
  have htotalC : (eulerSquareResidualTotal sigma : ℂ) ≠ 0 := by
    exact_mod_cast htotal
  have hzeta :
      riemannZeta ((2 * sigma : ℝ) : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  rw [eulerSquareResidualLogMoment, Complex.ofReal_tsum]
  rw [show (fun n : ℕ =>
      ((eulerSquareResidualProbability sigma n *
        Real.log n ^ 1 : ℝ) : ℂ)) =
      fun n : ℕ =>
        ((Real.log n : ℝ) : ℂ) /
          (n : ℂ) ^ ((2 * sigma : ℝ) : ℂ) /
            (eulerSquareResidualTotal sigma : ℂ) by
    funext n
    rw [eulerSquareResidualProbability, Complex.ofReal_mul,
      Complex.ofReal_div, pow_one,
      ofReal_eulerSquareResidualMass_eq hsigma]
    ring]
  rw [tsum_div_const]
  rw [← neg_neg (∑' n : ℕ,
      (Real.log n : ℂ) / (n : ℂ) ^ ((2 * sigma : ℝ) : ℂ)),
    ← GaloisForLFunctions.zeta_deriv_eq_neg_tsum
      (by simp; linarith : 1 < (((2 * sigma : ℝ) : ℂ)).re)]
  rw [ofReal_eulerSquareResidualTotal_eq_zeta hsigma]
  simp only [infinitePrimeFlux, logDeriv_apply]
  ring

theorem affineEulerFixedCurrent_eq_infinitePrimeFlux
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (squarefreeMobiusLogMoment 1 sigma : ℂ) +
        2 * (eulerSquareResidualLogMoment 1 sigma : ℂ) =
      infinitePrimeFlux (sigma : ℂ) := by
  rw [ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hsigma,
    ofReal_eulerSquareResidualLogMoment_one_eq_infinitePrimeFlux hsigma]
  simp only [GaloisForLFunctions.squarefreeFixedCurrent]
  push_cast
  ring

/-- Full positive-Euler overlap, before any divisor continuation. -/
def eulerAffineBoundaryOverlap
    (sigma epsilon u : ℂ) : ℂ :=
  riemannZeta (sigma + u * epsilon) / riemannZeta sigma

/-- Full-Euler pointed Fisher numerator. -/
def eulerAffineFisherScore
    (sigma epsilon u : ℂ) : ℂ :=
  2 * (deriv (eulerAffineBoundaryOverlap sigma epsilon) u +
    epsilon * infinitePrimeFlux sigma *
      eulerAffineBoundaryOverlap sigma epsilon u)

theorem deriv_eulerAffineBoundaryOverlap_eq_neg_mul_current
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) :
    deriv (eulerAffineBoundaryOverlap sigma epsilon) u =
      -epsilon * eulerAffineBoundaryOverlap sigma epsilon u *
        infinitePrimeFlux (sigma + u * epsilon) := by
  have hden : riemannZeta sigma ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsigma
  have hnum : riemannZeta (sigma + u * epsilon) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hshift
  have hs1 : sigma + u * epsilon ≠ 1 := by
    intro h
    rw [h] at hshift
    norm_num at hshift
  have houter : HasDerivAt riemannZeta
      (deriv riemannZeta (sigma + u * epsilon))
      (sigma + u * epsilon) :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hinner : HasDerivAt (fun v : ℂ => sigma + v * epsilon)
      epsilon u := by
    convert (hasDerivAt_const (x := u) (c := sigma)).add
      ((hasDerivAt_id u).mul_const epsilon) using 1
    all_goals ring
  have hcomp :
      HasDerivAt (fun v : ℂ => riemannZeta (sigma + v * epsilon))
        (deriv riemannZeta (sigma + u * epsilon) * epsilon) u :=
    houter.comp u hinner
  have hquot := hcomp.div_const (riemannZeta sigma)
  change deriv
      (fun v : ℂ => riemannZeta (sigma + v * epsilon) /
        riemannZeta sigma) u = _
  rw [hquot.deriv]
  simp only [eulerAffineBoundaryOverlap, infinitePrimeFlux, logDeriv_apply]
  field_simp [hden, hnum]

theorem eulerAffineFisherScore_eq_current_difference
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) :
    eulerAffineFisherScore sigma epsilon u =
      2 * epsilon * eulerAffineBoundaryOverlap sigma epsilon u *
        (infinitePrimeFlux sigma -
          infinitePrimeFlux (sigma + u * epsilon)) := by
  rw [eulerAffineFisherScore,
    deriv_eulerAffineBoundaryOverlap_eq_neg_mul_current hsigma hshift]
  ring

/-- Singular graph transport of the intrinsic all-Euler Fisher numerator. -/
def eulerAffineGammaCurrentTransportV
    (sigma epsilon : ℂ) (score : ℂ → ℂ) (u : ℂ) : ℂ :=
  2 * infinitePrimeFlux sigma -
    score u / (epsilon * eulerAffineBoundaryOverlap sigma epsilon u) -
    2 * logDeriv archFactor (sigma + u * epsilon)

theorem eulerAffineGammaCurrentTransportV_eq_two_seamFlux
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re)
    (hepsilon : epsilon ≠ 0) :
    eulerAffineGammaCurrentTransportV sigma epsilon
        (eulerAffineFisherScore sigma epsilon) u =
      2 * seamFluxCochain (sigma + u * epsilon) := by
  have hoverlap : eulerAffineBoundaryOverlap sigma epsilon u ≠ 0 :=
    div_ne_zero
      (riemannZeta_ne_zero_of_one_lt_re hshift)
      (riemannZeta_ne_zero_of_one_lt_re hsigma)
  rw [eulerAffineGammaCurrentTransportV,
    eulerAffineFisherScore_eq_current_difference hsigma hshift,
    seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hshift]
  field_simp [hepsilon, hoverlap]
  ring

/-- Intrinsic all-Euler transport into the continued Xi trace. -/
def eulerAffineGammaXiWardTransportV
    (sigma epsilon : ℂ) (score : ℂ → ℂ) (u : ℂ) : ℂ :=
  (-I / 2) *
    eulerAffineGammaCurrentTransportV sigma epsilon score u

theorem eulerAffineGammaXiWardTransportV_eq_continuedSource
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re)
    (hepsilon : epsilon ≠ 0) :
    eulerAffineGammaXiWardTransportV sigma epsilon
        (eulerAffineFisherScore sigma epsilon) u =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate (sigma + u * epsilon)) := by
  rw [eulerAffineGammaXiWardTransportV,
    eulerAffineGammaCurrentTransportV_eq_two_seamFlux
      hsigma hshift hepsilon]
  have hsource :=
    continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction
      (xiWardCenteredCoordinate (sigma + u * epsilon))
  rw [xiWardCenteredCoordinate_source] at hsource
  have hcompletion :=
    GaloisForLFunctions.completedXi_sub_completedSquarefree_eq_four_mul_infinitePrimeFlux_two
      hshift
  rw [hsource]
  linear_combination (-I / 2) * hcompletion

end RHTower
