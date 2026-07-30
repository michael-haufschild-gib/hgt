import GaloisForLFunctions.RHTower.EulerPositiveFisherHilbertLift
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour

/-!
# The complementary-record bridge from positive Euler Fisher transport to the Xi Ward column

The positive full-Euler Fisher tangent reaches the completed Xi logarithmic trace on the safe
Euler half-plane.  The anti-causal Ward column is not that full trace: it is the strict-right
Wiener--Hopf component together with its canonical boundary self-symbol.

This file proves the exact bridge.  Reflection moves the safe Euler trace to the Ward chart, and
the non-right canonical product is the complementary record that must be subtracted.  Thus the
Ward column is forced by the positive Euler transport only after the complementary divisor
channel is retained.
-/

open Complex

namespace RHTower

noncomputable section

/-- On every safe positive-Euler ray, the Hilbert-source transport is the centered Xi
logarithmic derivative, not merely an independently named continuation. -/
theorem eulerPositiveGammaXiWardHilbertTransportAt_eq_logDeriv_XiC
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositiveGammaXiWardHilbertTransportAt sigma u hsigma hu =
      logDeriv XiC
        (xiWardCenteredCoordinate
          (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)) := by
  let s : ℂ := (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)
  let z : ℂ := xiWardCenteredCoordinate s
  have hs : 1 < s.re := by
    dsimp only [s]
    simp only [ofReal_re]
    exact one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hcoord : 1 / 2 + z * I = s :=
    xiWardCenteredCoordinate_source s
  have hsource :
      continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (by rw [hcoord]; linarith) (by rw [hcoord]; exact hs1)
      (by rw [hcoord]; exact hzeta)]
    symm
    exact logDeriv_XiC_eq_relativeResolventTrace
      (XiC_ne_zero_of_continuedPrimeArch_domain
        (by rw [hcoord]; linarith) (by rw [hcoord]; exact hs1)
        (by rw [hcoord]; exact hzeta))
  rw [eulerPositiveGammaXiWardHilbertTransportAt_eq_continuedSource
    hsigma hu]
  simpa only [s, z] using hsource

/-- **Euler--Ward complementary-record law.**  On every safe positive-Euler ray, reflection
transports the positive Fisher coefficient to the full Xi trace in the Ward chart.  The
anti-causal Ward response is that reflected trace minus the non-right Wiener--Hopf logarithmic
derivative, plus the canonical boundary self-symbol. -/
theorem continuedXiAntiCausalWardResponse_eq_eulerFisherTransport_sub_complement
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    let s := eulerPositiveCriticalBoundaryParameter sigma u
    let w : ℂ := ((s - 1 / 2 : ℝ) : ℂ)
    continuedXiAntiCausalWardResponse w =
      -2 * I *
          eulerPositiveGammaXiWardHilbertTransportAt sigma u hsigma hu -
        2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
        xiAntiCausalWardBoundarySelfSymbol := by
  dsimp only
  let s : ℝ := eulerPositiveCriticalBoundaryParameter sigma u
  let w : ℂ := ((s - 1 / 2 : ℝ) : ℂ)
  let z : ℂ := xiWardCenteredCoordinate (s : ℂ)
  have hs : 1 < s :=
    one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  have hcoord : z = -(I * w) := by
    dsimp only [z, w, s]
    rw [xiWardCenteredCoordinate]
    push_cast
    ring
  have hzneg : XiC (-(I * w)) ≠ 0 := by
    rw [← hcoord]
    apply XiC_ne_zero_of_one_lt_centered_re
    rw [xiWardCenteredCoordinate_source]
    simpa only [ofReal_re] using hs
  have hzpos : XiC (I * w) ≠ 0 := by
    simpa only [XiC_even] using hzneg
  rw [continuedXiAntiCausalWardResponse_eq_logDeriv_XiC_sub hzpos,
    logDeriv_xiHadamardQuotient_eq_zero, mul_zero, sub_zero]
  change
    2 * I * logDeriv XiC (I * w) -
          2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
          xiAntiCausalWardBoundarySelfSymbol =
      -2 * I *
          eulerPositiveGammaXiWardHilbertTransportAt sigma u hsigma hu -
        2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
        xiAntiCausalWardBoundarySelfSymbol
  have hodd := logDeriv_XiC_neg (I * w)
  have htransport :=
    eulerPositiveGammaXiWardHilbertTransportAt_eq_logDeriv_XiC
      hsigma hu
  have htransportZ :
      eulerPositiveGammaXiWardHilbertTransportAt sigma u hsigma hu =
        logDeriv XiC z := by
    simpa only [z, s] using htransport
  rw [hcoord] at htransportZ
  rw [← htransportZ] at hodd
  linear_combination 2 * I * hodd

end

end RHTower
