import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestBoundaryTransgression

/-!
# Primitive-endpoint transport to the completed Xi source trace

The exact Gamma/Hardy boundary transgression retains enough arithmetic
information to reconstruct the completed Xi logarithmic source current on
the Euler half-plane.  No squarefree projection or divisor factor is used.

For `σ > 1`, let `Pσ(n)` be the normalized von-Mangoldt prime-power law and
let `ε = σ - 1`.  The endpoint character `n^(-ε a)` has expectation

`(-ζ'/ζ)(σ + ε a) / (-ζ'/ζ)(σ)`.

Multiplication by the source normalizing flux therefore recovers the full
prime current at `σ + ε a`.  Adding the fixed archimedean completion and
rotating to the centered Xi coordinate gives
`continuedPrimeArchSourceRelativeTrace` exactly.

The same expectation is the off-diagonal entry of a two-node endpoint
Green primitive.  Hence this is a literal observation of the relative
Gamma/Hardy boundary object constructed in
`EulerPrimitiveCommonTestBoundaryTransgression`, not an independently
inserted analytic continuation.

This closes transport to the *full* completed Xi source trace on the safe
half-plane.  Extracting its strict-right odd Ward component without the
divisor-fed complementary factor remains separate.
-/

open Complex

namespace RHTower

noncomputable section

/-- Safe Euler point selected by the pole-scale endpoint direction `a`. -/
def eulerPrimitiveBoundaryXiTracePoint
    (sigma : ℝ) (a : ℂ) : ℂ :=
  (sigma : ℂ) + ((sigma : ℂ) - 1) * a

/-- Literal normalized prime-power expectation of one endpoint character. -/
def eulerPrimitiveBoundaryEndpointExpectation
    (sigma : ℝ) (a : ℂ) : ℂ :=
  ∑' n : ℕ,
    (eulerPrimeCurrentProbability sigma n : ℂ) *
      eulerPrimitiveBoundaryEndpointFeature sigma a n

theorem eulerPrimitiveBoundaryEndpointExpectation_eq_response
    {sigma : ℝ} (hsigma : 1 < sigma)
    {a : ℂ} (ha : -(1 / 2 : ℝ) < a.re) :
    eulerPrimitiveBoundaryEndpointExpectation sigma a =
      eulerPrimeCurrentComplexBlowupResponse sigma (1 + a) := by
  have hpair :=
    tsum_eulerPrimitiveBoundaryEndpointPair
      hsigma (a := a) (b := 0) ha (by norm_num)
  simpa [eulerPrimitiveBoundaryEndpointExpectation,
    eulerPrimitiveBoundaryEndpointFeature,
    eulerPrimitiveHorizonMultiplier] using hpair

/-- Source-normalized endpoint observation before Gamma completion. -/
def eulerPrimitiveBoundaryPrimeFluxTransport
    (sigma : ℝ) (a : ℂ) : ℂ :=
  ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) *
    eulerPrimitiveBoundaryEndpointExpectation sigma a

/--
The literal endpoint observation reconstructs `-ζ'/ζ` at the shifted safe
Euler point.  Prime-power label, pole normalization, and spectral direction
all remain visible in the left side.
-/
theorem eulerPrimitiveBoundaryPrimeFluxTransport_eq
    {sigma : ℝ} (hsigma : 1 < sigma)
    {a : ℂ} (ha : -(1 / 2 : ℝ) < a.re) :
    eulerPrimitiveBoundaryPrimeFluxTransport sigma a =
      infinitePrimeFlux (eulerPrimitiveBoundaryXiTracePoint sigma a) := by
  rw [eulerPrimitiveBoundaryPrimeFluxTransport,
    eulerPrimitiveBoundaryEndpointExpectation_eq_response hsigma ha,
    ofReal_eulerPrimeCurrentTotal_eq hsigma]
  unfold eulerPrimeCurrentComplexBlowupResponse
  have hflux : infinitePrimeFlux (sigma : ℂ) ≠ 0 := by
    rw [← ofReal_eulerPrimeCurrentTotal_eq hsigma]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (eulerPrimeCurrentTotal_pos hsigma))
  have hpoint :
      1 + (((sigma : ℂ) - 1) * (1 + a)) =
        eulerPrimitiveBoundaryXiTracePoint sigma a := by
    rw [eulerPrimitiveBoundaryXiTracePoint]
    ring
  rw [hpoint]
  field_simp [hflux]

/-- Gamma-completed primitive endpoint transport in the centered Xi chart. -/
def eulerPrimitiveBoundaryCompletedXiTraceTransport
    (sigma : ℝ) (a : ℂ) : ℂ :=
  -I *
    (eulerPrimitiveBoundaryPrimeFluxTransport sigma a -
      logDeriv archFactor
        (eulerPrimitiveBoundaryXiTracePoint sigma a))

/--
**Primitive endpoint-to-Xi trace law.**  On every safe pole-scaled ray, the
literal prime-power endpoint Green channel plus Gamma completion is exactly
the continued prime--archimedean Xi source trace.
-/
theorem eulerPrimitiveBoundaryCompletedXiTraceTransport_eq
    {sigma : ℝ} (hsigma : 1 < sigma)
    {a : ℂ} (ha : -(1 / 2 : ℝ) < a.re) :
    eulerPrimitiveBoundaryCompletedXiTraceTransport sigma a =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (eulerPrimitiveBoundaryXiTracePoint sigma a)) := by
  rw [eulerPrimitiveBoundaryCompletedXiTraceTransport,
    eulerPrimitiveBoundaryPrimeFluxTransport_eq hsigma ha,
    continuedPrimeArchSourceRelativeTrace,
    xiWardCenteredCoordinate_source]

/-! ## The transport is an observation of the Green primitive -/

/-- Two endpoint nodes: the shifted test and the source basepoint. -/
def eulerPrimitiveBoundaryXiTraceNodes
    (a : ℂ) : Fin 2 → ℂ
  | 0 => a
  | 1 => 0

theorem eulerPrimitiveBoundaryEndpointExpectation_eq_greenEntry
    {sigma : ℝ} (hsigma : 1 < sigma)
    (a : ℂ) (ha : -(1 / 2 : ℝ) < a.re) :
    eulerPrimitiveBoundaryEndpointExpectation sigma a =
      eulerPrimitiveHorizonBoundaryGreen (Fin 2)
          (eulerPrimitiveBoundaryEndpointTransgression sigma
            (eulerPrimitiveBoundaryXiTraceNodes a)) 0 1 := by
  rw [eulerPrimitiveBoundaryEndpointExpectation_eq_response hsigma ha]
  rw [(eulerPrimitiveBoundaryEndpointTransgression_exact sigma
    (eulerPrimitiveBoundaryXiTraceNodes a)).2]
  simp [eulerPrimitiveBoundaryEndpointGram,
    eulerPrimitiveBoundaryXiTraceNodes]

/--
The safe prime current is the source-normalized off-diagonal Green
primitive.  This is the chain-level bridge from boundary transgression to
the completed current before odd Ward extraction.
-/
theorem eulerPrimitiveBoundaryPrimeFluxTransport_eq_greenEntry
    {sigma : ℝ} (hsigma : 1 < sigma)
    (a : ℂ) (ha : -(1 / 2 : ℝ) < a.re) :
    eulerPrimitiveBoundaryPrimeFluxTransport sigma a =
      ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) *
        eulerPrimitiveHorizonBoundaryGreen (Fin 2)
          (eulerPrimitiveBoundaryEndpointTransgression sigma
            (eulerPrimitiveBoundaryXiTraceNodes a)) 0 1 := by
  rw [eulerPrimitiveBoundaryPrimeFluxTransport,
    eulerPrimitiveBoundaryEndpointExpectation_eq_greenEntry hsigma a ha]

end

end RHTower
