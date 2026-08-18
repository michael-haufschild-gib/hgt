# Second-Cartier compact-circle and literal-short firewall

- **ID:** P-SHC-CIRCLE-FIREWALL
- **Stage:** 3-formalized
- **Type:** THEOREM / SHARP NO-GO (Lean 4)
- **Source:** `rh-current-frontier-map.md` · Route-P physical-order core
- **Statement:** A finite positive circle measure cannot represent the literal coefficient-faithful endpoint ghost on any occupied strict-right Xi fibre, and no scalar multiple of the literal non-spectral conormal short bounds its reciprocal radial energy.

## Result

For HTGeometry's exact finite-circle moment sequence

\[
  \widehat\mu(e)=\int_{\mathbb T}z^{-e}\,d\mu(z),
\]

Lean proves

\[
  |\widehat\mu(e)|\le \mu(\mathbb T)
\]

for every integer `e`; hence every finite positive circle-measure moment family is
`bilateralModerate`.

Let `D_{x,u,q,r,N,p}(G)` be the already-proved literal Gamma--Julia endpoint image of the
second-Cartier ghost, with exact clock, prime label, Xi support copy, conormal coefficient, both
Hardy orientations, and divisor multiplicity.  For every strict-right copy `q`, nonzero source
coupling/aperture, and positive endpoint third jet,

\[
  \nexists\mu<\infty:\quad
  \widehat\mu(e)=D_{x,u,q,r,N,p}(G)(e)\quad(\forall e\in\mathbb Z).
\]

The reason is exact, not qualitative: such a measure would make the endpoint moderate, while the
coefficient-faithful endpoint theorem proves geometric reciprocal escape and non-moderation.

The same escape closes the scalar-short alternative.  If
`S(c)=4|c|^2` is the literal non-spectral conormal short, then

\[
  \nexists C\in\mathbb R:\quad Q(T_{\lambda_{p,q}^n}H_c)\le C S(c)
  \quad(\forall n\in\mathbb N).
\]

Thus existing compact positive-measure/Toeplitz/Bochner admission and existing literal conormal
short are both rigorously incapable of controlling the same retained endpoint orbit.

## Global classification

Universal finite-circle representability over all strict-right Xi copies is equivalent to RH.
The forward implication contradicts the per-copy firewall under `not RH`; the reverse implication
is vacuous because RH empties `XiRightZeroCopy`.  This is a firewall, not an RH proof: corpus still
lacks an independent completed-source theorem producing global endpoint order before Xi selection.

## Lean

Module:
`GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierCompactCircleFirewall`

Declarations:

- `SourceHorizontalHTCircleMeasure`
- `circleMeasureMomentZ_bilateralModerate`
- `SourceHorizontalActualXiEndpointCompactCircleRepresentation`
- `not_sourceHorizontalActualXiEndpointCompactCircleRepresentation`
- `not_exists_sourceHorizontalActualXiLiteralConormalShort_orbit_budget`
- `EverySourceHorizontalActualXiEndpointCompactCircleRepresentation`
- `everySourceHorizontalActualXiEndpointCompactCircleRepresentation_iff_rh`

## Heavy-conjecture audit

- Finite positive circle-measure realization of exact endpoint: **failed and disproved** on every
  occupied strict-right fibre.
- Toeplitz/Bochner positivity added after endpoint extraction: **failed by same theorem**; it would
  imply bounded moments.
- Existing non-spectral conormal short controls reciprocal orbit: **failed and disproved**; short is
  static while positive two-sided energy tends to infinity.
- Strongest survivor: an unconditional completed source law that globally produces endpoint
  moderation/order would immediately imply RH, but it must act before divisor selection.  It cannot
  be a post-selected finite measure or a scalar multiple of existing short.

## Status

Paper proof and Lean proof are dependency-closed. Module is wired into `RHTower.lean`; exact leaf
verification and axiom audit pass. External novelty not audited.
