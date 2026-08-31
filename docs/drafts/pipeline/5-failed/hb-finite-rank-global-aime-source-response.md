# Failed route: HB finite-rank global AIME source response

Status: killed; Lean formalized

## Route

Let one finite-algebraic-rank complex-linear global response act on literal cubic, phase-odd AIME
source packet.  Permit arbitrary mixing among all Xi fibres and require diagonal output coefficient
to cancel AIME pole numerator on every fibre.

## Obstruction

Finite-dimensional range inside `XiZeroCopy →₀ ℂ` has one common finite output support.  Infinite Xi
divisor supplies a fibre outside it, where response coefficient is zero but AIME numerator is
nonzero for every nonzero seed.  Universal cancellation fails.

Closed Lean certificate:
`RHTower.d4HBFiniteRankGlobalAIMESourceResponseCancellationRouteKilled`.

## Positive survivor

Any universal source-adapted cubic AIME cancellation response has infinite algebraic rank.  This
survivor is formalized as
`RHTower.d4HBGlobalAIMESourceResponse_universalCancellation_forces_infiniteRank`.

Therefore surviving HB causal producer must retain infinitely many independent output directions
before divisor selection.  Arbitrary finite cross-fibre mixing cannot replace completed continuum,
infinite-variation/non-Rajchman peripheral data, or genuinely infinite-rank nonlocal response.
