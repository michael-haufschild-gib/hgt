# Squarefree convolution-half Laplace source criterion

- **ID:** squarefree-convolution-half-laplace-source-criterion
- **Stage:** 1-in-progress
- **Type:** BRIDGE CANDIDATE
- **Source:** `multiplicity-parity-ladder-route.md`
- **Status:** `[OPEN LOCAL BOUND] [LEAN-PROVED BRIDGE] [NOT RH]`

## Exact surviving edge

Construct an analytic square root of `poleClearedFirstTraceExponentialContinuation` on
`rightHalf`, equivalently discharge `RHLadder 1`. This is the report's first multiplicity rung.

## Frozen bridge L-HEAT1

For `N >= 0`, define the exponentially damped arithmetic half

\[
  A_N(s)=\sum_{n\ge 1} a_n n^{-s}\exp\!\left(-\frac{n}{N+1}\right),
  \qquad a*a=\mu^2,
\]

where `a = squarefreeConvolutionHalf`. Then:

1. every `A_N` is entire;
2. `A_N(s) -> LSeries a s` for every `Re(s)>1`;
3. after multiplying by `poleFactorSqrtApprox N` and dividing by
   `squarefreeCarlemanHalfDet`, local boundedness on `rightHalf` implies `RHLadder 1` by Vitali.

Items 1--3 are derived bridge claims with visible proof routes, not the conjectural arithmetic
input. The frozen open statement is local boundedness of that explicit pole-cleared family.

## Formalized bridge

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfLaplaceCriterion.lean`.

Lean proves unconditionally:

- positive damping scale `1/(N+1)` tends to zero;
- every damped sum is entire by a local exponential M-test;
- dominated convergence recovers `LSeries squarefreeConvolutionHalf` at every `Re(s)>1`;
- pole/Carleman-normalized approximants converge pointwise to the canonical source limit there;
- local boundedness on `rightHalf` implies `RHLadder 1` through the existing Vitali bridge.

Verification on 2026-09-04: direct production check pass; targeted build `12847/12847`; four
public theorem axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`; umbrella
import wired. No local boundedness claim is made.

## Why prior no-gos do not immediately apply

- No finite cutoff or terminal boundary coefficient exists.
- No first discrete primitive recovers raw partial sums, so the order-one Cesaro interpolation
  no-go does not apply verbatim.
- Damping is infinite-order and source-faithful: every coefficient is retained, and weights tend
  pointwise to one in the Euler chamber.

## Hostile falsification

The expected Selberg--Delange main term for the convolution-half coefficients predicts growth near
the exterior point `s=6/11`, plausibly refuting local boundedness. Corpus currently contains no
such asymptotic for `squarefreeConvolutionHalf`; proving or bypassing it is the first attack after
formalizing items 1--3.

## Falsifier

Any unconditional proof that the pole-cleared Laplace family is unbounded at one point of
`rightHalf`, especially `boundaryExteriorPoint = 6/11`, retires L-HEAT1. A weaker pointwise
divergence statement is insufficient unless the pole-factor/Carleman normalization is included.

## Log

- 2026-09-04 -- corpus search found no exponential-damping construction for
  `squarefreeConvolutionHalf`; card opened after all cofinal Cesaro schedules were closed.
- 2026-09-04 -- positive-backbone/Euler-correction variant rejected as a new route because
  `TwinRigidity.lean` reduces it to existing diagonal analytic-unit freedom.
- 2026-09-04 -- entire smoothing, Euler undamping, normalized pointwise limit, and exact
  Vitali-to-rung bridge formalized and axiom-audited; local boundedness remains open.
