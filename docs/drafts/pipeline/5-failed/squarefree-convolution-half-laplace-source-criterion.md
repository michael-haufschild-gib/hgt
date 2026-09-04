# Squarefree convolution-half Laplace source criterion

- **ID:** squarefree-convolution-half-laplace-source-criterion
- **Stage:** 5-failed
- **Type:** FALSIFIED BRIDGE
- **Source:** `multiplicity-parity-ladder-route.md`
- **Status:** `[LOCAL BOUND FALSIFIED] [LEAN-PROVED NO-GO] [NOT RH]`

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

## Hostile falsification — closed

No Selberg--Delange asymptotic is needed. At `s=6/11`, local boundedness would force diagonal heat
samples at `t_N=1/(N+1)` to be `O(5^{-N})`. Bounded shifted coefficients and the exact exponential
moment bound make the full heat profile uniformly bounded between adjacent reciprocal mesh points.
Its Mellin transform is then holomorphic for `Re(z)>0`; translation by `6/11` and reciprocal-Gamma
removal continue the canonical arithmetic half to `Re(s)>6/11`. Squaring on the Euler overlap and
analytic uniqueness contradict `zetaResidueUnit 1 = 1`.

## No-go certificate

`not_poleClearedFirstTraceLaplaceLocallyBounded` in
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfLaplaceDiagonalNoGo.lean` proves the
exact negation of the open local-bound hypothesis. Direct check and targeted build `13034/13034`
pass; public theorem axiom audit contains only `propext`, `Classical.choice`, `Quot.sound`. The
route is retired, not an RH proof.

Strongest positive survivor: reciprocal heat meshes have a sharp transport law. If shifted
coefficients are bounded, adjacent-time variation costs only a universal constant because mesh
gap `asymp N^{-2}` cancels exponential first-moment scale `asymp N^2`. A viable successor must
decouple smoothing time from pole degree enough to break this transport, or introduce a literal
source-derived singular/nonlinear correction.

## Log

- 2026-09-04 -- corpus search found no exponential-damping construction for
  `squarefreeConvolutionHalf`; card opened after all cofinal Cesaro schedules were closed.
- 2026-09-04 -- positive-backbone/Euler-correction variant rejected as a new route because
  `TwinRigidity.lean` reduces it to existing diagonal analytic-unit freedom.
- 2026-09-04 -- entire smoothing, Euler undamping, normalized pointwise limit, and exact
  Vitali-to-rung bridge formalized and axiom-audited; local boundedness remains open.
- 2026-09-04 -- local boundedness falsified by reciprocal-mesh interpolation plus Mellin pole
  contradiction; L-HEAT1 retired without Selberg--Delange input.
