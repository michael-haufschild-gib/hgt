# Exact damped clock endpoint sum rule

- **ID:** LI-CLOCK-DAMPED-ENDPOINT-SUM-RULE
- **Stage:** 3-formalized; four named leaves/35 public declarations; final exact Lean, all-public foundational axiom and independent source audits PASS
- **Type:** THEOREM; exact signed arithmetic aggregate, not pointwise positivity
- **Parent:** [finite eta orientation window](../1-in-progress/li-clock-finite-eta-orientation-window.md)

## Exact positive survivor

For the literal actual completed-source response F,

`integral_0^infinity exp(-2t) F(t) dt = (2+EulerGamma-log(4pi))/4 > 0`.

For one actual admissible fixed radius r and every 0<c<r/4, let W_N=c log(2N+1). The literal finite-prefix response satisfies

`integral_0^W_N exp(-2t) Re F_N(t) dt -> (2+EulerGamma-log(4pi))/4`.

Thus these growing-window signed areas are eventually positive. This does not supply pointwise clock sign and remains compatible with negative cofinal clocks under not-RH. Neither RH nor actual all-clock nonnegativity is assumed.

## Dependency-closed paper mechanism

The actual sine/Taylor response has coefficient (-1)^j M_j/(2j+1)!, with |M_j|<=A/150^j. Integrating each absolute damped term yields at most A/(4*600^j), using the exact gamma integral of t^(2j+1) exp(-2t). Summability closes Bochner/real integral interchange. The resulting complete sum is (1/4) sum_j M_j*(-1/4)^j; the installed Xi endpoint boundary value identifies it with the stated arithmetic constant. Installed `hasSum_normalizedPrimeArchMoment_endpointCurvature`, `tsum_normalizedPrimeArchMoment_endpointSpecialValue` and `xiEndpointCompletedCurvature_pos` give the exact arithmetic value and its unconditional positivity. Root spotchecked endpoint series and moment-radius source; all applicable APIs still require scratch verification.

For finite-prefix windows, actual uniform approximation gives epsilon_N=B_N*sinh(W_N/r)->0 and bounds the absolute weighted integral error by epsilon_N/2. W_N->infinity; absolute integrability of exp(-2t)F(t) makes the actual truncated integral tend to the full endpoint area. Combine both limits, then pass strict positive limit to eventual positive finite area. Retain finite-source integrability/continuity assumptions and prove them from the actual regular finite circle; approximation alone is not a measurability proof.

## Audit limits

Producer and independent pole paper audits PASS fixed p=2 formula, factor1/4, integrated complete envelope and finite-window transfer. Focused documented corpus research completed: `python3 scripts/formal_tools.py research 'actual completed sine clock exponentially damped Laplace integral endpoint Euler gamma log four pi signed area' --mode deep --budget-seconds 300 --explore 0`; log /tmp/hgt-li-clock-damped-endpoint-research.log. No corpus-wide or public novelty claim. Endpoint boundary formula is preexisting; new target is its exact signed clock integral and source-defined finite-window transfer.

Completed coefficientwise positivity strategy fails already cubic: finite cubic coefficients tend to -M1/6<0, even though actual and finite small-clock response is positive. This does not falsify the growing-window candidate. The broader damping family below passed paper, independent source and formal audits. No pointwise-sign consequence follows.

## Formal plan

1. Verify all installed endpoint/integration APIs in scratch.
2. Exact actual complete area plus absolute integrability, with no zero-location hypothesis.
3. Source-defined growing finite-window area convergence and eventual positivity, including actual finite integrability on quantitative valid circles.
4. Named leaves, final exact source, all public axiom audits and root spot-check before stage3.

## Log

- 2026-09-30 01:37 UTC — Card recorded before new Lean. Exact signed area and growing-window transfer are independently paper-closed; focused corpus audit and exact interface verification pending. No route retired; pointwise arithmetic window sign remains open.

## Stronger source-resolvent family (independent paper PASS)

Put w_q=(xiSpectralPoint q)^(-1), lambda_q=w_q^2 and A=sum_q|lambda_q|. Actual strip and radial bounds give |Im w_q|<1/300 and Re(lambda_q)>=(167/168)|lambda_q|>0. Therefore |F(t)|<=A*t*exp(t/300) for t>=0.

For p>1/300, absolute atom-integral Fubini gives

`integral_0^infinity exp(-p*t)F(t)dt = Re sum_q lambda_q/(p^2+lambda_q)`

`>= (167/168)*p^2*A/(p^2+1/150)^2 > 0`.

Complete source mass and t*exp(-(p-1/300)t) justify interchange; no first-power summability or RH. Per-copy real numerator is p^2*Re(lambda_q)+|lambda_q|^2 and denominator <=(p^2+1/150)^2. The algebraic resolvent itself has absolute convergence and the same lower bound for every p>0; integration needs the stricter damping condition. The algebraic extension and literal transform both passed independent premise review and final Lean checks.

For fixed admissible r,0<c<r/4,W_N=c log(2N+1), the finite weighted area J_N(p) tends to this positive invariant. If kappa=p-1/300 and epsilon_N=B_N*sinh(W_N/r), the explicit error is bounded by

`epsilon_N/p + A*exp(-kappa*W_N)*(W_N/kappa+1/kappa^2)`.

The p=2 arithmetic special value remains exact, independent of this broader transform mechanism. The two descriptions must agree, with all multiplicity copies retained.

## Exact deflated weighted cancellation (independent paper PASS)

The installed regular finite split gives, at p=2,

`integral_0^W_N exp(-2t)Re Fdef_N(t)dt - W_N -> (xiEndpointCompletedCurvature-1)/4`.

Indeed the removed compensation integrates exactly to W_N-(1-exp(-4W_N))/4. Producer, independent pole audit and root algebra check PASS. This is a signed aggregate cancellation law, not growing pointwise positivity.

- 2026-09-30 01:44 UTC — Focused area search complete57.52s, full63145 inventory, older coverage generation1146816/current1146817, semantic coverage unmeasured, shown candidate/source_arguments source-only and unsuitable. Broadened lexical endpointCurvature query found8 named hits including exact endpoint HasSum/Tsum; root read literal source135..177 and moment bound115..132. No public/corpus-wide novelty claim. Broader source-resolvent focused query running, log /tmp/hgt-li-clock-damped-resolvent-research.log.
- 2026-09-30 01:44 UTC — Disjoint formal scopes reserved: producer LiEvenCrossActualClockDampedEndpoint; current-source agent LiClockCentralTraceSineContinuity; root LiClockPairedEtaDampedWindow; pole LiEvenCrossActualClockDampedResolvent awaits broadened paper/search gate. No new clause is formal yet.

## All-damping finite deflated renormalization (independent paper PASS)

For every p>1/300, use the same admissible r and 0<c<r/4. Define the literal finite pole area P_p(W)=integral_0^W exp(-pt)*2sinh(2t)dt. Then

`integral_0^W_N exp(-pt)Re Fdef_N(t)dt - P_p(W_N) -> D_p`.

The exact source identity gives equality to J_N(p) at every quantitatively valid finite prefix. Both literal finite responses are continuous on real clocks; all finite weighted integrals exist. Subtraction takes place before the limit, so no subtraction of divergent improper integrals occurs when p<=2. Independent current-source audit PASS; root checked exact source split and finite circle regularity. The p=2 centered intercept remains the stated arithmetic constant. Further damping-regime asymptotics are paper observations, outside this formal target.

- 2026-09-30 02:14 UTC — Actual p=2 endpoint (5public), generic contour continuity (1public), broader damped resolvent (15public) all completed named build, final exact Lean and foundations-only axiom audits. Root read every broader declaration/proof. Broader documented search returned partial reranking after258.03s; installed laplace_sineKernel and QuasiPolynomial integral bridge reused with literal atom and full-copy absolute integral summability. No novelty claim. Root finite-window scratch proved uniform weighted-error transfer and growing area convergence apart from an installed sinh API spelling, now corrected; full finite window/explicit tail/deflated cancellation targets pending.

## Final formal certificates

All exact statements are formal in these four leaves (35 public declarations total):

- `LiClockCentralTraceSineContinuity.lean` (1): continuity for a literal circle-defined sine contour. Logs `/tmp/li_current_trace_continuity_{named,direct,axioms}.log`.
- `LiEvenCrossActualClockDampedEndpoint.lean` (5): absolute integrability, integrated norm bound, exact curvature and arithmetic endpoint values, positive signed area. Logs `/tmp/hgt-li-clock-damped-endpoint-{build,direct,axioms}.log`.
- `LiEvenCrossActualClockDampedResolvent.lean` (15): actual reciprocal transverse bound, squared-weight global envelope, full-copy absolute transform interchange for p>1/300, absolutely summable positive resolvent and quantitative floor for p>0. Logs `/tmp/li_pole_damped_resolvent_{named_build,final_direct,axioms}.log`.
- `LiClockPairedEtaDampedWindow.lean` (14): literal finite window/area definitions, finite clock continuity, growing-window signed-area convergence and eventual positivity, quantitative approximation-plus-tail bound, all-p finite deflated renormalization, exact arithmetic endpoint and centered deflated intercept. Logs `/tmp/hgt-li-clock-damped-window-{build,direct,axioms}.log`.

Root named build terminal exit0 (30s/14367 jobs); final exact source exit0, empty output; every public declaration has only `[propext, Classical.choice, Quot.sound]`. Independent review checked every definition/proof, radius and damping quantifier, finite integrability, complete copies, signs and intercept. Every leaf wired in RHTower umbrella. No RH, all-clock nonnegativity or growing pointwise sign premise enters these aggregate laws.

- 2026-09-30 02:26 UTC — Strongest recorded survivor closed in paper and Lean; card promoted Stage3. Main growing arithmetic sign candidate remains Stage1. Index and global lint gates follow umbrella wiring; unrelated workspace failures are reported separately. No route retired.
