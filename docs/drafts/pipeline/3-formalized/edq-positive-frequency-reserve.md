# EDQ positive-frequency reserve and sharper full-source comparison

- **ID:** EDQ-PFR
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Source:** [current EDQ frontier](../1-in-progress/rh-current-frontier-map.md), [outgoing stationary comparison](edq-stationary-reflected-tail-sum.md)
- **Statement:** For positive logarithmic height and positive frequency, the actual anchored sine integral is at most its initial reciprocal clock weight. An exact nonnegative higher-derivative reserve halves the existing positive-frequency ceiling in the full remainder comparison.

## Goal and scope

Euler deletion → exact remainder → cumulative incoming-head comparison → off-line-zero exclusion → RH. The existing incoming-head comparison loses much of its margin to the positive-frequency ceiling. This component proves a sharper ceiling from the actual weighted phase, with every integration boundary and opposing sector retained. The incoming-head comparison itself and RH remain open.

## Dependency-closed paper proof

Let `a>0`, `beta>2`, `gamma>=0`, `omega>0`, `d=omega*x+gamma`, `phi=omega*(x-a)+gamma*log(x/a)`. The actual reciprocal weight is `W=x^(1-beta)/d`, and `D=-W'`. Existing proofs give `S=integral x^(-beta)*sin(phi)=W(a)-integral D*cos(phi)` and total mass `integral D=W(a)`.

Define `H=D/phi'`, `K=-H'`, `L=K/phi'`, `M=-L'`. Then

`H=x^(1-beta)*(beta*omega*x+(beta-1)*gamma)/d^3`.

With `u=omega*x`, `delta=beta-2`,

`K=x^(-beta)*[(delta+2)*(delta+3)*u^2+(2*delta^2+7*delta+4)*u*gamma+(delta+1)^2*gamma^2]/d^4`.

The numerator of `M`, after its factor `x^(-beta)/d^6`, is

`(delta+2)*(delta+3)*(delta+4)*u^3 + (3*delta^3+21*delta^2+40*delta+14)*u^2*gamma + (3*delta^3+15*delta^2+17*delta+6)*u*gamma^2 + (delta+1)^3*gamma^3`.

All coefficients are positive. These formulas prove `K,M>=0` directly. The identities `H=x^(1-beta)*(beta/d^2-gamma/d^3)` and `L=x^(1-beta)*(beta*(beta+1)/d^3-(3*beta+2)*gamma/d^4+3*gamma^2/d^5)` give `H,L -> 0`; derivative integrability follows from their monotonicity and finite endpoint limits. Therefore two integrations by parts give

`integral D*cos(phi)=integral K*sin(phi)=integral M*(1-cos(phi))>=0`.

Every boundary product vanishes at infinity and at the anchor (`sin(0)=0`, `1-cos(0)=0`). Hence `0<S<=W(a)`, including the exact nonnegative reserve `W(a)-S`.

For the literal positive-frequency atom this yields `Im A(s,N,k)<=w_k/(2*pi*k*N+t)`. The known positive-frequency mass `1/24` bounds its full sector by `1/[24*(2*pi*N+t)]`, half the prior ceiling. The full stationary and incoming/outgoing comparisons retain their other terms; this does not impose nonpositivity on the stationary head.

## Exact full-source consequences

Write `m=t/[12*normSq(s+1)]`, `c=1/[24*(2*pi*N+t)]`, and `S_N` for the exact stationary-frequency sum. The complete inequality is

`N^(2*sigma+1)*Im(g_s(N)) <= S_N+c-m`.

For `0<sigma<=1`, `t>=1`, `N>=1`, the already proved comparison `2*c<m` gives the strict reserve `m/2<m-c`. Consequently the scaled source is strictly below `S_N-m/2`. This is a quantitative margin, with no assumption on the source being at a zeta zero.

For the incoming/outgoing decomposition `S_N=Im(H+C*P_ref)`, the full comparison becomes

`N^(2*sigma+1)*Im(g_s(N)) <= Im(H)+Q*norm(P_ref)+c-m`.

At a zero with `1/2<=sigma<1`, `t>=1`, and unit cutoff `K=floor(t/(2*pi))`, the retained incoming head satisfies

`Im(H(s,1,K)) > t*(2*sigma-1)/[2*normSq(conj(s)*(1-conj(s)))]+t/[24*normSq(s+1)]-Q(s,1)*P(s,K)`.

`Q` and `P` are the actual outgoing-factor and reflected-prefix envelopes from the linked certificate. This does not show that `Q*P` is smaller than the reserve, nor give an opposing upper bound on `Im(H)`. These zero-consequences also apply on the critical line. RH remains open.

## Lean inventory and audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticPositiveFrequencyReserve`; 475 lines, 33 declarations (27 theorems, 6 definitions). Namespace: `RHTower.DeletionMixedRefinement`.

- Exact derivative polynomials, nonnegative densities, zero boundary limits, and absolute integrability.
- `integral_positiveClock_cos_eq_sin`, `integral_positiveClock_sin_eq_defect`, `integral_anchoredLogSine_exact_positive_reserve`, `integral_anchoredLogSine_le_initial_weight`.
- `normalizedWeightedRemainder_scaled_im_le_stationary_half_ceiling`, `normalizedWeightedRemainder_scaled_im_le_incoming_half_ceiling`, `positiveFourier_half_ceiling_reserve`, `normalizedWeightedRemainder_scaled_im_lt_stationary_half_mean`.
- `stationaryFourierBudget_lowerBound_half_mean_at_zero`, `stationaryIncomingSection_im_lowerBound_half_mean_at_zero`, and their exact-ceiling forms.

Foreground scratch passed. Final targeted `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticPositiveFrequencyReserve` built only this leaf in 4.4 seconds, reusing dependencies. The umbrella import is wired; no umbrella build ran. All 33 new declarations were audited once, depending only on `propext`, `Classical.choice`, and `Quot.sound`. No numerical experiment or computational certificate was used. Formal lint passed (existing size warnings only). Audit logs: `/tmp/edq_positive_reserve_{build,axioms,lint}.log`.

## Verification gates

- [x] Corpus search and source inspection before new Lean code.
- [x] Dependency-closed symbolic paper proof with derivative and analytic checks in Lean.
- [x] Foreground scratch verification.
- [x] Wire finished leaf; final targeted leaf build only.
- [x] New-only axiom audit and formal lint.
- [x] Current-frontier update, corpus index refresh, and cleanup. All owned Lean processes exited; temporary Lean sources removed.
- [ ] Independent incoming-head comparison and unconditional RH proof/falsification.
