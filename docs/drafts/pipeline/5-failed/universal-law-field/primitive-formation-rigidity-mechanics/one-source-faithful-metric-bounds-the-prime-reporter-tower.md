# One source-faithful metric bounds the prime reporter tower

- **Status:** `[FALSIFIED] [NO-GO CLOSED] [POSITIVE SURVIVOR EXTRACTED]`
- **Date:** 2026-08-12
- **Parent programme:**
  `../../../1-in-progress/universal-law-field/primitive-formation-rigidity-mechanics/field-programme.md`
- **Positive survivor:**
  `../../../2-fully-proven/universal-law-field/primitive-formation-rigidity-mechanics/prime-jet-analytic-formation-transport-reporter-conservation-and-boundary-port-transmutation-law.md`

## Failed conjecture PFRM-B1

There is one normed completion of the finite prime packets such that

1. every fixed prime atom remains uniformly bounded;
2. every exact normalized FE-paired derivative reporter remains uniformly bounded;
3. coordinatewise prime inclusion is the formation transition;
4. common scalar renormalization may be used if necessary.

## Exact countertheorem

Fix a prime `p`. Let `e_p^(N)` be its coordinate atom in every sufficiently large finite prime
packet, and let `varphi_N` be the exact normalized FE-paired derivative reporter. Suppose

\[
 \sup_N\|e_p^{(N)}\|_N\le M_p<\infty.
\]

The Lean-certified prime barycentric coefficient theorem gives

\[
 |\varphi_N(e_p^{(N)})|\longrightarrow\infty.
\]

Therefore

\[
 \|\varphi_N\|_N
 \ge\frac{|\varphi_N(e_p^{(N)})|}{\|e_p^{(N)}\|_N}
 \ge\frac{|\varphi_N(e_p^{(N)})|}{M_p}
 \longrightarrow\infty.
\]

Conversely, a uniform reporter bound forces `||e_p^(N)||_N` to diverge. Thus no one bornology is
simultaneously source-faithful and reporter-faithful.

The Lean-certified projective escape theorem strengthens this: for fixed primes `p<q`,

\[
 \frac{|\varphi_N(e_q)|}{|\varphi_N(e_p)|}\longrightarrow\infty.
\]

Hence no support-dependent scalar rescales both coefficients to finite nonzero limits.

Finally take `x_N=E_N(z)`, the prime sample of the odd coordinate function. Then
`varphi_N(x_N)=1`. If `L_N=ker varphi_N`, exact work--capacity reciprocity gives

\[
 \operatorname{dist}(x_N,L_N)^2=\|\varphi_N\|^{-2}\longrightarrow0.
\]

The conjectured metric would therefore make exact formation depth positively invisible rather than
proper.

## Exact reason for failure

Coordinatewise prime inclusion is the wrong transition. The correct transition is the nonlocal
Lagrange formation map

\[
 T_N=E_{N+1}\iota_NE_N^{-1}.
\]

The reporters satisfy `varphi_(N+1) T_N=varphi_N`, while their restrictions along local coordinate
inclusion do not agree. The coefficient divergence is a chart incompatibility coupled to a genuine
bornological obstruction.

## Positive survivor

The failed bounded-metric conjecture exposes four exact laws:

1. strict nonlocal formation transport;
2. contravariant reporter conservation;
3. rank-one locality defect `Delta_N=a_* tau_N`;
4. one-step boundary-port transmutation and reciprocal Gram work.

The next live programme is not another metric search. It is a polarized two-sector formation law
coupling source atoms to an independently admitted analytic/archimedean reporter.

## Lean status

The arithmetic divergence and projective escape inputs are Lean-certified. The fused
formation-transport and boundary-port survivor is paper-proved but not yet Lean-formalized, so it
does not yet count as a completed formal theorem under project rules.

## Log

- 2026-08-12 -- conjecture killed by fixed-prime coefficient divergence and projective escape;
  nonlocal analytic formation and boundary-port transmutation extracted as positive survivor.
