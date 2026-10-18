# Route PM: uniform active-pair bound

Status: refuted on paper and in Lean 4; positive survivor formalized. Retired scope: a uniform bound on the
active-plus-predecessor contribution or its uncentered shifted-difference upper remainder.

## Obstruction

Write `P_ε(T)` for the complete active-plus-predecessor sum. Its exact logarithmic coefficient is

`κ_ε = (A_ε - C_ε - H(ε,1+ε) + H(ε,ε))/2`,

where `A_ε` and `C_ε` are the existing mixed same-node and square densities, and
`H(s,t)=∏_p(1-p^(-1-s)-p^(-1-t))` is the actual adjacent Cesàro density.
For every `ε>0`, `P_ε(T)/log T → κ_ε`. As `ε↓0`,

`κ_ε/ε → 1/4 - A/2 ≥ 1/24`, with `A=∏_p(1-1/(p(p-1)))` and `0<A≤5/12`.

Thus every sufficiently small fixed positive damping has `P_ε(T)→+∞`.
The existing upper bound by `1/8` plus half the uncentered shifted-difference sum also rules out
a horizon-uniform upper bound on that remainder.

## Positive survivor

The obstruction exposes an exact arithmetic drift and interior cancellation coefficient,
not only a negative verdict. Put `r_ε=v_ε/2+κ_ε`, where `v_ε` is the divisor variance.
The complete energy `E_ε`, covariance diagonal `V_ε`, and doubly-inactive interior `I_ε` satisfy

`E_ε(T) = (V_ε(T)-v_ε log T) + 2(P_ε(T)-κ_ε log T) + 2(I_ε(T)+r_ε log T)`.

The first two brackets are `o(log T)` unconditionally. Consequently
`(I_ε(T)+r_ε log T-E_ε(T)/2)/log T → 0`, and
`r_ε/ε → (1-A)/2 ≥ 7/24`.
This identifies the explicit cancellation required from the actual signed interior.
Bounding the complete energy remains open.

Paper proof: dependency-closed and complete in the
[survivor card](../3-formalized/pm-active-pair-shifted-correlation.md).
Lean status: all four leaves passed; all 22 exported theorems use only Lean's standard axioms.
The exact active-pair and interior consequences are in `PMActivePairLogarithmicDrift.lean`.
No external literature novelty claim is made; the task prohibited that audit.
