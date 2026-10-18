# Route PM: active-pair shifted correlation

Status: in progress. Scope: unconditional arithmetic contribution to the FZZ-P energy obstruction.

## Task and constraints

Use the current Lean corpus; no web search, numerical experiments, or literature novelty audit.
Do not edit `docs/reports/rh-current-frontier-map.md`. Preserve unrelated worktree edits.
Complete paper proof before Lean; audit leaf modules in the foreground, wire umbrella imports,
run formal lint and axiom audit. No added axioms or unproved analytic premises.

## Plan

1. Inspect the active-pair reduction and existing arithmetic correlation machinery.
2. Test a uniform bound for the uncentered shifted-divisor remainder; extract the strongest
   positive law if the bound fails.
3. Prove the exact surviving statement on paper and formalize it.
4. Audit statements, dependencies, imports, Lean checks, and lint; record actual remaining gap.

## Evidence and current conjectures

The frontier map and current Lean modules establish the active-pair identity and an upper
bound by `1/8` plus half the compensated sum of
`τ_ε(n) τ_(1+ε)(n) - τ_(1+ε)(n) τ_ε(n+1)`.
Dropping gradient dissipation may lose an essential logarithmic term.

C1: this shifted difference has a uniform upper bound in the horizon.
Refuted on paper: its same-node and adjacent-node Euler densities differ strictly at small damping.

C2: the *complete* active-pair term has a positive logarithmic drift at sufficiently small
positive damping. Candidate slope as damping tends to zero:
`1/4 - A/2`, where `A = ∏_p (1 - 1/(p(p-1)))`.
Paper proof complete below. Lean audit in progress: actual Cesàro correlation and its Euler
product have passed; small-damping passage, compensated logarithmic transfer, and sign remain.

The intended positive survivor is an exact arithmetic drift and the corresponding interior
cancellation budget. Neither a negative statement alone nor a conditional RH receiver completes
this task.

## Dependency-closed paper proof

Write `u_s(n) = ∏_{p|n}(1-p^(-s)) = ∑_{d|n} μ(d)d^(-s)` for `n ≥ 1`,
and `α_s = ∏_p(1-p^(-1-s))`. All parameters below are strictly positive.
The existing corpus proves `0 ≤ u_s ≤ 1`, `α_ε/ε → 1`, same-node second density
`C_ε/ε → 1/2`, and mixed same-node density `A_ε/ε → 1`.

**Adjacent density.** For `s,t > 0`,
`N⁻¹ ∑_{n=1}^N u_s(n+1)u_t(n) → H(s,t) = ∏_p(1-p^(-1-s)-p^(-1-t))`.

Proof: for fixed positive `d`, expand the average of `1_(d|n) u_s(n+1)` into the
`a`-divisor sum. The simultaneous count `d|n, a|n+1` has density `1/(ad)` if
`gcd(a,d)=1` and zero otherwise, by CRT. Its normalized count is at most `2/a`
for every `N ≥ 1`, since `n+1 ≤ N+1`. Thus dominated convergence applies with
majorant `2 |μ(a)|/a^(1+s)`. Now expand `u_t(n)`. Each outer normalized term has
absolute value at most `|μ(d)|/d^(1+t)`, using `0 ≤ u_s ≤ 1` and the exact count
`⌊N/d⌋`. A second dominated convergence yields
`∑_{gcd(a,d)=1} μ(a)μ(d)/(a^(1+s)d^(1+t))`.
This double series is absolutely summable. Restricting both indices to integers supported on
a finite prime set factors it into `∏(1-p^(-1-s)-p^(-1-t))`: each prime occurs in
the first index, the second, or neither, and square powers vanish. These finite sets exhaust
all nonzero terms, so absolute convergence gives the asserted Euler product.

**Small-damping correlations.** Set `D_ε=H(ε,ε)` and `B_ε=H(ε,1+ε)`.
Divide their Euler products by the nonzero `α_ε`:

`H(ε,t)/α_ε = ∏_p (1 - p^(-t)/(p-p^(-ε)))`.

All factors lie in `(0,1)` for `t≥ε>0`. The factor at `p=2` shows
`0 ≤ D_ε/α_ε ≤ 1 - 2^(-ε)/(2-2^(-ε)) → 0`; hence `D_ε/ε → 0`.
For `t=1+ε`, the deficits are at most `1/(p(p-1)) ≤ 2/p²` and converge pointwise
to `1/(p(p-1))`. Dominated convergence for infinite products gives
`B_ε/ε → A`, where `A=∏_p(1-1/(p(p-1)))`.
The deficits are summable and each factor is strictly positive, so `A>0`.
Keeping only the `p=2,3` factors gives `A ≤ (1/2)(5/6)=5/12`.

**Exact active-pair drift.** Let `S_ε(n)=(u_(1+ε)(n)-u_ε(n))/2` and
`X_ε(n)=u_ε(n)-α_ε`. The corpus's exact active-pair identity is
`P_ε(T)=∑_{n=1}^{T-1} X_ε(n+1)(S_ε(n+1)-S_ε(n)) w_T(n)`,
with `w_T(n)=1/(n+1)-1/(T+1)`.
The Cesàro mean of its summand is
`κ_ε=(A_ε-C_ε-B_ε+D_ε)/2`.
Indeed expand the four products; shifted same-node means have the same limit because
all fields are bounded; the centering term has mean zero by telescoping bounded `S_ε`.
Cesàro-to-harmonic transfer, a summable `1/n-1/(n+1)` correction, and the bounded
compensation `(T+1)⁻¹∑summand` prove `P_ε(T)/log T → κ_ε`.
Consequently `κ_ε/ε → 1/4-A/2 ≥ 1/24`.
There exists `δ>0` such that for every `0<ε<δ`, `κ_ε>ε/48`, and therefore
`P_ε(T) → +∞`. The original C1 is false as well: its logarithmic rate is
`A_ε-B_ε`, whose quotient by `ε` tends to `1-A>0`.

**Positive survivor and exact budget.** The established complete-energy identity is
`E_ε(T)=V_ε(T)+2P_ε(T)+2I_ε(T)`, with `I` the doubly-inactive Bézout interior.
Therefore the explicit finite-horizon renormalization
`E_ε(T)= [V_ε(T)-v_ε log T] + 2[P_ε(T)-κ_ε log T]
          + 2[I_ε(T)+(v_ε/2+κ_ε)log T]`
is exact, and the first two brackets are `o(log T)` unconditionally for every `ε>0`.
The required interior log coefficient has small-damping rate
`(v_ε/2+κ_ε)/ε → (1-A)/2 ≥ 7/24`.
This locates the missing cancellation in the actual signed interior with an explicit arithmetic
coefficient. It does not prove the bounded complete energy or RH.

Paper status: proof complete. Lean status: adjacent Cesàro limit and Euler product checked in
`PMAdjacentDivisorCorrelation.lean` and `PMAdjacentDivisorEuler.lean`; downstream audits pending.
These are actual adjacent Cesàro limits, not merely a formal Euler product or finite-period analogue.

## Tool availability

`update_plan` and `multi_tool_use.parallel` are not exposed in this session; track steps here and
batch independent reads with `functions.exec` / `Promise.allSettled`.
Serena is initialized but its active language is Python; Lean symbol extraction returns
`ValueError: Cannot extract symbols ... Active languages: ['python']`. Use exact `rg` locations
and bounded source reads for Lean.
