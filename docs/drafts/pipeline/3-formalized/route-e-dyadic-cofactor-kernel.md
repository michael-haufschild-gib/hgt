# Route E exact dyadic cofactor kernel and critical boundary

- **ID:** MC-DYADIC-COFACTOR-KERNEL-2026-10-01
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/mc-source-cancellation-loop-2026-10-01.md`, C05a
- **Module:** `formal/GaloisForLFunctions/RHTower/RouteEDyadicCofactorKernel.lean`
- **RH used:** no
- **Numerical experiments:** none
- **Status:** scratch audit, targeted leaf build, final direct module audit and all five axiom audits passed.

## Exact statements

Let `K_r(a,b)=(a+b)^(-r)-(2a+b)^(-r)` and

`T_r(a,b)=K_r(2a,b)-K_r(a,b)+K_r(a,2b)`.

Write `F_r(a,q;Q)` for the literal nonlinear integer-numerator fibre with cofactor cutoff `Q`; its coefficients are `1_((a,d)=1) μ(a)μ(qd)`. Define

`H_r(a,q;Q)=Σ_(0<d<Q, d odd) 1_((a,d)=1) μ(a)μ(qd) T_r(a,qd)`,

`B_r(a,q;Q)=Σ_(0<d<Q, d odd, Q≤2d) 1_((a,d)=1) μ(a)μ(qd) K_r(a,2qd)`.

For every real `r`, odd numerator `a`, odd prime `q`, and natural `Q`,

`F_r(a,q;Q)+F_r(2a,q;Q) = -H_r(a,q;Q)+B_r(a,q;Q)`.

The critical kernel has the exact positive form, for all `a,b>0`,

`T_1(a,b)=a(4a²+5b²)/(2(a+b)(a+2b)(2a+b)(4a+b))>0`.

For every prime `q` and `a≤q`,

`|B_1(a,q;q)|≤1/q²`.

Consequently, for every odd prime `q` and `A<q`, the literal completed odd-core block satisfies

`|P_1(A,q;q)+Σ_(1≤a≤A, a odd) H_1(a,q;q)|≤1/q`.

All restrictions are explicit domain conditions; no cancellation, zero-location or RH premise is used.

## Dependency-closed paper proof

Split the cofactor sum into odd and even integers. The even part reindexes exactly by `d=2e` with `2e<Q`. Terms with even `e` vanish because `μ(2qe)=0`. For odd `a,e,q`, multiplicativity gives `μ(2a)=-μ(a)` and `μ(2qe)=-μ(qe)`; coprimality with `2a` excludes all even cofactors. This yields the three terms of `T_r`. Completing `2e<Q` to the entire odd range `e<Q` produces exactly `B_r`, with the displayed positive sign. The identity keeps `μ(qd)` even beyond the prime cutoff.

At `r=1`, clear the positive denominators to obtain the displayed rational formula. This proves positivity at comparable scales as well as in the far cone.

For the boundary estimate, `q≤2d` implies `b=2qd≥q²`. The existing exact first-order upper bound gives `0≤K_1(a,b)≤a/b²≤1/q³` whenever `a≤q`. The actual coefficient has absolute value at most one. At most `q` denominator terms give `1/q²` per numerator; at most `q` numerator terms give `1/q` for the block. This uses the nonlinear kernel directly, with no approximation error.

## What remains hard

At physical cutoff `d<q`, primality gives `μ(qd)=-μ(d)`. Thus the remaining sum has genuine coefficients `μ(a)μ(d)` on coprime odd cores. Kernel positivity supplies no sign or power saving for this sum. In particular, the coprimality-filtered symmetric kernel has zero diagonal on indices greater than one and positive off-diagonal entries on coprime pairs, so a generic positive-semidefinite argument is unavailable.

The C05 target `|P_1(q-1,q;q)|=O_ε(q^(-1/2+ε))` is still conjectural. No implication from this single block to the full RH receiver has been established here. This result removes the earlier far-cone linearization loss and isolates a subcritical cutoff boundary; it is not a proof of signed cancellation or RH.

## Lean certificate

Public theorems:

- `routeE_dyadicCofactorKernel_one`
- `routeE_dyadicCofactorKernel_one_pos`
- `routeE_integerPair_dyadicCofactor_exact`
- `routeE_oddCofactorBoundary_le`
- `routeE_integerPairBlock_dyadicCofactor_error`

Validation:

- Direct scratch `lake env lean`: passed, no warnings.
- `lake build --old GaloisForLFunctions.RHTower.RouteEDyadicCofactorKernel`: passed; only the new leaf built. Existing dependency warnings/info were replayed.
- `RHTower.lean`: import wired; no umbrella build.
- Final `lake env lean GaloisForLFunctions/RHTower/RouteEDyadicCofactorKernel.lean`: passed without warnings.
- All five `#print axioms` audits in a `/tmp` scratch file passed: exactly `[propext, Classical.choice, Quot.sound]`. No added axioms or proof gaps.
- Generated indexes refreshed twice. Follow-up `scripts/formal_tools.py lint --check-generated` failed on twelve unrelated unwired RHTower modules and two generated files changed during the audit (`LEAN_GAPS.md`, `LEAN_OVERVIEW.md`). The new leaf is wired and present in `LEAN_API.md`; no forbidden declarations were reported. Global lint has not passed.
