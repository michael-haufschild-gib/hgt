# Cofactor completion of the full nonlinear numerator block

- **ID:** MC-SOURCE-C03AB
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route MC, legacy E; `../1-in-progress/mc-source-cancellation-loop-2026-10-01.md`.
- **Statement:** At critical order, completing the full odd-core nonlinear numerator block below prime `q` costs at most `6/q`; the associated moment-sum completion costs at most `3A`.

## Source and target

Let `M(s,a,q)=Σ_(0<d<q,(d,a)=1) μ(d)d^(-s)` and

`S(A,s,q)=Σ_(1≤a≤A, a odd) μ(a)a [2M(s,2a,q)-M(s,a,q)]`.

This is the signed moment aggregate in the physical adjacent-pair linearization. The proved estimate is

`|S(A,s,Q)-S(A,s,q)|≤3A`, for every `s≥2`, `A<q≤Q`.

The moment estimate needs no prime-cutoff condition; the nonlinear source statement below uses the source’s prime denominator. Neither estimate assumes a sign law, unproved source bound, RH, or numerical experiment.

## Dependency-closed paper proof

For `q≥2`, the difference of the two moments is exactly the cofactor tail `q≤d<Q`. Since `|μ(d)|≤1` and `s≥2`, its absolute value is at most

`Σ_(q≤d<Q) 1/d² ≤ 1/(q-1)`.

The last inequality is the corpus's finite telescoping bound. The bracket `2M(s,2a,q)-M(s,a,q)` thus changes by at most `3/(q-1)`. For each `a<q`, multiplication by `|μ(a)|a≤a≤q-1` gives a change at most `3`. At most `A` odd numerators lie in `[1,A]`. Triangle inequality proves the result. The case `A=0` is empty.

## What moves, and what remains open

The cofactor cutoff is controllable at a linear error, below the proposed `A^(3/2+epsilon)` weighted cancellation scale. Future attempts on this aggregate need not assume a cofactor-tail bound or derive a new infinite-product theory to handle it.

This does **not** bound the original signed numerator sum, and the block condition `A<q` does not cover every numerator range of the full source. It also does not bound the nonlinear physical fibre error: the available absolute linearization estimate sums to `O(A³/q)`, which is still `O(A²)` at `q` proportional to `A`. Collective numerator cancellation and that nonlinear source regime remain open. No implication from this sector alone to RH is asserted.

## Stronger nonlinear source statement

Let `F_r(a,q;Q)` keep the original kernel and literal coefficient `μ(a)μ(qd)`, with only the cofactor cutoff extended from `q` to `Q`. Thus `F_r(a,q;q)` is definitionally the existing `routeEFixedOrderIntegerNumeratorFibre`. No coprimality of `q` and the newly added cofactors is assumed.

Let `P_r(A,q;Q)` sum `F_r(a,q;Q)+F_r(2a,q;Q)` over odd `a∈[1,A]`. For prime `q`, `1≤r≤2`, `A<q≤Q`,

`|P_r(A,q;Q)-P_r(A,q;q)|≤6A q^(-(r+1))`.

The source kernel is nonnegative and at most `r a(qd)^(-(r+1))`. Since `r≤2` and `d≥1`, its tail is at most `2a q^(-(r+1))/(q-1)` by the same reciprocal-square telescope. The two adjacent numerators cost at most `6a q^(-(r+1))/(q-1)≤6q^(-(r+1))` each. Summing proves the block statement without a linearization error term.

Taking `r=1`, `A=q-1` gives the critical physical bound

`|P_1(q-1,q;Q)-P_1(q-1,q;q)|≤6/q`.

Thus these completion errors sum to at most six times reciprocal-prime mass on any finite prime family. This improves the scope from the linearized moments to the exact physical nonlinear block. The signed original block remains uncontrolled.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/RouteECofactorCutoffStability.lean`.

- `RHTower.routeE_coprimeMobiusMoment_cutoff_tail`
- `RHTower.routeE_completedCoreMomentSum_cofactor_stability`
- `RHTower.routeE_integerNumeratorCutoffFibre_self`
- `RHTower.routeE_integerNumeratorCutoffFibre_tail`
- `RHTower.routeE_integerPairCutoffBlock_stability`
- `RHTower.routeE_integerPairCutoffBlock_critical_tail`

- `lake build --old GaloisForLFunctions.RHTower.RouteECofactorCutoffStability`: PASS; one new leaf built, existing dependencies replayed.
- `lake env lean GaloisForLFunctions/RHTower/RouteECofactorCutoffStability.lean`: PASS without output or warnings.
- Separate `/tmp` `#print axioms` audit of all six public theorems: exactly `[propext, Classical.choice, Quot.sound]`; no added or unproved axioms.
- Umbrella import added; `scripts/formal_tools.py index`: PASS.
- `scripts/formal_tools.py lint`: repository gate FAIL on ten unrelated modules unreachable from RHTower. This leaf is wired and not among the findings; no forbidden-declaration finding was reported. Unwired modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.

The audit does not establish RH or any bound on the complete signed source.
