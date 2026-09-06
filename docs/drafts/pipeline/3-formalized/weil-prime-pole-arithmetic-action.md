# Literal prime action on the two pole profiles

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Module:** `RHTower.CCMRestrictedWeilPrimePolarArithmeticAction`, wired into `RHTower.lean`; 12 public theorems, 3 definitions.
- **Sources:** exact prime compression and exponential profiles in `CCMRestrictedWeilBoundedRemainder`; actual cutoff theorem in `CCMRestrictedWeilPrimeOuterShell`; full constrained space in `CCMRestrictedWeilPolarGroundForcing`; current Chebyshev API and `MertensFirst`.

## Proof chain and remaining scope
Literal prime–Gamma action → arithmetic description of constrained ground forcing → exclude a constrained zero ground → positive ground at every aperture → weighted pole exclusion → RH. The literal prime action and its constrained arithmetic pairing are proved here. Identifying the full Gamma action on these truncated profiles and controlling the resulting signed arithmetic expression remain open. RH is not proved or disproved.

## Conjecture loop
1. Separate prime norms, including the strict joint bound, do not supply the signed Weil comparison. Pivot to exact action on the two pole profiles.
2. **Proved:** the two translation directions become different arithmetic cumulatives: Chebyshev `psi` and reciprocal von Mangoldt mass. All endpoint cutoffs and prime powers are retained.
3. **Proved:** the exponentially large Chebyshev main term is exactly the opposite excluded pole profile. Removing it preserves every constrained pairing.
4. **Proved:** remove the remaining constant pole component and separate a spatial ramp, the genuine Chebyshev error, and a reciprocal error bounded uniformly by `log 4+5`.
5. **Next conjecture:** the Gamma action cancels the spatial ramp in the complete pole pairing, leaving explicit Gamma boundary terms against arithmetic errors. This is not part of the formal result; see the open Gamma-boundary card.

## Dependency-closed paper proof [PROVED HERE]
Let `p±(x)=1_{[-a,a]} exp(±x/2)` and let `P_a` be the actual finite-prime operator. Put

`M(X)=sum_{2≤n≤floor X} Lambda(n)/n`,

`E_M(t)=M(exp t)-t`.

For every `n≥2`, transport by `+log n` sends the positive exponential to itself with scalar weight one after multiplication by `1/sqrt(n)`; transport by `-log n` has scalar weight `1/n`. On the original aperture, these terms are allowed precisely when `log n≤a-x` and `log n≤a+x`. The almost-everywhere compression formula, followed by a finite sum, therefore gives

`P_a p+(x)=1_{[-a,a]} exp(x/2)[psi(exp(a-x))+M(exp(a+x))]`.

Reflection commutes with literal prime transport and sends `p+` to `p-`. Hence

`P_a p-(x)=1_{[-a,a]} exp(-x/2)[M(exp(a-x))+psi(exp(a+x))]`.

The global source cutoff `floor(exp(2a))` reduces exactly to the two endpoint cutoffs because `a±x≤2a` inside the aperture. The omitted terms `n=0,1` have zero von Mangoldt weight. No prime counting approximation enters these identities.

Define `D_s=P_a p_s-exp(a)p_{-s}`, where `p_s(x)=1_{[-a,a]}exp(sx)`. The identity

`exp(x/2) exp(a-x)=exp(a) exp(-x/2)`

shows that `D_(1/2)` replaces `psi(Y)` by `psi(Y)-Y`, with `Y=exp(a-x)`. Both defects are reflected copies. Self-adjointness gives

`<p±,P_a f>=<D_(±1/2),f>`

for every `f` in the complete constrained form space, because the opposite exponential moment is zero.

For `t≥0`, set `N=floor(exp t)≥1`. The existing elementary Mertens theorem gives `|M(exp t)-log N|≤log 4+4`. Also `N≤exp t<N+1≤2N`, and `log(exp t/N)≤exp t/N-1≤1`. Thus

`|E_M(t)|≤log 4+5`.

Finally, removing `a p+` from `D_(1/2)` gives the exact physical representative

`D_(1/2)-a p+ = 1_{[-a,a]} exp(x/2)[psi(exp(a-x))-exp(a-x)+E_M(a+x)+x]`.

The removed `a p+` also pairs to zero. `inner_polar_prime_constrained_eq_arithmetic_integral` identifies the literal positive pole moment of `P_a f` with the integral of this real representative times the actual complex L² representative of `f`. The theorem quantifies over the completed constrained submodule itself; it assumes no ground regularity, source sign, or arithmetic estimate.

## Exact gain and boundary
The off-diagonal prime coupling to the pole profiles is now expressed through literal arithmetic errors. Its excluded main terms must not be counted as surviving constraint forces. The reciprocal channel is uniformly controlled after logarithmic subtraction; the Chebyshev error and the spatial ramp remain in the exact formula. A bound for this off-diagonal coupling alone does not orient the entire quadratic form or exclude a forced zero ground.

The searched prior corpus contained scalar critical-Mellin completed-error identities and abstract forcing coefficients, but no pointwise action of this actual operator on the pole profiles. No external novelty claim is made for elementary Mertens or exponential transport algebra.

## Verification
- Scratch `lake env lean /tmp/hgt-prime-pole.Xhbr4D4a/Integral.lean`: PASS.
- Named final audit `lake --old --log-level=error build GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimePolarArithmeticAction`: PASS (34 seconds).
- Scratch `Audit.lean`: all 12 public theorems use exactly `[propext, Classical.choice, Quot.sound]`; actual mathlib `RiemannHypothesis` printed.
- `git diff --check`: PASS.
- `python3 scripts/formal_tools.py lint`: PASS (large-file warnings only). The temporary shared-tree umbrella gap was resolved by its owning task; no unrelated source file was modified here.
- All owned Lean/build processes have completed. No full or umbrella build, numerical experiment, computational oracle, or added axiom.
