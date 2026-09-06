# Actual logarithmic phase segments: scaling limit and sign obstruction

- **Stage:** 3-formalized
- **Type:** closed source theorems and [BRIDGE]
- **Module:** `formal/GaloisForLFunctions/RHTower/ArithmeticLogarithmicPhaseScaling.lean`
- **Namespace:** `RHTower.DeletionMixedRefinement`

RH remains unproved. This proves a sign obstruction for the actual finite Bernoulli remainder segments and a positive transfer theorem. It does not prove the cumulative logarithmic-clock inequality, any restriction at a zeta zero, or literature novelty.

## Exact source identities

Let `b(x)=(fract(x)^2-fract(x))/2`, integer `N>0`, and `s=sigma+i*t`. The literal fixed-anchor segment is

`A(s,N;a,b)=N^(-s)*integral_(N*exp(a/N)..N*exp(b/N)) b(x)*x^(-conjugate(s)-2) dx`.

The module proves its exact imaginary part, including the original anchor:

`Im A = N^(-sigma)*integral b(x)*x^(-sigma-2)*sin(t*log(x/N)) dx`.

At height `t=lambda*N`, the positive normalization of the real integral is

`S(sigma,lambda,N;a,b)=integral b(x)*(N/x)^(sigma+2)*sin(lambda*N*log(x/N)) dx`.

Two separately checked identities are

`S=N^(sigma+2)*integral b(x)*x^(-sigma-2)*sin(lambda*N*log(x/N)) dx`

and

`S=integral_(a..b)b(N*exp(v/N))*exp(-(sigma+1)*v/N)*sin(lambda*v) dv`.

Consequently `S=N^(2*sigma+2)*Im A` at this height. The phase is anchored at N throughout; it is not reset at the left endpoint of each later segment.

## Closed limit and actual complete-turn counterexample

For fixed `sigma>=-1`, fixed lambda, and `0<=a<=b`,

`S(sigma,lambda,n+1;a,b) -> integral_(a..b)b(v)*sin(lambda*v) dv`.

Integer periodicity first replaces the diverging argument by `(n+1)*(exp(v/(n+1))-1)`, which tends to v by the derivative of exp at zero. The quadratic is continuous, including at integer joins. Its boundedness and the bounded damping factor give finite-interval dominated convergence. This proof uses no asymptotic series or numerical data.

For `lambda=4*pi/3`, the already proved constant-speed integral on `[3/2,3]` is strictly positive. Thus, for each fixed `sigma>=-1`, the actual second logarithmic turn is positive for all sufficiently large N. In particular, beyond every lower bound M there is an integer `N>=M` with

`0<t=(4*pi/3)*N<2*pi*N`

and

`Im[N^(-s)*integral_(N*exp(2*pi/t)..N*exp(4*pi/t))b(x)*x^(-conjugate(s)-2) dx]>0`.

`not_all_complete_logarithmic_turns_nonpos` formally negates the universal nonpositive claim with the literal complex integral and the usual complete-turn endpoints. Taking any fixed positive sigma refutes the frozen B1 in its stated domain. Height varies with N; this is not a claim of cofinally many positive turns at one fixed height, and these heights are not asserted to be zeta zeros.

## Strongest positive survivor and boundary

For fixed `0<lambda<2*pi`, natural m and K, and `0<r<1` with `lambda*(m+r)=2*pi*K`, the actual prefix

`S(sigma,lambda,n+1;0,m+r)`

is strictly negative for every sufficiently large n, for each fixed `sigma>=-1`. This follows from the full exact constant-speed prefix formula and the source limit, not merely from a model analogy. No uniform cutoff over lambda, endpoint, or sigma is supplied.

When r=0 the limiting prefix is exactly zero. Convergence alone gives no sign. The independently frozen [first-variation identity F is now proved](arithmetic-clock-first-variation.md): the actual prefix has a strictly negative first-order coefficient. Together these theorems cover every fixed positive complete prefix, with a cutoff allowed to depend on the prefix. B2, C, D1, and E remain open. The arithmetic constraint on the unit remainder at every zero remains missing even if these tail conjectures are proved.

## Declarations and validation

Four definitions and twelve public theorems expose the source, its exact transformations, convergence, both eventual signs, and the literal complete-turn no-go. The main declarations are `tendsto_scaledLogarithmicSegment`, `anchoredLogarithmicSegment_im`, `eventually_scaledLogarithmic_prefix_neg`, `exists_arbitrarily_large_positive_anchored_second_turn`, and `not_all_complete_logarithmic_turns_nonpos`.

Scratch and source checks with `LEAN_NUM_THREADS=1 lake env lean` passed; the final source check had no warnings. The serialized leaf audit `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticLogarithmicPhaseScaling` passed, rebuilding only this leaf. All sixteen public declarations were audited from `/tmp/rh_clock_scale_axioms.lean`; each reports only `propext`, `Classical.choice`, and `Quot.sound`. No numerical certificate or added axiom occurs. The corpus index was refreshed and the new declarations were retrieved with the research tool. `python3 scripts/formal_tools.py lint --check-generated` passed with existing large-file warnings; output is in `/tmp/rh_clock_scale_lint.txt`. The new module is wired into the RH umbrella; no full or umbrella build ran. All owned Lean and Runpod processes completed.

Related: [frozen statements](../1-in-progress/arithmetic-clock-homotopy.md), [actual complete-turn no-go](../5-failed/arithmetic-logarithmic-block-sign.md), [Runpod clock diagnostics](../2-fully-proven/computations/arithmetic-clock-homotopy/REPORT.md).
