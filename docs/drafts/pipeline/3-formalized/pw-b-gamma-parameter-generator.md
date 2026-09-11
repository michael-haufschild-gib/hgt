# PW-B actual Gamma coefficient-parameter generator

- **ID:** PW-B-GAMMA-PARAMETER-GENERATOR-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** At every positive ray scale the actual Gamma/Möbius source is complex differentiable at every coefficient parameter. Its derivative at zero is exactly the complete von Mangoldt current of its original preimage, and that derivative is eventually positive in real part as the ray scale grows.

## Actual family and proof

Keep `Q(x)=sqrt(x)*exp(-x)`, the canonical preimage
`M(x)=sum_n mu(n)*Q(n*x)`, and full forcing
`E(x)=sum_n -mu(n)*log(n)*Q(n*x)` from the
[actual-source extension](pw-b-gamma-mobius-current.md).
Define, for a complex coefficient parameter `b`,

`M_b(x)=sum_n mu(n)*exp(-b*log(n))*Q(n*x)`.

The zero index vanishes. At `b=0`, this is exactly `M(x)`.
The complete derivative series is

`E_b(x)=sum_n -log(n)*mu(n)*exp(-b*log(n))*Q(n*x)`.

For each fixed `x>0` and every natural `k`, the series
`sum_n n^k*|Q(n*x)|` converges. On the positive indices,
`sqrt(n)<=n` and `sqrt(n*x)=sqrt(n)*sqrt(x)`, giving the summable
majorant `sqrt(x)*n^(k+1)*exp(-x*n)`. The zero index is handled separately.
This uses the current mathlib theorem
`Real.summable_pow_mul_exp_neg_nat_mul`.

On the complex parameter ball `|b|<N`,

`|exp(-b*log(n))| = exp(-Re(b)*log(n)) <= n^N` for `n>=1`.

Since `|mu(n)|<=1` and `0<=log(n)<=n`, the summands of `M_b` and their
complex derivatives are bounded respectively by
`n^N*|Q(n*x)|` and `n^(N+1)*|Q(n*x)|`. These are common summable
majorants on the whole ball, not unrelated bounds at individual parameters.
Each term has its asserted complex derivative. The series converges at
zero, and the ball is open and preconnected. Applying
`hasDerivAt_tsum_of_isPreconnected` proves

`partial_b M_b(x)=E_b(x)`

throughout the ball. Every complex parameter lies in such a ball, proving
complex differentiability everywhere and admission of both full series.
The exact zero-parameter specialization is

`partial_b M_b(x)|_(b=0) = E(x) = sum_n Lambda(n)*M(n*x)`.

The last equality uses the admitted arithmetic convolution identity, with
every von Mangoldt coefficient retained. No positive-parameter collar,
stronger Schwartz-class premise or assumed analytic interchange occurs.

The [leading-prime theorem](pw-b-gamma-leading-forcing.md) proves `Re(E(x))>0`
for all sufficiently large `x`. Thus the actual parameter derivative is
eventually positive in real part, and `b -> M_b(x)` is nonconstant for all
such scales. Entire parameter admission and the exact generator identity
do not supply stationarity.

## Prior theorem and the genuine extension

`DeningerAdiabaticGreenStokes.lean` already has a parameter-derivative
construction for `DeningerMeyerSource` in `L¹`, at strictly positive real
parameters. Its derivative majorant requires a collar `b>=d>0` and sums
`log(n)/n^(d+1)`. That theorem cannot be specialized to the literal Gamma
source at zero. The present extension instead proves the actual Gamma
series pointwise in the ray scale, on every bounded **complex** parameter
region, including zero. It does not assert an `L¹` derivative at zero.

## Scope and next hard obstacle

Literal PW response -> FE partner imbalance -> positive Deninger Ward
transmutation -> independently source-forced fixed-grade balance -> RH
remains the proof chain. The arithmetic logarithmic current is now an
actual coefficient-parameter derivative. The earlier exact forcing defects
show why it cannot simply be relabeled a raw spatial Gamma forcing.
Identifying this coefficient parameter with the spectral Ward parameter,
with the correct global domain and complete reflected source, remains open.
RH is not proved and PW-B stays active.

All analytic statements here fix `x>0`. Their bounds depend on `x`; they do
not justify integration through `x=0`, global finite energy, or Mellin
continuation. The existing ordinary Möbius--Laplace bridge requires an
actual `MemLp` base-energy hypothesis for continuation and zero exclusion.
Pointwise complex differentiability cannot discharge that hypothesis.

The [global absolute-admission successor](pw-b-gamma-global-absolute-admission.md)
now proves the sharp boundary. With `C=Gamma(3/2)>0`, each actual atom has
`L¹(dx)` norm `C*|mu(n)|/n^(Re(b)+1)`; derivative atoms retain `log(n)`.
Both norm sums converge exactly when `Re(b)>0`. Prime restriction proves
necessity; p-series and log-p-series prove sufficiency. Both complete
sources are integrable in that open region, with justified integral
interchange. Failure of those norm sums at zero does not exclude an
integrable signed sum. The next signed Abel assembly must retain the
Gamma derivative window and terminal term.

The next paper candidate is the full source-transform identity
`Mellin(M_b)(s)=Gamma(s+1/2)/zeta(s+b)` in the absolute-convergence region
`Re(s)>-1/2`, `Re(s+b)>1`. Both restrictions and the half-density shift
must be retained. At `b=1/2`, the source itself should be
`sqrt(x)*sum_n mu(n)*exp(-n*x)`, connecting to the existing ordinary source.
These are next candidates, not Lean results of this leaf. Extending the
global domain toward the zero-bearing region requires new signed
arithmetic control; a conditional continuation endpoint is not that control.

## Verification

All 14 public theorems passed scratch and direct leaf checking, targeted
final build, axiom audit and formal lint. Every theorem uses only `propext`,
`Classical.choice` and `Quot.sound`; no added axioms, proof holes or numerical
experiments. The new leaf builds cleanly. Dependency replay includes an
existing informational `ring_nf` hint. Formal indices contain all 14
theorems and two public definitions; name-collision and diff checks passed.
All owned Lean and search processes finished.

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusParameterGenerator.lean`.
- Closed capstone: `RHTower.pwGammaMobiusTilt_entire_generator_closed`.
- Actual derivative: `pwGammaMobiusTilt_hasDerivAt`.
- Euler identification: `pwGammaMobiusTilt_hasDerivAt_euler_zero`.
- Nonstationarity: `pwGammaMobiusTilt_deriv_zero_eventually_pos` and
  `pwGammaMobiusTilt_eventually_nonconstant`.
- Scratch: `/tmp/pwb-gamma-parameter.lean`; axiom scratch:
  `/tmp/pwb-gamma-parameter-axioms.lean`.
- Logs: `/tmp/pwb-gamma-parameter-{scratch,direct,build,axioms,lint,index}.txt`.
- Umbrella import wired. All Lean checks used `lake env lean`; the final
  `lake build` named only this leaf. No umbrella/full build ran.

## Corpus and external method audit

Five deep searches cover the parameter source, differentiation methods,
complex local bounds, Euler convolution and the Mellin endpoint. Their
partial coverage and retrieved proposals are saved in
`../1-in-progress/pw-b-gamma-parameter-searches.json`.
The useful transfer is the common-derivative-majorant method of the prior
Deninger adiabatic theorem and current mathlib smooth-series API. Formal
power-series differentiation, generic ODE decay, exponential Taylor error
bounds and quantum parameter-shift formulas do not by themselves justify
this analytic interchange. Private Gaussian Mellin lemmas expose a proof
method but are not public callable endpoints. Reciprocal-zeta series
identities retain their right-half-plane premises.

Broad arXiv friction, entrainment and screening searches found the July
[protein-translation entrainment paper](https://arxiv.org/html/2607.25435v1).
Its sections IV-C--E derive weighted telescoping cancellations and use a
periodic quadratic energy to express the output deficit as a sum of
nonnegative terms. Zero deficit forces a common modulation of all rates.
This offers a possible global nonlinear method, but requires positive
chain states, the specific flow equations and periodic endpoint matching.
Those hypotheses have not been derived for the signed arithmetic source;
discarding Möbius signs would change that source. No external paper is a
formal premise, and no numerical examples were used as evidence.
