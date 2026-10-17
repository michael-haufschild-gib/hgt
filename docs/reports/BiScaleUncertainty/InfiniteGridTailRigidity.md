# Distant-copy detection on the infinite logarithmic grid

## Objects and exact scope

Let `f` be a real continuous compactly supported source, and set

\[
h(x)=\int_{\mathbb R} f(u)f(u+x)\,du,\qquad R=h(0),
\quad g_{a,T}(u)=f(u)-af(u-T).
\]

All integrals below are ordinary Lebesgue integrals. Products of translates are continuous
and compactly supported, hence integrable. The correlation is continuous, even, and compactly
supported; choose `D>0` with `h(x)=0` for `|x|>D`. Its origin value is the integral of `f²`.
For `a=exp(-T/2)`, `g` is the canonical polar copy. Its positive half-exponential source moment
vanishes by translation and `exp(-T/2) exp(T/2)=1`. For compact smooth sources this also gives
the hyperbolic correlation balance already proved in `DistantCopyPolarEnforcement.lean`.

## Theorem 1: canonical detecting node [PROVED HERE]

Define
\[
n_T=\lceil e^T\rceil\in\mathbb N,\qquad \delta_T=\log n_T-T.
\]
For every real `T`, `n_T>=1` and `0<=delta_T<=exp(-T)`. For `T>0`, `n_T>=2`.
Whenever `T>D`,
\[
h_{g_{a,T}}(\log n_T)=-a h(\delta_T). \tag{1}
\]

**Proof.** The ceiling bounds give `exp T <= n_T < exp T+1`. Monotonicity of the logarithm
gives the lower displacement bound. Writing `delta_T=log(n_T/exp T)` and using
`log z<=z-1` for `z>0` gives
`delta_T < (exp T+1)/exp T-1=exp(-T)`; the weak bound stated above follows.
For `T>0`, `exp T>1`, so its ceiling is at least two.
Expanding the four products in the correlation and translating the integration variable gives
\[
h_{g_{a,T}}(x)=(1+a^2)h(x)-a(h(x-T)+h(x+T)).
\]
At `x=log n_T>=T>D`, both `h(x)` and `h(x+T)` vanish. This proves (1). ∎

## Theorem 2: universal rescaled defect [PROVED HERE]

For every such source,
\[
\lim_{T\to\infty} e^{T/2}h_{g_{e^{-T/2},T}}(\log n_T)=-R. \tag{2}
\]
If `R>0`, there is `T0` such that for all `T>=T0`,
\[
n_T\ge2,\qquad
h_{g_{e^{-T/2},T}}(\log n_T)<-\tfrac12e^{-T/2}R<0. \tag{3}
\]
Thus no fixed nonzero source can enforce the full infinite zero grid by sufficiently distant
canonical polar copies. The conclusion is an unconditional dichotomy for compact continuous
sources: `R=0`, or (3) holds eventually. It does not require the original source to satisfy any
grid zeros.

**Proof.** Theorem 1 implies `delta_T->0`. Continuity gives `h(delta_T)->R`.
For all sufficiently large `T`, multiplying (1) by `exp(T/2)` cancels its attenuation exactly,
so its limit is `-R`. If `R>0`, eventually `h(delta_T)>R/2`; multiplying by the negative
number `-exp(-T/2)` gives (3). Finally `R>=0`, so the dichotomy follows. ∎

## Theorem 3: exact price of preserving the tail sample [PROVED HERE]

For any `T>D`, any `a!=0`, if `h_{g_{a,T}}(log n_T)=0`, then
\[
h(\delta_T)=0,\qquad
\int_{\mathbb R}|f(u+\delta_T)-f(u)|^2\,du=2R,
\qquad 0\le\delta_T\le e^{-T}. \tag{4}
\]

**Proof.** Equation (1) and `a!=0` force `h(delta_T)=0`. Expanding the square and translating
the two square integrals gives `2(R-h(delta_T))=2R`. ∎

This identifies the missing compactness condition for families: even after normalization,
their translation increments cannot be uniformly small near zero if their separated copies
preserve the infinite grid while `T` tends to infinity. The obstruction is independent of
how small the nonzero copy coefficient is.

## What is and is not established

- Finite-grid preservation and infinite-grid failure are compatible: the detecting index grows
  like `exp T`, outside every fixed truncation.
- The sample defect is exponentially small, but rescaling by the polar growth exposes the
  nonzero limit (2). Small unweighted sampling error therefore does not certify polar-tail control.
- Theorem 3 alone constrains changing sources; Theorems 4–5 below turn it into an energy bound.
- No result here identifies infinite-grid polar/nonpolar infima, proves a polar premium, or
  treats arbitrary many-copy cancellation.
- Counts: all five theorems and the error-sensitive law form **one** mathematical package.

## Prior-art and verification boundary

Internal search located the exact copy identity and finite-grid invariance in
`DistantCopyPolarEnforcement.lean`, and shrinking-collar dyadic-window L² control in
`MultiCosetGramPackingAndNyquistDensity.lean`. Neither result states the canonical tail-sample
identity, rescaled defect limit, or changing-source displacement obstruction above.
Search results are source-only with unmeasured semantic coverage; compilation is audited separately.

Concurrent corpus work in `AsymptoticTailCoercivityAndNyquistTrap5Closure.lean` derives weighted
dyadic polar-mass estimates from an explicit quadratic origin-collar bound `Delta(y)<=K y²`.
Its derivative-free version retains a factor `N` multiplying a shrinking-collar Levy integral.
Those statements do not give the uniform logarithmic translation modulus or the linear cost
for arbitrary changing two-copy sources proved below. Their compilation status is not asserted here.

Krein-type continuity inequalities are classical; see the primary paper
[Pevnyi and Sitnik, Inequalities of M. G. Krein, Yu. V. Linnik and E. A. Gorin for positive
definite functions](https://arxiv.org/abs/1609.01218). The present proof uses only elementary
ceiling geometry, the existing correlation identity, and continuity. It resolves a concrete
gap in this corpus; exhaustive external novelty is not claimed.

## Theorem 4: derivative-free logarithmic increment bound [PROVED HERE]

Write `Delta(x)=R-h(x)` and `J(f)=integral_0^infinity Delta(x) w(x) dx`. For a compact
`C²` source this energy is finite by the existing Levy-integrability theorem. For every
`0<delta<=b`,
\[
\Delta(\delta)\int_\delta^b w(x)\,dx\le4J(f). \tag{5}
\]
In fact the right side can be replaced by `4 integral_0^b Delta(x)w(x) dx`.

**Proof.** The translation chord inequality gives
`Delta(delta)<=2 Delta(x)+2 Delta(x-delta)`. The weight is positive and decreasing on
`(0,infinity)`: in `w(x)=2exp(-x/2)/(1-exp(-2x))`, the numerator decreases and the positive
denominator increases. Multiply the chord inequality by `w(x)` and integrate from `delta`
to `b`. The first term is bounded by twice the energy on `(0,b)`. In the second term,
put `u=x-delta`; monotonicity gives `w(u+delta)<=w(u)` for `u>0`, so this term is also
bounded by twice that energy. Endpoints have measure zero. All terms are nonnegative and
dominated by integrable energy densities; the constant-weight integral is finite because
`delta>0`. This proves both assertions. ∎

For `0<x<=1`, the elementary inequality `exp(-2x)>=1-2x` yields
\[
w(x)\ge\frac{e^{-x/2}}x\ge\frac{e^{-1/2}}x.
\]
Consequently (5) implies the explicit uniform modulus
\[
e^{-1/2}\Delta(\delta)\log(1/\delta)\le4J(f)
\qquad(0<\delta\le1). \tag{6}
\]
For completeness, integrate the preceding weight bound to obtain
`integral_delta^1 w >= exp(-1/2)(-log delta)` and use `Delta(delta)>=0` in (5).

## Theorem 5: linear energy cost of infinite-grid two-copy escape [PROVED HERE]

Let `f` be a nonzero compact `C²` source, with correlation support radius `D>=0`. Let
`T>D+1` and `a!=0`. If `g=g_{a,T}` satisfies even the single distant constraint
`h_g(log n_T)=0`, then
\[
\frac{J(f)}{h_f(0)}\ \ge\ \frac{e^{-1/2}}4T,
\qquad
\frac{J(g)}{h_g(0)}\ \ge\ \frac{e^{-1/2}}4T. \tag{7}
\]
The second conclusion also holds if the source and coefficient depend on `T`.
In particular every infinite-grid two-copy source in this separated regime obeys (7),
including canonical polar copies.

**Proof.** By Theorem 3, `h_f(delta_T)=0` and `0<=delta_T<=exp(-T)<1`.
If `delta_T=0`, this would give `h_f(0)=0`, contradicting nonzero energy. Thus `delta_T>0`.
Since `T>D+1`, the local-copy identity holds on `[-1,1]`:
`h_g(x)=(1+a²)h_f(x)`. Hence `h_g(0)=(1+a²)h_f(0)>0` and `h_g(delta_T)=0`.
Apply (6) to each of `f,g`, with `Delta(delta_T)=h(0)`. Finally
`delta_T<=exp(-T)` implies `log(1/delta_T)>=T`. Divide by the positive origin energy. ∎

This upgrades fixed-source failure to an energy obstruction for arbitrary changing sources.
It uses the full singular Levy integral, so it does not discard the physical-space mechanism
identified in Trap 1. It does not require a common bound on `D`, only the stated separation.
No sharpness is claimed for the coefficient `exp(-1/2)/4`.

The two-copy obstruction remains narrower than the full infinite-grid polar problem. Multiple
packets can contribute interfering cross-correlations at the detecting node; arbitrary polar
sources need not admit a separated-copy representation. Those cases remain open.

For `a>=0`, the same argument without assuming a zero sample proves the error-sensitive law
\[
 e^{-1/2}T\bigl(aR+h_{g_{a,T}}(\log n_T)\bigr)\le4aJ(f)\qquad(T>D).
\]
Indeed the expression in parentheses is exactly `a Delta(delta_T)`; (6) and the grid mesh
bound apply. If `delta_T=0`, that expression is zero and the inequality follows from `J>=0`.
For `a>0,R>0,T>0`, this says
`h_g(log n_T)/(aR)<=-1+4 exp(1/2) J(f)/(R T)`.
Thus bounded normalized base energy yields a uniform relative negative sample, not merely
failure of an exact zero. This is part of the same theorem package.

External parent theory: logarithmic energy spaces already have compactness mechanisms;
see [Laptev–Weth, Spectral properties of the logarithmic Laplacian, §1–2](https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf).
The new corpus application is the explicit coupling of a tail sample, its exponentially small
displacement, and a linear cost for the actual copy source. The generic energy-space idea is
not claimed as new.

## Lean certificates

The complete package is formalized in two leaves:

- `InfiniteGridTailRigidity.lean`: canonical mesh bounds, exact tail sample,
  `tendsto_rescaled_polarCopy_sample`, `polarCopy_infinite_grid_dichotomy`, and
  `subtractCopy_zero_forces_translation_defect`. These require only compact continuous sources.
- `LogarithmicIncrementEnergy.lean`: `autocorr_increment_mul_weight_integral_le_local`
  proves the stronger local version of (5); `autocorr_increment_mul_log_le` proves (6);
  `subtractCopy_tail_sample_energy_bound` proves the error-sensitive law;
  `subtractCopy_zero_linear_energy_cost` proves the division-free form of (7).
  `exists_subtractCopy_infinite_grid_energy_barrier` derives the support radius for every
  compact C² source. No modulus, energy estimate, or support radius is assumed at that endpoint.

Both leaves passed direct `lake --old env lean <leaf> -o <leaf.olean>` audits.
All 22 new theorems passed a scratch `#print axioms` audit: only `propext`, `Classical.choice`,
and `Quot.sound`. Both imports are wired into the BiScaleUncertainty umbrella; generated indexes
include both modules. No full or umbrella build was run.

Evidence: `/tmp/infinite-grid-energy-build.log`, `/tmp/infinite-grid-final-axioms.log`,
`/tmp/infinite_grid_final_axioms.lean`, and `/tmp/infinite-grid-index.log`.
Global `scripts/formal_tools.py lint` failed on three concurrent modules absent from the umbrella:
`AsymptoticTailCoercivityAndNyquistTrap5Closure`, `MultiCosetGramPackingAndNyquistDensity`,
and `ProducerConsumerDualityAndNymanBeurlingBridge`. No task-owned lint error was reported.
These other modules were not modified.
