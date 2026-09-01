# HB pre-divisor Schwarz-polarized infinite-rank no-go

- **ID:** HB-SCHWARZ-POLARIZED-INFINITE-RANK
- **Stage:** 2-fully-proven
- **Type:** ROUTE-CLASS NO-GO + SHARP POSITIVE SURVIVOR
- **Source:** HB Hermitian/antiholomorphic survivor after analytic two-leg no-go

## RH chain attacked

Kill
`moving-horizon third mass + AIME -> finite-dimensional analytic right QNM packet + finite-dimensional analytic Schwarz left packet -> Hermitian/Schwarz-polarized coefficient -> forced susceptibility g(Re z) -> same-pole compensation/opposite HB sign -> Ward extinction -> RH`.

## Internal frontier

- `[CORPUS]` `d4HBPreDivisorAnalyticLeftQNMTwoLegRouteKilled`: no jointly holomorphic complex-bilinear two-leg realization exists.
- `[CORPUS]` `thetaCuspHawkingSchwarzPolarizedAnomaly_diagonal`: an independent Schwarz variable exactly recovers Hermitian diagonal pairing.
- `[CORPUS]` `finiteDimensional_translationSpan_of_separationRank`: finite separation rank forces finite translate rank.
- `[CORPUS]` `archHankelKernel_not_hasPositiveOpenSquareSeparationRankAtMost`: the corpus already uses pole-separated translate independence for a different Suzuki kernel.
- `[CORPUS]` `d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal`: the exact horizontal susceptibility has a rational complex continuation.

No corpus theorem determines separation rank of the pre-divisor AIME/third-mass susceptibility.

## External frontier through August 2026

- `[LITERATURE]` Classical Kronecker theory classifies finite-rank Hankel kernels as exponential polynomials; see Yafaev, *On finite rank Hankel operators*, JFA 2015, https://doi.org/10.1016/j.jfa.2014.12.005.
- `[LITERATURE]` Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935, construct conserved complex-bilinear QNM projections, not a finite-rank Hermitian AIME susceptibility.
- `[LITERATURE]` Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, establish cubic AIME from moving-background mode projection, not the reflected pre-divisor compensation kernel.
- `[LITERATURE]` Aruquipa--Casals--Nolan, arXiv:2604.21219, construct a regularized Schwarzschild Teukolsky Green function; no finite-separation-rank optical compensation is derived.

Abstract finite-rank Hankel rigidity is known. Exact pole-rank classification of this susceptibility and its HB consequence were not found.

## Conjecture loop

1. `[FALSIFIED]` Same-variable Hermitianization can give the required regular complex-frequency optical landing. Corpus local-open Hermitian no-go kills it: a same-variable Hermitian anomaly is real up to phase.
2. `[CONJECTURE]` Passing to the canonical independent Schwarz variable rescues the route in a finite-dimensional QNM sector.
3. `[PAPER-PROVED]` It does not: the exact Schwarz-polarized susceptibility kernel has infinite separation rank already on `(0,1/2)^2`.

## Exact claim

Let `G` be `d4PreDivisorOpticalCancellationHolomorphicContinuation` and

`K(x,y) = G((x+y)/2)`.

For every `r`, there are no functions `f_k,g_k : R -> C`, `k<r`, satisfying

`K(x,y) = sum_{k<r} f_k(x) g_k(y)`

for all `0<x<1/2` and `0<y<1/2`.

## Proof `[PAPER-PROVED]`

Put

`A(t)=t(3-t)`, `B(t)=(1-t)(2+t)`,

`N(t)=A(t)^2(2-B(t))+B(t)^2(2-A(t))+2A(t)B(t)`,

`P(t)=54 N(t)(2-t)(t+1)`, and `D(t)=A(t)^2B(t)^2`.

On `0<t<1`, direct cancellation of the two nonzero horizon shifts gives `G(t)=P(t)/D(t)`. Also `P(0)=864`, while the roots of `D` are exactly `0,3,1,-2`.

First prove translate independence. Let distinct `y_j` lie in `(0,1/2)` and suppose

`sum_j c_j K(x,y_j)=0`

for every `x` in `(0,1/2)`. All denominators are nonzero there. Multiplication by their product gives the polynomial

`C(z)=sum_j c_j P((z+y_j)/2) product_{k != j} D((z+y_k)/2)`.

It vanishes on a real interval, hence is identically zero. Evaluate at `z=-y_j`. Every term except the `j`-term contains `D(0)` and vanishes. In the surviving term, `P(0)=864 != 0`; for `k != j`, `(y_k-y_j)/2` lies in `(-1/4,1/4)\{0}`, hence misses all four roots of `D`. Thus `c_j=0`. Every finite family of distinct translates is linearly independent.

Now assume a separation-rank-`r` representation. Choose `r+1` distinct `y_j` in `(0,1/2)`. The `r+1` vectors `(g_k(y_j))_{k<r}` in `C^r` are linearly dependent, so some nonzero `c` satisfies `sum_j c_j g_k(y_j)=0` for every `k`. Then

`sum_j c_j K(x,y_j) = sum_k f_k(x) sum_j c_j g_k(y_j) = 0`

for every `x` in `(0,1/2)`, contradicting translate independence.

No regularity of the separated factors is used.

## Hostile audit

- The theorem is not the classical Kronecker theorem restated: proof is direct and coefficient-faithful for the exact corpus susceptibility. Kronecker is parent theory and confirms normalization.
- No Xi-zero location, RH, finite sample, numerical pole check, positivity, or completeness hypothesis enters.
- Totalized division at boundary roots is irrelevant: cancellation is used only on `(0,1)`, then the cleared polynomial is evaluated at boundary pole coordinates.
- Difference collisions cannot occur: selected shifts have diameter `<1/2`, whereas nonzero horizon-root gaps from zero are `1,2,3`.
- Scope is exact: finite-dimensional Schwarz-polarized/Hermitian channels die; infinite-dimensional, distributional, support-changing, or nonseparated channels survive.

Verdict: `SURVIVES PRELIMINARY ATTACK`; dependency-closed paper proof.

## Positive survivor

`[PAPER-PROVED]` Any exact Schwarz-polarized HB compensation has infinite separation/Schmidt rank on every physical neighborhood containing this square. Thus a surviving Hermitian left-QNM construction needs an infinite-dimensional channel before any PDE, positivity, or passivity question arises.
