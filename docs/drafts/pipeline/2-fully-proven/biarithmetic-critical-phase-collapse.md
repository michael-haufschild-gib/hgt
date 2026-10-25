# The digital phase family collapses continuously at critical contact

- **ID:** biarithmetic-critical-phase-collapse
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; source-family boundary law)
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** As the geometric source parameter decreases to `sqrt(5)` from above, every phase of its ordinary cofactor Gram family converges to the unique critical Gram table, uniformly in phase. The convergence extends to the full covariance of every two fixed critical Wiener kernels. An exact annular formula controls the phase oscillation.

## Objects and dependencies

For `1<a<5`, let `F_a` be the positive profile obtained by uniform refinement
of `a/(5-a) a^(-M) D_a(floor(5^M x))`. The dependency-closed construction and
source covariance comparison are on
[the quantitative profile card](biarithmetic-digital-profile-bounded-covariance-error.md).
In particular `F_a(5x)=a F_a(x)`, the profile is bounded on compact positive
intervals, and it is positive there. No new analytic source premise is added.

For positive integers `j,k`, write

`J_a(j,k)=integral_1^5 F_a(x/j)F_a(x/k) dx/x^2`,
`A_(a,tau)(j,k)=integral_1^tau F_a(x/j)F_a(x/k) dx/x^2`,
`q=a^2/5`.

Here `1<=tau<=5`; all annular integrals are finite, nonnegative, and
`0<=A_(a,tau)(j,k)<=J_a(j,k)`. Moreover `J_a(1,1)>0`.

## Exact annular formula

For `a>sqrt(5)`, substitute `x=5^(-m)y` on the annulus
`5^(-m)<x<=5^(1-m)`. The scaling law gives its integral as
`q^(-m) J_a(j,k)`. These annuli, `m>=1`, partition `(0,1]` up to endpoints.
Summing their nonnegative geometric series proves integrability at the
origin and the exact identity

`integral_0^1 F_a(x/j)F_a(x/k) dx/x^2 = J_a(j,k)/(q-1)`.

Consequently every strict-regime phase kernel has the nonsingular formula

`K_(a,tau)(j,k)
 =[J_a(j,k)+(q-1)A_(a,tau)(j,k)]
  /[J_a(1,1)+(q-1)A_(a,tau)(1,1)]`.

In particular `K_(a,1)=J_a/J_a(1,1)`. Subtract this value from the displayed
quotient. Both products in the difference numerator lie between zero and
`J_a(j,k)J_a(1,1)`, while its denominator is at least `J_a(1,1)^2`. Thus

`|K_(a,tau)(j,k)-K_(a,1)(j,k)| <= (q-1) K_(a,1)(j,k)`.

The usual cofactor radius bound follows directly in this model:
substitution `x=ju` gives
`integral_0^1 F_a(x/j)^2 dx/x^2
 =(1/j)integral_0^(1/j) F_a(u)^2 du/u^2`,
at most `1/j` times the base integral. Cauchy--Schwarz then yields
`0<=K_(a,tau)(j,k)<=1/sqrt(jk)` at every phase, with the same proof using
upper endpoint `tau`. Therefore the phase error above is at most
`(a^2/5-1)/sqrt(jk)`.

## Continuity of the annular coefficients

Fix a compact parameter interval `[a0,a1]` inside `(1,5)` and a bounded
nonnegative argument interval. The refinement tail is bounded uniformly by
`4 a0^(-M)/(a0-1)` before the factor `a/(5-a)`, which is also uniformly
bounded and continuous. At a fixed grid depth only finitely many integer
arguments occur. Each corresponding digit value is a polynomial in `a`,
so its dependence on `a` is uniform over all arguments in that interval.
Approximating by this finite grid and then letting `M` increase proves
that `a -> F_a` is continuous in the uniform norm on each bounded argument
interval. Continuity in the argument itself is neither claimed nor used.

For fixed `j,k`, this uniform convergence makes the products on `[1,5]`
converge uniformly. The finite measure `dx/x^2` proves continuity of
`J_a(j,k)` and uniform-in-`tau` boundedness of `A_(a,tau)(j,k)` near
`a*=sqrt(5)`. On `[1,5)`, the zeroth grid already gives
`F_a(x)>=a/(5-a)`; hence `J_a(1,1)` stays bounded away from zero near `a*`.

The annular formula now gives

`sup_(1<=tau<=5) |K_(a,tau)(j,k)-K_crit(j,k)| -> 0`,
`K_crit(j,k)=J_(a*)(j,k)/J_(a*)(1,1)`.

This is the critical source table already identified by the summable
annular error argument. The assertion is uniform over horizon phases;
no phase selection is needed while the parameter approaches criticality.

## Full Wiener covariances

For two fixed critical Wiener kernels `f,g`, their represented covariance
is the absolutely convergent double series

`sum_(j,k>=1) conj(f(j)) g(k) K_(a,tau)(j,k)`.

Its terms are dominated, uniformly in `a,tau`, by
`|f(j)|/sqrt(j) * |g(k)|/sqrt(k)`, a summable product. Given a tolerance,
choose a finite rectangle making the product tail small. The kernel bound
controls both critical and strict tails; on the finite rectangle the
entrywise convergence is uniform in `tau`. This proves uniform convergence
of the entire covariance to its critical value. It includes every fixed
signed or complex packet and every fixed infinite Wiener kernel.

## Scope, selectivity, and verification

This is a deformation law for the source-defined digital family. The
annular geometric sum and dominated-series argument are classical. The
corpus search returned unrelated phase-covariance and scaling results;
no matching digital critical-boundary theorem surfaced. No external
originality claim is made.

Convergence of normalized covariances does not imply convergence or
closedness of the actual payment domains. The critical partial-sum
criterion and its nonclosed boundary remain separate. No inference
about zeta zeros, spectral multiplicities, or operator-norm convergence
between different Hilbert carriers is made.

- [x] Dependency-closed paper proof and explicit uniform phase bound.
- [x] Full fixed-kernel Wiener covariance extension.
- [ ] Lean profile parameter continuity and annular integral identity.
- [ ] Lean actual Gram comparison and critical phase convergence.
- [ ] Direct source checks, transitive audits, and umbrella imports.
