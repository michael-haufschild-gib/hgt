# Shape-independent logarithmic continuity and infinite-grid tail decay

Let f be any real compactly supported C² source, h its autocorrelation,
R=h(0), J its archimedean Lévy energy, and c=exp(-1/2). For R>0 write E=J/R.
Source regularity is the domain of the theorem; no extra analytic estimate is assumed.
This package concerns unweighted correlation tails, independently of any packet representation.

## Certified ingredients

`autocorr_krein_increment_sq_le` gives
(h(x)-h(y))² <= 2R(R-h(x-y)). Correlation is even and R>=0.
`autocorr_increment_mul_log_le` gives
c(R-h(d))(-log d) <= 4J for 0<d<=1.
`autocorr_logarithmicCeilLag_energy_bound` gives
c T(R-h(lag(T))) <= 4J for T>=0, where
n(T)=ceil(exp T) and lag(T)=log n(T)-T lies in [0,exp(-T)].
That result includes lag=0. If T>0 then n(T)>=2. Energy J is nonnegative.
These are proved in `KreinIncrementAndChordCascade.lean`,
`InfiniteGridTailRigidity.lean`, and `LogarithmicIncrementEnergy.lean`.

## Global logarithmic modulus [PROVED HERE]

For 0<d=|x-y|<=1,

    c(-log d)(h(x)-h(y))² <= 8 R J.

Proof. Evenness identifies h(x-y)=h(d). Multiply Krein's inequality by
c(-log d)>=0, then multiply the logarithmic increment bound by 2R>=0.
The middle quantities coincide. This applies at every location without any grid constraint.
For positive R, division by R² gives the same bound with normalized correlations and 8E.
In particular bounded normalized energy gives a common logarithmic continuity modulus.

The uniform quantifiers can be made explicit: given K>=0 and epsilon>0, set
delta=exp(-(1+8K/(c epsilon²))). Then 0<delta<=1. For any positive-mass source
with E<=K, and any x,y with |x-y|<delta, one has
|h(x)/R-h(y)/R|<epsilon. When x=y this is immediate. Otherwise
-log|x-y|>1+8K/(c epsilon²); a normalized difference of magnitude at least epsilon
would make the left side of the logarithmic modulus exceed 8K, a contradiction.
No grid constraint is needed for this assertion.

## Sampling error and arbitrary-source tail law [PROVED HERE]

For every T>=0, without any grid constraint,

    c T(h(T)-h(log n(T)))² <= 8 R J.

Proof. Apply Krein to log n(T),T; its increment is lag(T), and reversing
the order of the two correlation values does not change the square. Multiply by cT>=0
and use the ceiling-lag energy bound multiplied by 2R. Both factors are nonnegative.

If h(log n)=0 for every integer n>=2, then for every real T,

    c |T| h(T)² <= 8 R J,
    c |T| (h(T)/R)² <= 8 E                    (R>0).

Proof. For T>0 the sampling node is at least two, so its sample vanishes.
At T=0 the left side is zero and the right side is nonnegative. For negative T use
evenness and apply the positive result to |T|. Divide by R² for the normalized result.
Equivalently, for T!=0 the magnitude is at most sqrt(8 exp(1/2) E/|T|).

## Uniform family quantifiers [PROVED HERE]

For every K>=0 and epsilon>0, set

    A = 1 + 8K/(c epsilon²).

Then A>0, and for EVERY compact C² source with R>0, E<=K, and all grid zeros,
EVERY real T with |T|>=A satisfies |h(T)/R|<epsilon.

Proof. If |h(T)/R|>=epsilon then its square is at least epsilon². Since c>0 and
|T|>=A>0, the normalized tail inequality implies
c A epsilon² <= c |T| (h(T)/R)² <= 8E <= 8K.
But c A epsilon² = c epsilon²+8K > 8K, a contradiction.
The same radius works across changing source shapes, supports, and derivative norms.

## Decaying window energy [PROVED HERE]

For all-grid sources and 0<A<=B,

    c A integral_A^B h(x)² dx <= 8(B-A) R J.

Proof. On [A,B], c A h(x)² <= c x h(x)² <= 8 R J.
Continuity of h supplies interval integrability of both sides. Integrate this inequality
and move the constant cA outside the integral. This is a nonnegative oriented interval.

For every integer N>=2, choose A=log N and B=log(2N), whose difference is log 2:

    c log N integral_logN^log(2N) h(x)² dx <= 8 log 2 R J.

Thus the window integral is at most 8 exp(1/2) log 2 R J/log N. Unlike the existing
bound 2 R J, this tends to zero with N at fixed bounded R,J. Unlike the existing
quadratic-collar estimate, it needs no extra derivative/collar constant.

## Interpretation and remaining boundary

This closes the arbitrary-shape unweighted-tail question, with one uniform rate over
bounded normalized-energy classes. It also exposes a route to compactness of normalized
correlation functions: common local modulus plus common tails. Realization and energy
properties of a limit still require proof.

The inverse-square-root decay is too slow to control a cosh-weighted polar integral.
No uniform polar-tail tightness, optimal decay rate, or strict polar energy premium is claimed.
The constituent Krein inequality is classical; novelty here means the exact connected
application beyond the inspected corpus, not an exhaustive literature-priority claim.

Search: `/tmp/infinite-grid-arbitrary-tail-search.txt`; semantic coverage unmeasured,
older-generation inventory snapshot, useful candidates verified against their source files.

## Formal certificate

`InfiniteGridUniformTail.lean` passed a direct `lake --old env lean` leaf check without
diagnostics. Its ten public endpoints are:

- `autocorr_difference_sq_mul_log_le`
- `normalized_autocorr_difference_sq_mul_log_le`
- `exists_uniform_autocorr_continuity_radius`
- `autocorr_logarithmicCeilNode_error_sq_le`
- `autocorr_sq_mul_location_le_of_infinite_grid`
- `autocorr_sq_mul_abs_location_le_of_infinite_grid`
- `normalized_autocorr_sq_mul_abs_location_le_of_infinite_grid`
- `exists_uniform_infinite_grid_tail_radius`
- `integral_autocorr_sq_window_mul_left_le`
- `integral_autocorr_sq_dyadic_mul_log_le`

The private normalization helper is included transitively in the endpoint dependency audit.
All ten dependency audits passed with only `propext`, `Classical.choice`, and `Quot.sound`.
The umbrella import and all ten generated API entries are present. The connected package
counts once, bringing this research ledger to 7/100.

Logs: `/tmp/infinite-grid-uniform-tail-{leaf,axioms,index,lint}.log`.
The leaf check also emitted its `.olean` for the separate scratch import audit.
Global lint failed on four concurrent foreign modules missing umbrella reachability:
`RHTower.FermiNymanDyadicFoldGeometry`, `BiScaleUncertainty.CappedCollarArrayComparison`,
`BiScaleUncertainty.CappedCollarCutoffComparison`, and `BiScaleUncertainty.CappedSupportComparison`.
There is no lint error for this package. No full or umbrella build was run.
