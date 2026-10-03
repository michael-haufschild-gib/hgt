# RP: positive damping and the natural initial-prime core

- **ID:** RP-47-DAMPED-INITIAL
- **Stage:** 5-failed (full-ray growing-core replacement only)
- **Type:** PROVED obstruction with formalized positive physical-tail survivor
- **Source:** rh-current-frontier-map.md, Route RP; MobiusDivisorPrimeBlockEnergyEscape
- **Statement:** For each 0<epsilon<1, A>0, and real B,
  y^(-B)*integral_(y^A)^infinity H_{P_y}(x)^2*x^(-3-epsilon) dx tends
  to infinity, with P_y containing every prime at most y.

## Goal

Test whether positive damping repairs the full-ray growing-core energy
strategy for the native signed RP payment. The existing initial-core
escape is undamped. Arbitrary late-prime extensions already have a local
shell obstruction, so merely reweighting those is not new frontier work.
The proved statement retains every earlier prime and uses the literal
processed continuous divisor head. It does not concern the exhaustive
physical cutoff H_full and cannot falsify RH.

## Corpus-grounded paper proof

Fix 0<epsilon<1. Set alpha=(5+epsilon)/4 and sigma=alpha-1/2.
Then 1+epsilon/2<alpha<3/2, 1/2<sigma<1, and
kappa=2*alpha-2-epsilon=(1-epsilon)/2>0. For each finite core P,
the corpus square-root envelope makes the damped energy finite.
Weighted Cauchy--Schwarz at s=alpha+i*t gives

    E_epsilon(P) >= kappa*|Mellin(H_P)(-s)|^2.

Here the complementary square integral is exactly
integral_1^infinity x^(1+epsilon-2*alpha) dx=1/kappa. There is no
Plancherel limit, unproved source admission, or infinite Euler product.

The exact finite-core Mellin identity gives

    Mellin(H_P)(-s)=Mellin(U)(-s)*product_{p in P}(1-p^(-sigma-i*t)).

U is nonnegative, positive on (1,2), and has an admitted Mellin transform
for alpha>1/2. Thus its real moment at alpha is strictly positive; continuity
gives a positive lower bound at t=pi/log y for large y.

Take the entire initial core P_y and this frequency. Primes p>=sqrt y
have nonpositive cosine and therefore do not contract. The terminal window
y/3<p<=y has cosine<=-1/2, so each squared factor is at least 1+y^(-sigma).
Every prime has radius p^(-sigma)<=p^(-1/2)<=3/4; the same elementary
logarithmic estimate as the existing undamped proof gives squared factor
at least exp(-8*p^(-sigma)). The complete smaller-prime loss is bounded by

    sum_{p<sqrt y} p^(-sigma)
      <= y^((1-sigma)/2)*(1+log(sqrt y)).

Indeed p^(-sigma)=p^(1-sigma)/p, so monotonicity and the elementary harmonic
bound suffice; no prime cancellation is assumed in this adverse part.
The existing prime-window count and log(1+z)>=z/2 for 0<=z<=1 give

    log |Euler(P_y,s)|^2
      >= y^(1-sigma)/(6*log y)
          -8*y^((1-sigma)/2)*(1+log(sqrt y)).

Since 1-sigma>0, the positive term dominates and tends to infinity.
Weighted Cauchy--Schwarz therefore proves full-ray energy escape faster
than every power of y. Every displayed source/domain identification has
now passed Lean, including admission of each finite-core positive moment.

## Positive survivor and surviving hard problem

The substantive survivor is a physical localization statement: for each
fixed A>0 the energy beyond y^A also tends to infinity. The corpus bound
|H_P(x)|<=(3/5)*x*sqrt x gives every prefix through X a bound at most
(9/25)*X for epsilon>0. The Mellin lower bound above is exponential in a
positive power of y divided by log y, so it exceeds every polynomial.
The Lean theorem retains an additional arbitrary polynomial rescaling
y^(-B) of that tail. Consequently the natural initial core requires a joint physical
cutoff; damping alone does not permit replacing it by its full-ray limit.
This leaves the actual finite-history signed estimate open.

The complementary strict regime is also explicit: for epsilon>1 the same
core-uniform physical envelope gives E_epsilon(P)<=9/(25*(epsilon-1)) for
every finite core P. The result therefore separates all epsilon in(0,1)
from all epsilon>1. No assertion about the endpoint epsilon=1 is made.

## Gates

- [x] Literal source, complete initial prime core, positive damping fixed.
- [x] Paper source/domain proof audited against retrieved corpus and source;
  search coverage limitations recorded in the working log.
- [x] Exact energy and tail statements formalized; leaf and axiom audits.
- [x] Umbrella wired; no full build.

## Formal certificate and no-go closure

Module: formal/GaloisForLFunctions/RHTower/RoutePDampedInitialPrimeEscape.lean.

- routeP_damped_initial_prime_scaled_tail_escape: literal positive energy
  beyond every polynomial prime-scale cutoff, after every polynomial
  rescaling, tends to infinity for each damping in(0,1).
- routeP_strong_damping_core_uniform_bound: the complementary strict
  regime epsilon>1 admits the stated uniform bound for every finite core.

Final foreground audit90367 exited0 without diagnostics:

    lake --old env lean GaloisForLFunctions/RHTower/RoutePDampedInitialPrimeEscape.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/RoutePDampedInitialPrimeEscape.olean

Axiom audit41983 in /tmp exited0; both public theorems use only propext,
Classical.choice, Quot.sound. One RHTower umbrella import added; no umbrella
or full build. Lint93355 exited1 on eleven unrelated unreachable modules,
listed in the main working log; no finding for this leaf. Global lint is
not green. No numerical experiment, added axiom, proof hole, or resource
limit override was used. No literature novelty claim is made.

The killing mechanism is amplification of a strictly interior Mellin
functional along the complete initial prime core, including its adverse
small-prime factors. The positive survivor is physical localization of
that energy beyond every polynomial cutoff, not merely the negation of
a proposed bound. Both strict damping regimes are formalized. This rules
out damping alone as a justification for replacing the growing core by
its full future ray. It does not retire Route RP or show native energy
escape: the native head processes additional primes as the physical
cutoff grows. Signed finite-cutoff payment and both history debts remain
open. The endpoint epsilon=1 is not decided here.

## Log

- 2026-10-02: RP-47 conjecture, paper proof, symbolic implementation, and
  dependency-closed leaf/axiom audits completed. Failed intermediate
  checks and corrections are recorded in the main RP working log.
