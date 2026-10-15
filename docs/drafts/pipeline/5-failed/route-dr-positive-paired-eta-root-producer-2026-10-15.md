# Positive convolution roots of paired eta cannot supply DR

Scope: retire this proposed root producer only. DR's actual Kummer gluing
problem remains active.

## Exact candidate

Let A be the union, over n >= 0, of the intervals
`(log(2n+1), log(2n+2)]`. For sigma > 0 put

    Z(sigma) = integral_A exp(-sigma*x) dx,
    d mu_sigma(x) = exp(-sigma*x) 1_A(x) dx / Z(sigma).

The candidate was that positive convolution roots of this probability law
could provide actual analytic dyadic roots of the paired source. Already the
square-root claim `mu_sigma = nu * nu`, with nu a probability measure on R,
is false for every sigma > 0.

## Paper proof of failure

Z(sigma) is finite because A is contained in the positive half-line, and
strictly positive because A contains `(0,log 2]`. For every real t < sigma,

    integral exp(t*x) d mu_sigma = Z(sigma-t)/Z(sigma) < infinity.

If mu_sigma were nu*nu, Tonelli gives the left side as the square of
`integral exp(t*x) d nu`. This integral is strictly positive (nu has mass one)
and hence finite. Thus nu has every exponential moment with parameter t<sigma.

Consequently

    G(s) = sqrt(Z(sigma)) integral exp((sigma-s)*x) d nu(x)

is holomorphic for Re(s)>0. To justify holomorphy near any point, choose two
real parameters on either side of sigma-Re(s), still below sigma. They
dominate the integrand and every fixed derivative on a smaller neighbourhood;
polynomial factors are absorbed by the exponential margins. No assumption on
zeros or on continuation of G is used here.

Absolute integrability and Fubini then give

    G(s)^2 = integral_A exp(-s*x) dx = eta(s)/s,   Re(s)>0.

The last equality is the actual paired-interval transform identity, not a
generic model: it is present in
`RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure.lean` as
`integral_exp_neg_mul_pairedEtaLogMeasure_eq_factor_riemannZeta_div`.

At rho = 1 + 2*pi*i/log 2, the factor `1-2^(1-s)` has a simple zero, while
zeta(rho) is nonzero by the unconditional zero-free line Re(s)=1. Since rho
is nonzero, eta(s)/s has a simple zero at rho. An analytic square cannot have
a simple zero: its derivative vanishes at every zero. Contradiction.

The underlying analytic obstruction is already formalized in
`PairedEtaRootContinuationBoundary.lean`:
`not_exists_analytic_etaPair_squareRoot_rightHalf`. Its `rightHalf` means
Re(s)>1/2. Moment inheritance is already formalized in
`ThetaTiltXiInfiniteDivisibilityNoGo.lean` as
`integrable_exp_mul_of_convPow_two_root`.

Verdict: FALSE as a positive root producer; REDISCOVERED as an analytic
obstruction. This is a consequence of existing corpus results, not a claim
of new scientific knowledge. The probability-measure specialization above
has a paper proof; no new Lean formalization of that specialization is claimed.

## Positive survivor and second pass

Failure of positivity does not rule out holomorphic roots on the open
half-strip. The offending auxiliary zero is on Re(s)=1, outside that strip.
Removing that divisor must preserve, rather than discard, genuine zeta charge.

The exact positive survivor is already paper-proved and Lean-formalized in
`PairedEtaKummerCoverTransport.lean`: explicit correction roots give a
base-preserving homeomorphism of the actual pole-unit and normalized paired
eta Kummer surfaces, including their hypothetical branch points. It commutes
with all dyadic squaring maps and deck rotations. It does not kill their
remaining monodromy.

A second proposed salvage was to use signed formal arithmetic roots. The
corpus already supplies the strongest algebraic version: every normalized
arithmetic function has a unique coherent Dirichlet-convolution root tower,
with its prime coefficient divided by 2^k. This is
`SquarefreeConvolutionDyadicTower.lean`. Its squarefree specialization is
proved not absolutely summable for Re(s)<=1 at every finite depth in
`SquarefreeConvolutionDyadicAbsoluteConvergenceWall.lean`. Formal arithmetic
roots are therefore not, by their existence alone, an analytic continuation
mechanism.

The prospective local signed inverse-Laplace formula from the working card
is not being promoted to a new producer or formal theorem. Its continuation
and the genuine source's sheet return remain unresolved. No extra wrapper
theorems were added to the Lean tree.

## Verification

A scratch Lean audit imported the exact named modules, checked all four
declarations above, and printed their axioms. It exited 0; every declaration
uses only `propext`, `Classical.choice`, and `Quot.sound`. The direct audit
`lake --old env lean GaloisForLFunctions/RHTower/PairedEtaRootContinuationBoundary.lean`
of the current source also exited 0 without diagnostics. No numerical
computation or external search was used.

## Remaining hard problem

Construct actual Euler-marked roots of the pole unit across
`1/2 < Re(s) < 1`, with trivial local sheet return at every dyadic depth.
The retired positive producer and the automatic coefficient tower do not
solve that problem. Do not retire DR, claim RH, or replace it with an
absolute-convergence estimate problem.
