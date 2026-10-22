# DR: an entire counterterm for finite Euler root towers

Status: in progress; the half-strip continuation theorem is OPEN.

Previous cycle found that the literal finite product times (s-1) introduces
a branch point at 1 even though the pole-filled infinite source is a unit
there. This cycle tests an explicit counterterm that avoids that mismatch.
The goal is still the actual root tower on Re(s)>1/2.

## Exact source construction

For real X>=2 put L=log X, P_X={primes p<=X}, and

    J_L(s) = integral_(0,L) (1-exp(-(s-1)t))/t dt,

where the integrand at t=0 has its removable value s-1. Equivalently
J_L(s)=Ein((s-1)L), with Ein(z)=sum_(n>=1) (-1)^(n-1) z^n/(n*n!).
The latter series is entire and equals the integral by uniform convergence
of the exponential series on compact t intervals. In particular J_L(1)=0.

On Re(s)>0 define the marked logarithm

    Lambda_X(s) = log(zeta(2)) + J_L(s)-J_L(2)
      - sum_(p in P_X) [Log(1-p^(-s))-Log(1-p^(-2))].

The Euler logarithms are the principal ones: |p^(-s)|<1, so 1-p^(-s)
lies in the open right half-plane. The constant log(zeta(2)) is real.
Define

    U_X(s) = exp(Lambda_X(s)),
    R_(X,k)(s) = exp(Lambda_X(s)/2^k).

Every U_X is an analytic unit on Re(s)>0, including at 1. The roots are
actual analytic functions on this whole domain, satisfy
R_(X,k)^(2^k)=U_X and R_(X,k+1)^2=R_(X,k), and have the same positive
anchor zeta(2)^(1/2^k) at s=2. No root-existence or zero-free assumption
about zeta in the critical strip enters these definitions.

This is a concrete candidate approximating family, not yet the required
comparison between its root covers and the actual continued source.

## Unconditional forward checks on paper

For Re(w)>0,

    Ein(wL) = gamma + Log(wL) + E1(wL),
    E1(wL) = integral_(L,infinity) exp(-w*t)/t dt.

The identity follows by differentiating in w on the right half-plane and
fixing its real constant using the real Ein asymptotic. Uniform decay of
the last integral on Re(w)>=delta>0 gives

    J_L(s)-J_L(2) -> Log(s-1)

locally uniformly on Re(s)>1. The actual finite Euler logarithm converges
locally uniformly there as well. Consequently Lambda_X converges there to
Log(s-1)+the canonical Euler logarithm of zeta, and U_X converges to
E(s)=(s-1)zeta(s). Each fixed root degree has the matching Euler-germ limit.
E is understood with its removable value E(1)=1 filled in.

At s=1 the exact finite value is

    U_X(1) = zeta(2) * exp(-Ein(log X))
      * product_(p<=X) (1-1/p)^(-1)
      / product_(p<=X) (1-1/p^2)^(-1).

The real Ein asymptotic, Mertens product asymptotic, and the ordinary Euler
product at 2 give U_X(1)->1. Lambda_X(1) is real, so every fixed root also
tends to 1 at this point. This removes the literal finite-stage branch at
the pole, without claiming convergence in a neighborhood crossing Re(s)=1.

## Hard conjecture and attack

Conjecture for this exact family: U_X converges locally uniformly to E on
Re(s)>1/2, with the corresponding marked root towers converging there.

This conjecture would prove the requested result by conservation of local
order / Hurwitz nonvanishing. Its definitions are source-explicit, but the
convergence assertion is not a known or authorized premise.

The exact logarithmic derivative shows what remains:

    Lambda_X'(s) = (1-X^(1-s))/(s-1)
      - sum_(p<=X) log(p)/(p^s-1),

with the first quotient filled by log X at s=1. The counterterm handles
the continuous pole contribution. It does not cancel an unknown local
divisor charge of the completed source. Its k>=2 prime-power terms already
converge normally on Re(s)>1/2; the first-prime term retains the previously
identified continuation obstruction.

Neither agreement at 1, exact normalization at 2, agreement on Re(s)>1,
nor finite-stage unit roots proves local uniform convergence across the
strip. The corpus already proves that compact-open approximation by
holomorphic squares is equivalent to the first missing rung. The present
explicit family must earn that convergence through additional arithmetic
structure. Do not invoke normality, Vitali, or a cover limit without proving
their hypotheses for this family.

Verdict so far: BRIDGE. The finite pole mismatch has an explicit remedy;
the actual source attachment has not been proved. This is not a new
scientific theorem or a zero-free certificate.

## Direct contour attack

Trying to retain only sheet return does not remove the source attachment
problem. Let C be a positively oriented circle contained in Re(s)>1/2,
with E nonzero on C, and containing just a hypothetical zero rho of E of
order m>0. For every finite X, Lambda_X is a single-valued holomorphic
function on the disk bounded by C, so

    integral_C Lambda_X'(s) ds = 0.

The argument principle gives the exact defect

    integral_C [E'(s)/E(s) - Lambda_X'(s)] ds = 2*pi*i*m.

Consequently the arclength integral of the absolute value of this defect
is at least 2*pi*m for every X. Even convergence of these currents against
the constant contour test would exclude the hypothetical zero; it cannot
be inferred from their agreement on the Euler half-plane. This is a
conditional obstruction, not a proof that this family actually fails to
converge on the desired half-plane.

At degree d the actual Kummer lift returns with multiplier exp(2*pi*i*m/d),
whereas the finite exponential root returns with multiplier 1. The
counterterm and the normally convergent higher-prime-power correction each
have zero period on C. Neither can supply the missing comparison for the
primitive prime current. Taking a limit of the finite return multiplier
without constructing that comparison would be circular.

This is already explained by current corpus divisor and contour results;
it is not a new theorem. It identifies precisely what a direct contour
proof for this explicit source would still have to establish.

## Current corpus evidence

Read current Lean source:

- `RHTower/EulerTruncationRigidity.lean`: actual finite Euler units and all
  marked power roots on Re(s)>0, with the additive/multiplicative mismatch.
- `RHTower/PrimeVacuumExponentialIntegral.lean`: continuous prime vacuum
  identified with the exponential integral on its defining half-plane.
- `RHTower/EulerMascheroniExponentialIntegral.lean`: real Ein asymptotic.
- `RHTower/MertensThirdTheorem.lean`: the actual Mertens product asymptotic,
  `tendsto_mertensPrimeProduct_mul_log`, with constant exp(-gamma).
- `RHTower/MertensProductLaplace.lean`: already defines `einCompare`,
  identifies it with `ein`, and attaches a logarithmic continuation to the
  pole-filled source. The Ein--Mertens subtraction mechanism is therefore
  REDISCOVERED. Do not describe this normalization as new scientific
  knowledge or pivot to optimizing Mertens estimates.
- `RHTower/PrimeBoundaryMonodromyEscape.lean`: quantized residue of the
  continued primitive prime current, finite entire-cumulant period zero,
  and the obstruction to passing nonvanishing through a claimed limit.
- `HTGeometry/ProKummerHolonomyCapacity.lean`: the exact return multiplier
  and its divisibility criterion. Vanishing chords as root degree grows
  do not imply zero integer charge.
- Earlier current-source audit of
  `RHTower/XiPoleClearedFirstTraceSquareApproximation.lean`: the missing
  compact-open convergence is not provided by a normal-family reformulation.

No numerical experiment or external search is used. The complex entire
counterterm and the full stated forward limits above are paper work until
explicitly formalized; they are not claimed as verified new Lean theorems.

All three corpus searches completed with `partial=false` and no reported
errors. Compiler coverage contains many pending/stale sources and semantic
coverage was unavailable. The relevant source files above were inspected;
search output is not claimed to be a fresh Lean build. No repository Lean
source was changed in this cycle, and no new formalization is warranted
for these already-known mechanisms alone.

## Next work

OPEN CORE: prove source-specific preservation of sheet return for this
family on the half-strip, or find a different actual root-producing
operation. Further normalization identities alone do not meet the target.
Do not change DR's goal to proving the forward checks or improving
cutoff bounds.
