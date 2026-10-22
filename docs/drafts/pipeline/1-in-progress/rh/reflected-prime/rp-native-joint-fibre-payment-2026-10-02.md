# RP-53: native joint-fibre payment

Stage: in progress. Route RP; unconditional RH remains the target.
Prior turn completed RP-52's signed boundary theorem and audits.
Hard target: a cutoff-uniform lower payment for native negative coprime
work at every fixed positive damping. Signed high-LCM control and both
history debts remain open.

The new balance B=h^2+C is L1 with zero mass, and C's positive part is
L1. Thus positive work cannot pay the missing square by itself. The
desired estimate must retain negative-work cancellation across the
actual physical cutoffs. No new conditional receiver will count.

## Trial 1: complete divisor-lattice projection

Source anchors: RoutePLcmPairPayment,
EulerDeletionTruncatedDivisorPairCorrelation,
EulerDeletionCenteredLcmCoprimeConservation,
EulerDeletionCoprimeHeadSubpower, RoutePNativeUndampedBalance.

Conjectured mechanism: use exact physical divisor-incidence annihilation
before integration to cancel the joint high-LCM sector, with a payable
projection remainder. The read corpus gives a complete divisor-lattice
sum as a coprime-window discrepancy square, and exact lcm-floor counts
at every physical window. The native coefficient set is an initial
interval, not a complete divisor lattice. All added labels and their
cross terms must be retained; no period averaging is allowed.

Need to establish an actual comparison for the native weighted unit-head
profile, rather than identify it with the different residue field. The
coprime residue head's existing subpower remainder still retains its
quadratic harmonic coefficient and later physical tail. It does not
supply the desired native square bound.

No new mathematical result claimed yet; no new Lean source written.

Trial 1 calculation: let N=floor(X), choose L divisible by1,...,N,
and extend the native weight f(d)=sqrt(d)*U(X/d) by zero on divisors
d>N. This extension is exact since U vanishes at arguments<=1.
Write M_N=sum_{d<=N}mu(d). For L>1, total divisor Mobius mass is zero;
the exterior mass is -M_N. Centering at f(1) therefore leaves the
exterior centered sum f(1)*M_N, rather than zero. Together with the
interior centered sum H(X)-f(1)*M_N it reconstructs H(X) exactly.
The complete-lattice identity supplies no upper bound unless this
interior/exterior cross term is estimated jointly. A zero raw weight
does not justify deleting its centered weight. This is an obstruction
to this proposed estimate, not a new no-go theorem or retired route.

## Trial 2: keep common scales and primitive pairs together

For finite X, retain the literal integrated square

  E_epsilon(X)=integral_1^X H(x)^2*x^(-3-epsilon) dx.

Set d=g*a,e=g*b,gcd(a,b)=1. Nonzero coefficients force g,a,b squarefree
and g coprime to a*b, so mu(d)*mu(e)=mu(g)^2*mu(a)*mu(b).
The substitution x=g*u gives the exact finite expression

  sum_{g*a<=X,g*b<=X,gcd(a,b)=1,gcd(g,a*b)=1}
    mu(g)^2*mu(a)*mu(b)*g^(-1-epsilon)*sqrt(a*b)
    * integral_max(a,b)^(X/g) U(u/a)*U(u/b)*u^(-3-epsilon) du.

Every upper endpoint X/g remains physical. The g-series is absolutely
summable for epsilon>0, but its coefficients are nonnegative. All
remaining signs are primitive-pair signs mu(a)*mu(b). Summing g cannot
create sign cancellation within a primitive fibre. The next trial
tests shifted primitive pairs b=a+k and retains their actual cutoff
and coprimality constraint; no infinite primitive-series interchange
has been justified.

Trial 2 follow-up: b=a+k makes gcd(a,b)=gcd(a,k). The read correlation
receivers require an assumed shifted-correlation or low-frequency
Dirichlet-polynomial budget; none gives that budget for the retained
kernel. Fixed-lag estimates would also need summation uniform in the
growing lag range. The binary additive recurrence concerns a+b, not
b-a, and gives positive recurrence, not an upper payment. No such
estimate has been supplied here.

The square-root-core alternative was checked in source before use.
MobiusDivisorCriticalMovingCoreObstruction already proves the exact
native completion by signed terminal prime copies and shows that the
square-root core itself has unbounded quadratic energy. Its extension
balance retains precisely the cancellation this task needs. Rewriting
that existing balance is not new knowledge and was not formalized again.

## Trial 3: time-weighted coprime cancellation

Let u=routePCoprimeUnitProfile, f=routePCoprimeNativeProfile, and D_a
denote the corpus's finite logarithmicWeightedDilation. All sums retain
n<=exp(t). The finite composition theorem and the read identity
Lambda*mu=-(mu*log), with the last product pointwise, give

  t*f(t) = D_mu(w)(t),  w(t)=t*u(t)-D_Lambda(u)(t).

This is the exact source correction required by multiplication by time;
replacing w by t*u would omit the prime forcing. The intended mechanism
was to use the first mixed coprime derivative to break zeroth-order
cancellation, then reuse RP-52's admission argument on the new source.

That admission is not justified: u is positive on an interior part of
the first unit block. Prime atoms with exp(t)/b<p<exp(t)/a for fixed
1<a<b<2 therefore contribute a positive multiple of exp(t) to
D_Lambda(u), by prime-window density, whereas t*u(t)=O(t). The squared
source now has an exponentially growing critical majorant. Subtracting
a proposed leading exponential changes its Mobius reconstruction by
exp(t)*sum_{n<=exp(t)}mu(n)/n; it is not a harmless constant or an
already admitted RP correction. This calculation diagnoses the failed
reuse of RP-52; it is not a new audited asymptotic theorem, a payment,
or a falsification of RH.

The finite-prime version avoids this dense forcing but leaves every
original zeta-zero cancellation intact. Passing to all primes needs
the uniform source estimate that the time-weighted calculation exposes.
No new Lean theorem or claimed frontier bound follows from these trials.

## Search and verification record

All five documented deep commands terminated with exit0. All result
sections, including candidate_lemmas, source_arguments, proof_ideas,
ingredient_sets, and coverage/freshness, were inspected. Candidate
statements were source-only; no generated proposal was accepted as a
proof. Semantic coverage is unmeasured and background refresh incomplete.

- Joint query79717: partial=false, no errors/unfinished stages;
  query1190904, coverage1190918/current1190919;64631 files,0 pending.
- Fibre query65209: partial=false, no errors/unfinished stages;
  query1190929, coverage1190947/current1190949;64633 files,0 pending.
- Shifted query8719: partial=false, no errors/unfinished stages;
  query1190937, coverage1190954/current1190963;64633 files,0 pending.
- Completion query22402: partial=true; malformed local JSON, Qdrant
  deadline, and decomposition runtime deadline; corresponding three
  stages unfinished. Query1190957, coverage1190997/current1190998;
  64636 files,0 pending. Available exact native terminal-source hits
  were used and read, without treating retrieval failure as absence.
- Time query14605: partial=false, no errors/unfinished stages;
  query1190972, coverage1190997/current1190998;64636 files,0 pending.

The positive generalized-prime-density inversion hit was read: it uses
mu(n)/n^2 and argument u/n, not the native unweighted logarithmic delay.
Its positivity theorem cannot be transferred to this source. The actual
prime-window log-mass asymptotic and first-block source positivity were
read for the time-forcing diagnostic.

No new Lean module, build, resource override, numerical experiment,
subagent, commit, or push. The authoritative frontier map is unchanged.
No route retired; no new positive survivor declared proved or formalized.

## Next hard trial

Retain both coefficient variables before time weighting: apply the exact
mu*log=-Lambda*mu identity to the finite integrated pair kernel in each
variable, reindex the prime forcing jointly, and keep the moving upper
endpoint. Test whether the resulting two-variable forcing difference has
a native signed upper payment. A separate norm estimate for either
forcing channel repeats the failure above. The desired output remains
sup_X E_epsilon(X)<infinity for each epsilon>0, with every actual
coefficient and boundary retained. The identity alone will not count.
