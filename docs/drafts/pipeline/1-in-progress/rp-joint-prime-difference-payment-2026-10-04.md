# RP-64: joint prime differences at the native moving cutoff

Route RP. Hard gaps: positive-damping negative work, signed high-LCM
control, and both native history debts. RP-63 formalized native
sharpness of independent prime projection; it paid no critical debt.
This attack retains all mixed prime differences simultaneously.

## Corpus basis and exact finite calculation

Sources inspected: UniformPrimeSubsetEnergy's exact signed pair
kernel; UniformPrimeSubsetBooleanInversion's parity-qualified sign
theorem; MobiusDivisorFixedCoreProfile's native channel limit;
RoutePUnsignedProfilePowerSaving's common quotient remainder;
MobiusDivisorContinuousHeadMoment's exact continuous homothety.
RP-63's two-channel Schur identity is now Lean certified.

Let P be a finite set of primes. Write d_S=product_(p in S)p,
a_S=A(M,d_S), theta_p=1-1/p, gamma_p=1-theta_p^2. Extend the literal
native channel by its existing value zero when d_S>=M; do not
complete it by a constant profile outside its support.

The covariance on the full finite Boolean cube is

    E_P(M)=sum_(S,T subset P) (-1)^(|S|+|T|)*a_S*a_T*theta(S symmdiff T).

Define the joint difference

    D_R a=sum_(T subset R)(-1)^|R\T|*theta(R\T)*a_T.

Tensoring the exact one-coordinate identity gives the finite paper identity

    E_P(M)=sum_(R subset P) gamma(P\R)*(D_R a)^2.

Proof: order the finitely many coordinates. In each coordinate the
signed covariance matrix [[1,-theta],[-theta,1]] factors as the sum
of gamma times the first-coordinate square and the square of
second-coordinate minus theta times first-coordinate. Apply this
identity successively to every coordinate and expand the finite
products. Each subset R selects the difference square in precisely
its coordinates; the other coordinates supply gamma. This is only
a finite algebraic identity, not an energy bound.

For a fixed P, the corpus profile limit gives

    D_R a/sqrt(M) -> c_0*product_(p in R)(1-theta_p),
    E_P(M)/M -> c_0^2*product_(p in P)(2/p).

The limiting ratio of the empty-coordinate Schur floor
gamma(P)*a_empty^2 to E_P is product_(p in P)(1-1/(2*p)). Thus
RP-63's one-prime sharpness does not eliminate collective savings
from a growing initial prime set. A fixed-P statement cannot
justify that growing-set limit.

## Attempt at the hard moving-cutoff bound

Candidate: for every epsilon>0, the full native covariance with
P={primes p<M} obeys E_P(M)<=C_epsilon*M^(2+epsilon), uniformly
in M. This is an open candidate, not a consequence of the formulas.
Its applicability to the exact RP criterion must retain the
full-selection weight product theta_p and the physical cutoff.

Tested mechanism: apply the uniform unsigned profile remainder to
all mixed differences before summing their squares. Put Q=product P,
alpha=1/40. After enlarging C and T_0 to absorb the integer quotient,
when M>=T_0*Q the source theorem yields

    |D_R a/sqrt(M)-c_0*product_(p in R)(1-theta_p)|
      <= C*M^(-alpha)*product_(p in R)(theta_p+p^alpha).

Squaring and summing with the exact gamma weights gives

    E_P(M)/M <= 2*c_0^2*product_(p in P)(2/p)
      +2*C^2*M^(-2*alpha)*
         product_(p in P)(1+2*theta_p*p^alpha+p^(2*alpha)).

This proof is valid only in the common quotient regime M>=T_0*Q.
For the native moving core, many products d_S lie at or beyond M,
and the hypothesis fails. Substituting the limiting constant there
would replace actual zero channels by nonzero values. Even the
already-proved escape of fixed initial cores at positive damping
forbids replacing the physical family by full-ray fixed-core bounds.

No critical payment follows. The next proof obligation is the joint
mixed-difference contribution of the quotient boundary, with those
zero channels retained exactly. This is the same hard native
arithmetic problem, now exposed in the complete Schur expansion;
independent cofactor Cauchy and fixed-core limits do not discharge it.
The moving-core conjecture remains active, not retired.

## Search audit

Deep covariance search: generation 1220609, coverage 1220617/current
1220618, 65058 files; no partial/errors/unfinished stages. Hits were
mostly unrelated prime-counting/covariance results and supplied no
native joint bound. A lexical retained/covariance search returned
source pointers but no freshness report or new applicable estimate.

Rephrased deep search restricted to MobiusDivisor: generation 1220639,
coverage 1220656/current 1220657, 65061 files; no partial/errors/
unfinished stages. Candidate/source/ingredient sections inspected.
Useful hits retain literal source channels, physical annulus identities,
fixed-core energy limits, and mixed-interaction statements. The
suggested ingredient chain was unverified and did not prove the
moving-core estimate. Both deep searches reported unmeasured semantic
coverage and incomplete refresh; compiler states mostly pending,
stale, or unavailable. No search result is treated as a certificate.

Status: finite calculations above are paper only. No new Lean wrapper
for an unpaid bound, no added assumption, no numerical experiment.
All hard RP debts and unconditional RH remain open.
