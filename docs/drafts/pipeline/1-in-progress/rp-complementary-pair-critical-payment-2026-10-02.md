# Complementary signed-pair critical payment

- **ID:** RP-33 continuation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** RP, after the audited RP-32 hyperbolic deletion.

## Hard target

With A_M(d)=mobiusDivisorDilationChannel M d, prove unconditionally

    exists B>=0, forall M,
      sum_{1<=d,e<=M, M<lcm(d,e)} A_M(d)*A_M(e) <= B*M^2,

or prove that no such B exists. RP-32 pays the entire d*e<=M sector by
o(M^2); RP-33 now pays the larger lcm(d,e)<=M sector by an unconditional
O(M^2) absolute bound. The literal full signed square and the remaining
complementary sum therefore differ by O(M^2). The native history floor
and both square debts remain open.

This is a signed aggregate estimate. The diagonal already has a quadratic
bound; individual pair signs and positive common-divisor completions are
not a substitute.

## Corpus evidence and next attack

The exact gcd reconstruction and MobiusReciprocalPrimitiveRatio put the signs
on coprime primitive indices a,b, with d=g*a,e=g*b. The common-scale factor is
mu(g)^2, subject to coprimality of g with a*b. In the complementary sector
the remaining lower scale cutoff is g*a*b>M, while g*max(a,b)<=M.

The next proof attempt is signed partial summation in those primitive ratio
indices, retaining that lower cutoff and the full clipped source profile.
Seek an exact arithmetic cancellation of the leading ratio mass and a
critical bound for the complete residual. A finite gcd rewrite alone does
not advance this target and must not become the deliverable. Bounds for
individual positive scale columns do not control their signed assembly.

The existing largest-prime source identity is an alternative representation
of the same joint problem: the moving head and its late-prime correction
have supercritical components and must be kept together. Its known
asymptotic does not supply the required critical remainder.

## Failed extension and lesson from RP-32

The RP-32 domination used e<=floor(M/d) on d*e<=M. That inequality reverses
on the complement. The profile power saving therefore gives no summable
e^(-41/40) majorant there. Extending the same absolute estimate does not
prove the desired bound. A new signed cancellation argument is necessary;
no exponent optimization repairs this logical gap.

## Constraints

Retain all gcd classes, both diagonal portions, current-cutoff clipping,
and original Mobius signs. Do not assume RH, a Mertens square-root bound,
a positive Gram budget, a fixed terminal cap, or unrestricted delayed repair.
Do not promote search suggestions or a conditional RH receiver to a producer.
No numerical experiment is part of this attempt.


## RP-33 proved: complete lcm-sector payment

The full signed
sector lcm(d,e)<=M admits an unconditional O(M^2) absolute bound. This
contains the paid product sector and genuinely adds complementary pairs.
It leaves lcm(d,e)>M unpaid.

Write v_d=V_M(d)/sqrt(M). In each complete lcm fibre n,
sum_{lcm(d,e)=n}mu(d)mu(e)*f(d)=mu(n)*f(1). This follows by partitioning
e=(n/d)*h, h|d when n is squarefree: sum_{h|d}mu(h)=0 unless d=1;
non-squarefree fibres have zero Mobius pair weights. Consequently the
whole lcm sector equals

    V_M(1)^2*Mertens(M)
      + sum_{lcm(d,e)<=M} mu(d)mu(e)*
          (V_M(d)-V_M(1))*(V_M(e)-V_M(1)).

The single-coordinate terms cancel exactly. Write d=g*a,e=g*b with
coprime a,b. Then lcm(d,e)=g*a*b<=M. The uniform profile remainder,
extended to every positive quotient by the global channel ceiling, gives
|v_d-v_1|<=2C/b^eta and |v_e-v_1|<=2C/a^eta, eta=1/40.
There are at most M/(a*b) possible common scales. Dropping coprimality
and Mobius masks only after taking this mixed error's absolute value gives

    |mixed remainder| <=4*C^2*M^2*sum_{a,b>=1}(a*b)^(-1-eta).

The double series is finite. The main term is <=(9/25)M^2 using the
existing unsigned ceiling and |Mertens(M)|<=M. This entire argument is now
formalized in RoutePLcmPairPayment.lean. The final foreground leaf audit
and separate axiom audit passed; both public endpoints use only
propext, Classical.choice, Quot.sound. The exact partition preserves all
excluded pairs. See the completed card
../3-formalized/rp-complete-lcm-sector-payment-2026-10-02.md.
No claim of payment for lcm(d,e)>M or RH follows.

## Next hard conjecture: joint incomplete-packet cancellation

For squarefree n and d|n, write e=(n/d)*h with h|d. The lcm condition is
automatic and mu(d)*mu(e)=mu(n)*mu(h). On n>M the active condition e<=M
becomes h<=floor(M*d/n), a strict partial divisor range. Complete-packet
annihilation is therefore replaced by the actual truncated Mobius divisor
sum coupled to the native profile at (n/d)*h. The candidate mechanism is
signed summation of this joint moving-cutoff expression over n and d.
It must produce the quadratic bound above, not merely a finite identity.

Corpus searches expose truncated-divisor window identities and omitted
Selberg boundary forms. The former's exact vanishing requires k<=N,
which fails in incomplete packets; the latter use different harmonic and
logarithmic weights. Neither is a producer for the native complementary
sum. The next attempt must retain those mismatches as real obligations.

## RP-34 attempted estimates and retained obstruction

No new critical bound was obtained in this attempt. The incomplete-packet
reflection h=d/k returns the exact primitive-ratio carrier: d=g*a,
e=g*b, g*a*b>M, g*max(a,b)<=M. Its original common-scale weight is
mu(g)^2 times a nonnegative native profile product. Thus reflection alone
does not cancel the primitive signs mu(a)*mu(b).

Grouping by the product instead also fails to create internal cancellation.
The corpus theorem MobiusProductFibre.pair_sign says every nonzero Mobius
pair with product q has the same Liouville sign. Multiplication by the
nonnegative native unsigned channels and restriction to lcm>M preserve
that fact. Summation by parts across product values still requires a
bound for the full signed accumulation; an absolute fibre variation bound
does not supply it. The corpus's Gamma-Hankel variation theorem concerns
a different kernel and cannot be imported as a native RP estimate.

The source-autocorrelation bounds also retain a genuine weight gap:
criticalAbelLogProfile(t)=exp(-3*t/2)*criticalContinuousAbel(exp(t)).
Its unweighted integrability and signed moments do not bound the source
at the required exp(t) scale. No exponential-weight estimate was inferred.

## Next candidate: logarithmic prime-power renewal of the same native sum

Keep V_M(d) as the actual clipped unsigned channel and define on paper

    H_M = sum_{d<=M} mu(d)*V_M(d),
    L_M = sum_{d<=M} mu(d)*log(M/d)*V_M(d),
    R_M(r) = sum_{e<=M/r} mu(e)*V_M(r*e).

The corpus identity vonMangoldt_mul_moebius, Lambda*mu=-mu*log,
gives for M>=1 the exact finite relation

    log(M)*H_M + sum_{r<=M} Lambda(r)*R_M(r) = L_M.

This is a paper starting identity, not a new Lean deliverable or an
estimate. The next attempt is a joint signed work estimate for this
renewal, retaining the prime-power cross terms and the full L_M source.
Neither term may be assumed small or nonnegative. A successful estimate
must imply the original quadratic head/complement bound; reformulating
that bound as a premise does not count as a producer.

Prior-art check found the pointwise and unweighted recursion already proved
in Sieve/MoebiusLogRecursion.lean, and the complete unit-Riesz dressing
collapse in CCMCriticalMellinRieszMobiusRenewal.lean. Their exact identities
do not provide the needed work bound. The latter explicitly retains the
unresolved comparison with the polar continuum.

A direct absolute-value induction also fails to close: under the target
linear scale for the shorter continuous heads, the prime-power sum is
bounded through M*sum_{r<=M}Lambda(r)/sqrt(r), which is of the larger
M^(3/2) scale before division by log(M). The native clipping correction
must also be retained. This does not falsify the joint renewal conjecture;
it rules out that particular unsigned induction argument. Continue with
the combined signed prime-power work and L_M, not separate budgets.

## RP-35: stationary work and shared-prime descent

No new critical estimate or Lean theorem was obtained. The exact stationary
action in `CCMPrimeDeficitCoefficientAction` reproduces the logarithmic
Chebyshev deficit. Its Hessian remains a signed divisor-source quadratic
form. `LogarithmicReconstructionTailSymmetry` kills interactions between
two coefficients beyond the square-root cutoff, not arbitrary mixed
short/long interactions. Stationarity is therefore not an energy bound.
The existing short quadratic reconstruction has an already-paid
square-root-scale correction; its signed main work remains RH-equivalent.

The alternative coarse Selberg recursion also cannot be used as a producer.
`PMSelbergSublinearPowerBoundary` supplies comparison remainders with
literal von Mangoldt weights, sublinear normalized response, and divergent
canonical variance. These are not the actual prime remainder; their role
is to exclude an inference from the recursion estimate alone. The exact
native forcing must be retained.

A more faithful pair-level attempt uses the corpus's three-channel lcm
split. Extend f(d)=V_M(d) by zero for d>M. For squarefree n=p*m with p
prime and p not dividing m, the complete signed fibre has the paper identity

    F_M(p*m) = sum_{lcm(a,b)=m} mu(a)*mu(b) *
      (f(p*a)*f(p*b) - f(p*a)*f(b) - f(a)*f(p*b)).

All indices here are positive divisors of m. This is obtained by the
left-only, right-only, and shared-prime cases, with the original clipping
carried by f. Weighting by log(p) and summing over p|n reconstructs
log(n)*F_M(n). This is a starting identity, not a new payment theorem.

The attempted descent has an exact obstruction even at aligned cutoffs:
when M=p*N, the shared slot is p times the child native fibre, and n>M
becomes m>N. It is still the unpaid child complement. The proved lcm<=N
estimate cannot pay it. The two directed mixed slots must repay the
inherited square jointly. The corpus's bilinear dilation and all-order
Boolean identities already retain precisely this covariance obligation;
no sign or uniform bound was imported from those identities.

### Next estimate to attack

Keep the three slots combined and center on each complete parent fibre.
Put delta_p(a)=f(p*a)-f(p), delta_1(a)=f(a)-f(1). The single-coordinate
annihilation used in RP-33 gives the paper expression

    mu(m)*(f(p)^2-2*f(p)*f(1))
      + sum_{lcm(a,b)=m} mu(a)*mu(b) *
          (delta_p(a)*delta_p(b)-2*delta_p(a)*delta_1(b)).

Seek a critical bound for its *combined* log(p)/log(p*m)-weighted sum on
M<p*m<=M^2, with p*m squarefree, using the exact prime/cofactor cutoff
geometry. The centered terms
are not individually declared paid: f(p*a)=0 when p*a>M, and those boundary
terms must cancel the constant-profile contribution rather than be dropped.
The two different cutoffs are essential. An identity-only formalization,
another coarse recursion inequality, or an assumed cross-covariance bound
would not advance this target. Full complementary payment and both native
square debts remain open.

## RP-36: mixed centering and the nonoscillating terminal cell

No critical aggregate bound was obtained. The first-prime contraction in
`MobiusDivisorPrimePairEnergy` concerns the sum of individual pair squares.
It preserves the full signed head, but does not pay cross-cofactor terms in
the square of that head. The exact new-prime incidence identities likewise
retain the left-only, right-only, and shared channels without estimating
their combined contribution.

Centering does not permit a termwise critical payment. With f extended by
zero, delta_p(a)=-f(p) whenever p*a>M. This is not a small tail error.
Even if the original three-slot expression vanishes because both shifted
indices are inactive, its separate centered constant and remainder terms
need cancellation. No absolute bound for those separate terms was promoted.

An attempted reciprocal-phase estimate encounters a concrete native source
term. The existing exact quotient-cell theorem, together with the source
definitions, gives on M/2<d<=M

    A_M(d) = mu(d)*(2*gamma-1)*(sqrt(M)-sqrt(d)).

Here primeFreeDivisorDefect(1)=2*gamma-1 and V_1(1)=0. The modular ramp of
period one is zero, while the displayed smooth term remains. Thus the
unsigned reciprocal-phase estimate does not account for this part of the
signed head. The existing cell bound contains sqrt(M)*mertensSup(M), not a
uniform critical M allowance. A generated search suggestion omitted that
Mertens factor; the actual source statement was checked and the suggestion
was rejected. No separate critical cell bound is assumed.

### Next joint source attempt

Return to the literal `routePUnpaidMobiusAbel`, keeping its smooth source
and moving ramps together. In the moving ramp term set m=d*j. Its exact
index region becomes sqrt(k)<m<=k, j|m, 1<=j<=floor(k/m). The already-proved
quotient-ramp identity gives the paper expression

    sum_{sqrt(k)<m<=k} [
      centeredModularRamp(m,k) * sum_{j|m, j<=k/m} mu(m/j)
      - sum_{j|m, j<=k/m} mu(m/j)*centeredModularRamp(m/j,k)/j ].

For m>1, the full divisor coefficient sums to zero. Test whether replacing
the truncated coefficient by its omitted divisor complement lets the
resulting terms cancel the actual smooth remainder before the half-order
time sum is estimated. Keep both displayed terms, all square-birth cutoffs,
and the quotient-one smooth contribution. This is an unproved estimate
mechanism, not a new identity-only formalization or a paid remainder.

## RP-37: joint completion and activation-window tests

No new critical bound or verified frontier theorem was obtained. Completing
the omitted-divisor reflection while retaining the smooth remainder returns
the original source, rather than a smaller remainder. With q=floor(k/d),
s=floor(sqrt(q)), and H_j the harmonic sum, the combined bracket becomes

    log(q!) + s^2 + (2*gamma+1)*q
      - ((2*k+1)/d)*H_q + 2*sum_{s<j<=q} floor(q/j).

The hyperbola identity changes s^2 plus the last sum into the full divisor
summatory function. Mobius convolution then gives exactly
psi(k)-k+2*gamma. This paper calculation supplies no estimate and was not
turned into a new Lean leaf.

Keeping the time windows exposes birth k=d*j^2 and completion k=d^2*j^2.
Both boundaries align with period d*j. First Abel domination at birth costs
a quantity of square-root size in d, rather than the constant budget available
at the complete square boundary. Second Abel summation retains a birth mean
and a terminal primitive; neither removes the Mobius sign assembly.

The read theorem `sum_divisorPairs_antitone_weight_nonpos` cannot presently
pay this assembly. It uses mu(m)*mu(n) and a nonnegative antitone weight in
m+n. Setting m=d*j only identifies the native coefficient with that divisor
pair sign on squarefree m. Nonsquarefree m still contribute, and the actual
activation weight depends on the product/ratio cutoffs. No matching positive
mixture of the theorem's weights was established.

The prime-energy attempt also remained open. The generic retrieved
`energy_estimate` assumes nonnegative jump work. The actual adaptive terminal
source identity leaves a transformed head square and the prime-weighted
child square sum. The source's zero inverse-five-halves mass is already
proved, but its logarithmic moment is exactly -divisorHarmonicBoundary/3.
The existing `criticalPrimeAbelHead_negative_linear_escape` rules out a
separate linear bound for the isolated prime head. None of these existing
facts was reported as new progress or as a falsification of RH.

### Next full-source energy conjecture

Test the literal logarithm-of-gcd form for M>=1, preserving the full native
channel a_d=A_M(d); all summed natural indices below are positive:

    G(M) = sum_{d,e<=M} a_d*a_e*log(gcd(d,e))
         = sum_{r<=M} Lambda(r)*(sum_{d<=M,r|d} a_d)^2.

The second equality follows on paper from the read corpus indicator identity
`log_gcd_eq_sum_vonMangoldt_indicator`; it is not a new audited theorem.
For this squarefree-supported source only prime r contribute. The research
target is an unconditional uniform bound G(M)<=C*M^2*(1+log M), not another
diagonalisation or conditional receiver. The already-refuted inclusive gcd
completion uses totient weights; its late-prime obstruction must not be
silently imported or silently ignored for this different logarithmic weight.

Retain both lcm regions when testing the estimate. Write
H=sum a_d, D=sum a_d*log(M/d), and
Q_low/high=sum a_d*a_e*|log(M/lcm(d,e))| on the two respective regions.
The exact paper balance is

    log(M)*H^2 = 2*H*D + G(M) - Q_low + Q_high.

G(M)>=0 alone is in the wrong direction for an upper bound. Moreover the
paid lcm<=M result does not automatically pay either logarithmically weighted
region. The next argument must estimate the native prime-multiple sums and
their complete cross terms. No bound, new RH equivalence, or frontier advance
is claimed for this candidate.

## RP-38: prime-power recursion retains the full hard source

No unconditional bound for G was obtained. Define, on paper,
C_p(M)=sum_{1<=d<=M,p|d} A_M(d) and H(M)=sum_{1<=d<=M} A_M(d).
The read integer homothety and prime Mobius mask give, for prime p,

    C_p(p*M) = -sqrt(p)*(H(M)-C_p(M)),
    C_p(p*M)^2 = p*H(M)^2 + p*C_p(M)^2
                  - 2*p*H(M)*C_p(M).

In particular H(M)=C_2(M)-C_2(2*M)/sqrt(2). Thus controlling the prime-two
component across the two scales already controls the original source. The
positive log-gcd form is not an easier arithmetic input that may be assumed.
These are paper consequences of existing homothety, not newly audited leaves.
For nonmultiple cutoffs, `mobiusDivisorSelectionFibre_prime_interpolation`
retains both adjacent quotient cutoffs and the square-root clip weight; those
terms cannot be replaced by the lower integer quotient alone.

The squared recurrence was tested as an induction mechanism. Separate
absolute bounds on its two source squares and mixed product do not produce
a closed critical bound. The mixed product has no supplied sign. Existing
unweighted autocorrelation integrability and its negative second moment do
not estimate this finite-cutoff critical pairing. The read
`criticalAbelCorrelationPrefix_boundary_balance` retains an endpoint and
only transfers a negative boundary correlation to some negative finite
prefix; it does not control all cutoffs or all prime-logarithmic lags.

### Continuing target: complete logarithmic off-diagonal

The diagonal of G is sum_d log(d)*A_M(d)^2, so the existing native quadratic
diagonal bound pays it with one logarithm. The unresolved estimate is the
complete signed off-diagonal with weight log(gcd(d,e)). A stronger trial is
aggregate nonpositivity of that off-diagonal (or a critical upper allowance
if exact nonpositivity fails). This is a conjecture, not a sign premise.

Do not impose signs on separate gcd classes. The read
`MobiusDivisorGcdCrossObstruction` has positive primitive/common-divisor
components while its complete eleven-channel cross sum is negative; its
statement explicitly leaves aggregate diagonal dominance unresolved.
The next proof attempt must estimate the complete weighted assembly from
the actual profile, preserving incomparable cofactor pairs. An identity-only
log-gcd diagonalisation, a generic positive Gram bound, or a conditional RH
receiver would not move this target.

## RP-39: squared-source inversion does not pay the native log-gcd form

No verified frontier advance. Aggregate nonpositivity of the native weighted
off-diagonal remains a conjecture; neither a proof nor a counterexample was
obtained. The positive individual gcd components in the corpus do not decide
this complete weighted sum.

The read theorem `logarithmicCoprimeEnergy_mobiusInverse` gives, for a source
v and its complete logarithmic Mobius inverse u, the exact finite balance

    u(T)^2 + CoprimeCross(u,T) = MobiusInverse(v^2)(T).

A uniform bound for v bounds the right side at the critical O(exp(T))
scale. It does not bound u(T)^2 without a lower bound on the signed cross
term. The actual-prime analogue is already present in
`CCMPrimeDeficitCoprimeBalance`; no new theorem is claimed for this identity.
The complete coprime row bound in `CCMPrimeDeficitCoprimeRows` likewise
retains its divisor mass. Summing its absolute envelope does not establish
the required critical cancellation.

A second paper test separates two quadratic forms that must not be confused.
For the delayed reconstructed vector u(T-log d), the log-gcd diagonalisation
has multiple coordinates v(T-log r). For the normalized native coefficient vector
mu(d)*v(T-log d), the prime multiple coordinates instead involve the sums
of u(T-j*log p) over positive powers p^j. Thus a bound for the former form
does not pay the latter. Even adding the full dilation row to the former
prime rows does not give generic endpoint coercivity: on the divisors of
two distinct primes' product, the alternating Mobius vector has endpoint
one and zero total and prime-multiple rows. This is only a paper applicability
check for a proposed generic estimate, not a counterexample for the native
source and not a newly audited no-go theorem.

The exact interpolation-square defect was also retained. It is nonnegative
before subtraction, but the full prime-merger update still contains the
mixed pairing of the original and interpolated fields. The adjacent-cutoff
square budget in `MobiusDivisorPrimeFibreInterpolation` does not bound that
pairing with the needed sign. No all-merger contraction or critical source
bound was inferred from it.

Continue the native aggregate estimate, preserving the complete signed
prime-power mixed work and every terminal term. Repeating the already tested
absolute renewal induction, or merely transporting the above identities,
would not move this frontier. Full lcm>M payment, both history-square debts,
and unconditional RH remain open. No production Lean changes or builds in
this trial.

## RP-40: integrated prime-power work still requires critical source energy

No verified frontier advance or new Lean theorem. The coupled prime-power
trial was worked out at finite logarithmic cutoffs, keeping the terminal
limits of every translated factor. It gives a relative comparison, not a
critical source budget.

Paper notation: h(t)=exp(-t)*H(exp(t)), zero for t<=0, and

    b_p(t) = sum_{j>=1, j*log(p)<=t} p^(-j/2)*h(t-j*log(p)),
    E(T) = integral_0^T h(t)^2 dt,
    A(T) = integral_0^T (T-t)*h(t)^2 dt,
    F(T) = integral_0^T sum_p log(p)*b_p(t)^2 dt.

These b_p are the normalized native prime rows on paper; the sign of a row
disappears in its square. Expanding at finite T, the j=k=1 part is exactly

    integral_0^T h(s)^2 * sum_{p<=exp(T-s)} log(p)/p ds.

The read `abs_mertensA_sub_log_le` compares this with A(T), with error bounded
by a constant times E(T), including the real-floor endpoint. Cauchy on each
translated product bounds all remaining terms by E(T) times

    sum_p log(p)*((sqrt(p)-1)^(-2)-1/p).

This coefficient sum is finite: its summand is bounded by a constant times
log(p)/p^(3/2). Thus the paper argument gives |F(T)-A(T)|<=B*E(T).
It does NOT give a bound for E(T), A(T), or F(T). No infinite critical-clock
integrability was used in this finite calculation. The generic relative
estimate was not turned into a Lean leaf or reported as a native payment.

The actual `mobiusDivisorCriticalClockTriangularPairing_density_cancellation`
was checked as a possible way to close that remaining estimate. Its
nonpositive balance includes the signed mixed correlation as well as the
density-weighted energy change; it does not bound the energy change alone
through exhaustive prime insertion. The finite clock factors and boundary
surplus cannot be dropped.

The next source-specific trial is the positive critical moment

    K(epsilon) = integral_0^infinity
      exp((1-epsilon)*t)*criticalAbelLogProfile(t)^2 dt,

for every epsilon>0, with actual integrability to be proved. This is the
same full source: criticalAbelLogProfile(t)=exp(-t/2)*h(t). The read corpus
proves unweighted integrability and boundedness, hence admits epsilon>=1;
the interval 0<epsilon<1 is the unpaid analytic obligation. No such moment
is assumed and no conditional RH receiver is being proposed as progress.

`criticalAbelCorrelationContinuation` is locally analytic at real points
greater than -1, but its source file explicitly does not assert exponential
admission of the physical signed correlation there. That continuation is
neither a continuation of K nor a proof of its integrability. The entire
divisor numerator likewise does not remove division by zeta in the native
source transform. The next argument must control this positive square
moment from the actual arithmetic source, not transfer an admitted moment
from a different profile or infer convergence from analytic continuation.

## RP-41: direct positive moment and its full arithmetic pair kernel

No verified frontier advance. Read the actual source coefficient and real
integral theorem: c(n)=Lambda(n)-1+2*gamma*delta(n,1), whose cumulative sum
is psiDefect. The complete Abel source therefore has the paper expansion

    H(x)=sum_{1<=n<=x} c(n)*(sqrt(x)-sqrt(n)).

The critical moment is integral_1^infinity H(x)^2*x^(-3-epsilon) dx.
Existing Chebyshev/dyadic square admission uses x^(-3) for the discrepancy
before half-order Abel integration. The corresponding Hardy estimate does
not admit the stronger x^(-2-epsilon) input for 0<epsilon<1. The coefficient
bound sum Lambda(n)^2/n=O(log(N)^2) controls a diagonal, not the cumulative
discrepancy square. Neither estimate was upgraded without proof.

For positive epsilon and positive integer m,n, put z=max(m,n). Integrating
one full-ray atom pair gives the paper kernel

    K_epsilon(m,n) = z^(-1-epsilon)/(1+epsilon)
      -(sqrt(m)+sqrt(n))*z^(-3/2-epsilon)/(3/2+epsilon)
      +sqrt(m*n)*z^(-2-epsilon)/(2+epsilon).

For n>=m this is

    n^(-1-epsilon)/(2*(3/2+epsilon)) *
      (1/(1+epsilon)-sqrt(m/n)/(2+epsilon)).

This calculation is for a finite coefficient truncation before integration;
it does not exchange an unadmitted infinite arithmetic sum and integral.
The actual prefix moment up to N retains a terminal subtraction. With
P_N=sum_{n<=N}c(n) and R_N=sum_{n<=N}c(n)*sqrt(n), it equals

    sum_{m,n<=N} c(m)*c(n)*K_epsilon(m,n) - B_epsilon(N),

where the complete terminal quadratic is

    B_epsilon(N) = P_N^2*N^(-1-epsilon)/(1+epsilon)
      -2*P_N*R_N*N^(-3/2-epsilon)/(3/2+epsilon)
      +R_N^2*N^(-2-epsilon)/(2+epsilon).

B is the nonnegative full-ray energy of P_N*sqrt(x)-R_N on x>N. Its mixed
term must remain; the current trial seeks a uniform upper bound for the
whole displayed difference, not separate bounds for its pieces. This is a
paper representation of the unpaid positive moment, not an audited theorem,
new payment, or replacement completion criterion added to Lean.

Read `MobiusMertensMeanSquareExponentLaw`: its upper estimates retain the
unknown zeta-zero abscissa, and the converse is an exponent criterion.
`MoebiusMeanSquareUnconditional` supplies a vanishing relative twist factor
with a restricted frequency band; its stated bound does not supply the
missing critical power. No critical Mertens moment or square-root estimate
was assumed. The next attempt should estimate the complete centered
arithmetic pair form with its terminal subtraction, or the corresponding
Mellin-weighted unpaid lcm sector. Do not implement the kernel identity alone
as frontier progress. Both native history-square debts and RH remain open.

## RP-42: Selberg product pairing leaves the complementary phase energy

No verified frontier advance. Read `DirichletLogDerivation`,
`DirichletSummatorySwap`, `SelbergWeightEvaluation`, and the relevant
recursion in `SelbergSecondInequality`. The exact Selberg identity is
Lambda*log + Lambda convolution Lambda = (log squared) convolution mu.
The bilinear regroup is by the product of the indices. It cannot be applied
unchanged to the max-index kernel above, which retains their ratio.

The centered identity was checked algebraically on paper, preserving the
Euler atom. Write z(n)=1 for n>=1, delta for the convolution unit, a=2*gamma,
c=Lambda-z+a*delta, and L for pointwise multiplication by log. All these
arithmetic functions are set to zero at index zero. Then

    L(c) + c*c - 2*a*c
      = mu*(log squared) - 3*log + z*z - a^2*delta.

Stars here mean Dirichlet convolution. This remains a product-index
identity; centering does not turn its square into an autocorrelation.
Neither its forcing nor its mixed terms were assigned an unproved sign.

The finite RP-41 kernel makes the missing part explicit. Put
sigma=(1+epsilon)/2 and beta=sigma+1/2. On paper,

    K_epsilon(m,n) = (m*n)^(-sigma)*kappa(log(m/n)),
    kappa(u) = (exp(-sigma*abs(u))/sigma
                 - exp(-beta*abs(u))/beta)/(4*(sigma+beta)).

This is the Gram kernel of the causal difference of the two exponentials.
For the finite polynomial F_N(w)=sum_{n<=N} c(n)*n^(-w), its full-ray
quadratic form Q_N therefore has the paper spectral expression

    Q_N = (1/(8*pi))*integral_R
      abs(F_N(sigma+i*t))^2/((sigma^2+t^2)*(beta^2+t^2)) dt.

The corresponding signed expression with Re(F_N squared) is

    W_N = (F_N(2*sigma)^2/sigma
             - F_N(sigma+beta)^2/beta)/(4*(sigma+beta)).

Both real arguments exceed one, so absolute source convergence bounds W_N
uniformly in N for each fixed epsilon>0. This is only the signed part:

    Q_N = W_N + J_N,
    J_N = (1/(4*pi))*integral_R
      Im(F_N(sigma+i*t))^2/((sigma^2+t^2)*(beta^2+t^2)) dt.

Consequently the actual prefix moment remains W_N+J_N-B_epsilon(N).
The terminal quadratic B is exactly the one retained in RP-41. The missing
estimate is an upper bound for J_N-B, jointly. A bound on a convolution
square, or on the difference of the real and imaginary energies, does not
supply it. This diagnoses the attempted estimate; it is not a no-go for
the actual native source and does not retire Route RP.

`CriticalCenteredPrimeTailPassivityNoGo` separately excludes a generic
positive-definite realization of its centered current. Its current differs
from c at the unit atom, so its theorem was not transferred verbatim to RP.
The negative non-prime-power coefficients persist away from that atom;
none were discarded in the present pair form.

These are finite-source paper diagnostics, not Lean certificates or a new
critical bound. No identity-only leaf was added. Next attack must retain
the ratio twist in the centered Selberg cross-convolution and estimate its
actual source contribution together with B. Untwisted product regrouping,
coarse absolute Selberg recursion, and assumed positive-moment admission
do not close this gap. Both native history-square debts remain open.

## RP-43: opposite twists and the coupled finite convolution tail

No verified frontier advance. The corpus's `dirichletShift_mul` preserves
Dirichlet convolution under a multiplicative complex-power twist. The
literal source coefficient is c=mu*g, where

    g(n)=log(n)-tau(n)+2*gamma, n>=1.

Its cumulative sum is the actual prime-free divisor defect. Applying
opposite twists gives the paper coefficient identity

    c_t*c_(-t) = (mu_t*mu_(-t))*(g_t*g_(-t)).

This retains the ratio phase, but estimating g's square-root-bounded
cumulative source does not estimate the two inverse factors at the
critical exponent. No such operator estimate was assumed. The entire
divisor numerator also does not remove either inverse zeta factor.

Read `LocalizedHalfDensityCurvature`'s opposite-twist von Mangoldt fibres.
Its three-prime vanishing and exact two-prime cosine apply to Lambda_t
convolution Lambda_(-t). For c=Lambda-z+a*delta, a=2*gamma, the full cross
product additionally contains

    -Lambda_t*z_(-t) - z_t*Lambda_(-t) + z_t*z_(-t)
    +a*(Lambda_t+Lambda_(-t)-z_t-z_(-t)) +a^2*delta.

These terms restore product layers outside the two-prime support. Neither
their signs nor their cancellation was inferred from the Lambda-only
fibre theorem. The queried logarithmic convolution bound has a different
pair of sequences and does not bound this centered product.

The next trial coupled the actual finite source to a finite zeta sum,
without dividing by it. For N>=1 define finite polynomials

    Z_N(w)=sum_{n<=N} n^(-w),
    F_N(w)=sum_{n<=N} c(n)*n^(-w),
    G_N(w)=sum_{n<=N} g(n)*n^(-w),
    E_N(w)=sum_{d,e<=N, d*e>N} c(d)*(d*e)^(-w).

Coefficient convolution and the exact finite hyperbola swap give on paper

    Z_N(w)*F_N(w)=G_N(w)+E_N(w),
    G_N(w)=sum_{d<=N} c(d)*d^(-w)*Z_floor(N/d)(w).

Both rectangular cutoffs in E_N are essential. Replacing it by an
untruncated product-index convolution loses actual source terms. This
identity is valid before any infinite series admission or zero-free claim.

The large leading term of Z_N cannot by itself pay F_N. For w!=1 write

    A_N(w)=N^(1-w)/(1-w),
    r_x(w)=Z_floor(x)(w)-x^(1-w)/(1-w), x>=1.

The exact same finite equation is

    G_N(w)=A_N(w)*F_N(1)
      +sum_{d<=N} c(d)*d^(-w)*r_(N/d)(w).

Thus the A_N*F_N(w) term cancels against the tail's leading term, with
coefficient exactly one. Read `ZetaPartialSumStrip` and `Sieve.ZetaTruncated`
for the actual fractional-part remainder and r_N(w)->zeta(w) when Re(w)>0,
w!=1. This fixed-point limit is not uniform through d near N, where N/d
stays bounded. The actual Mertens and harmonic constants give F_N(1)->0;
no power rate sufficient to control A_N*F_N(1) was extracted from this
limit. The remaining terms require a joint signed estimate.

The search hit `finiteCutoffZeta` is a Bernoulli-corrected approximation,
defined through `finiteCutoffResidual/(s-1)`, not Z_N above. Its approximation
and contour theorems were not substituted for raw polynomial estimates.
Likewise a proposed divisor-tail bound requiring sigma>3/2 does not apply
to the missing interval 1/2<sigma<1.

Neither trial bounded J_N-B_epsilon(N) or the native history. No new Lean
leaf, assumed bound, or no-go retirement. Next attack: integrate the actual
signed cutoff-tail work against the physical cutoff weight, retaining its
coupling to the RP-41 terminal quadratic. This is the complete zeta
convolution tail, not the earlier absolute prime-power renewal induction.
The target remains source payment; the finite identity alone is not progress.

## RP-44: admitted complete coprime budget and native sign obstruction

The integrated attack produced an actual source estimate. For the native
unsigned head U, W(y)=y*U(1/y)^2 is nonnegative, bounded, supported in(0,1),
and has positive mass C. The full source A(y)=sum_n mu(n)*W(n*y) satisfies
Mellin(A,s)=Mellin(W,s)/zeta(s) with absolute admission for Re(s)>1.
At s=1+epsilon the budget tends to0, and its quotient by epsilon tends to C.
RoutePCoprimeSquareMellin passed its leaf audit.

For u(t)=sqrt(exp(-t))*mobiusDivisorFullHead(exp(t)), exact source-faithful
transport gives A(exp(-t))=coprimeEnergy(u,t)=u(t)^2+coprimeCross(u,t).
RoutePCoprimeSquareNative passed its leaf audit and transfers both budget
limits to this actual complete coprime energy. The main positive theorems
have standard Lean axioms only. Both leaves are wired; no umbrella build.

The positive first-order zero also defeats pointwise positivity on this
native source. Were A nonnegative below1, its real Mellin budget would be
antitone in epsilon, contradicting its positive first-order zero.
RoutePCoprimeSquareSign passed final leaf and axiom audits. Its strongest
statement is existence of t>0 with
coprimeCross(u,t)<-u(t)^2. Thus even that local deficit bound cannot be used
to pay the square. This is not an RH falsification.

The source estimate is new verified information, but neither square debt
is paid. Any useful next lower bound must integrate signed work over whole
cutoff intervals and allow the native negative values; retain the terminal
quadratic. No uniform positive endpoint admission follows from the combined
budget. Eventual negative finite-prefix cross work remains a separate paper
candidate. See the native-coprime Abel-budget card and failed pointwise-
positivity card for exact scope and closure.
