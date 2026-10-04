# SZ: nonlinear prime forcing with its critical primitive retained

- **ID:** SZ-NONLINEAR-PRIME-FORCING
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (eventual sign); critical negative escape and exact upper-level comparison formalized
- **Source:** `CCMExponentialRampPrimeMoment`, `CCMCriticalMellinCompletedError`,
  `CCMSharpPrimeWindow`; continuation of SZ-JOINT-PHASE-CREDIT.
- **Statement:** Test eventual strict negativity of the actual normalized
  nonlinear age forcing, retaining its positive quadratic correction.

## Goal and exact objects

The final target remains the unconditional Gamma--prime--polar inequality
on canonical heads. This investigation concerns one actual arithmetic
forcing term in the signed age equation; it is not yet a proof of that
inequality and must not be used as an input hypothesis.

For T >= 0 let

    M(T) = criticalMellinPrimeMass T,
    psi(T) = criticalCumulative vonMangoldt (exp T),
    E(T) = (psi(T)-exp T)/exp(T/2),
    J(T) = integral from 0 to T of E(t),
    y(T) = 1 + M(T)/2 - exp(T/2),
    F(T) = exp(-T/2)*(M(T)+M(T)^2/4-psi(T)).

The exact arithmetic cutoff is floor(exp T)+1. The existing quantile
cumulative/prime-mass identity and `ccmExponentialRampPrimeMomentCumulative_eq_primeDiscrepancy`
identify F with the forcing in the actual age-moment equation.

Candidate: F(T) is eventually strictly negative. A stronger possible
version has an eventual negative constant margin. Neither version is
proved, and neither has been retired.

## Cancellation that the proof must preserve

The corpus's critical Mellin partial-summation identity gives

    M(T) = 2 exp(T/2) - 1 + E(T) + J(T)/2,
    y(T) = 1/2 + E(T)/2 + J(T)/4.

Substitution gives

    F(T) = 1 + J(T)/2 + exp(-T/2)*(y(T)^2-1).

The unsmoothed Chebyshev error cancels from the linear part. The positive
square remains. In particular, Chebyshev Omega-plus/minus alone cannot
refute eventual negativity of F. An initially considered oscillation
transfer to F had an incorrect factor of two and was rejected before
claiming a theorem. At T=0, E=-1, J=y=0, so the displayed formula gives
F=0; the endpoint constant is essential.

This cancellation is an auxiliary algebraic consequence of existing
source identities, not a claimed advance on the hard sign problem.

## Hard work still required

Obtain an unconditional upper bound for the joint expression

    J(T)/2 + exp(-T/2)*y(T)^2.

Bounding the two prime cumulatives separately loses this cancellation.
The available PNT-scale decay of relative quantile displacement does not
bound the positive square at the critical normalization. A conditional
RH estimate for J or E cannot be inserted into the proposed producer.
Even proving this forcing sign would still require a checked propagation
argument through the complete age, dissipation and terminal entropy
balance to the canonical-head target. No such implication is assumed.

The parallel canonical-ground inspection supplied existing fixed-point
and numerical-range identities, not an arithmetic lower bound. Do not
replace the signed numerical-range target by the stronger norm
contraction condition.

## Corpus and audit status

Deep searches1221338,1221365,1221424,1221440,1221454 were partial with
pending compiler coverage. Source identities were read directly; search
misses do not establish absence or novelty. No production Lean module,
RH receiver, numerical experiment, umbrella build, or axiom was added.

- 2026-10-04: auxiliary cancellation checked by
  `lake --old env lean /tmp/sz_nonlinear_forcing_probe.lean` in `formal`.
  Audit33974 exited0; its axiom query printed only `propext`,
  `Classical.choice`, `Quot.sound`. One non-semantic tactic-style warning.
  First probe47059 failed only on the order of multiplication in the
  final partial-summation rewrite; no failed proof entered the tree.
  This is a scratch verification of the displayed identity, not a new
  production theorem or proof of the forcing sign. Scratch removed after
  completion. The forcing sign and RH remain unresolved.

## Next proof attempt: cumulative compensation, not entrywise sign

At an arithmetic entry n, write w=Lambda(n)/sqrt(n) and
m=1+M_before/2. The increment of the unnormalized discrepancy is

    w*(m-sqrt(n)) + w^2/4.

Thus an entrywise negative-increment proof would need a signed displacement
estimate, including the positive w^2/4 correction. Relative displacement
tending to zero does not supply that sign. This entrywise argument remains
unproved; it has not been disproved for actual primes.

The next attack must estimate the accumulated signed entries, or the
equivalent J/2+exp(-T/2)*y^2, with actual von Mangoldt arithmetic retained.
The attempted separate-cumulative and ground-stationarity arguments did
not close that problem. No improvement in the canonical-head frontier
is claimed for this turn.

## 2026-10-04 continuation: actual first-contact geometry

The previous turn changed the next action by correcting the cancellation,
but proved no sign. Current cumulative-compensation search1221540 and
first-contact search1221567 are partial/source-only. The retrieved Selberg
second-grade identity retains a signed prefix error at a different scale;
it does not bound this forcing. `RoutePCompensatedMassRiccati` supplies the
actual continuous Abel primitive and its right derivative at prime entries.
Its conditional quadratic barrier has not been assumed.

Set m_n=1+primeMassHalf(n)/2 and

    U_n=2*sqrt(n)*m_n-n-psi(n)-1,
    D_n=m_n^2-psi(n)-1.

Then D_n=U_n+(m_n-sqrt(n))^2. Abel summation identifies U with
the continuous potential integral_1^x (m(t)-sqrt(t))/sqrt(t) dt.
At successive integers its exact increment is

    U_(n+1)-U_n
      =(sqrt(n+1)-sqrt(n))*(2*m_n-sqrt(n+1)-sqrt(n)).

First-contact theorem: if U_(n+1) is no larger than either neighbor,
the pre/post-entry masses lie on opposite sides of the adjacent square-root
midpoints. Consequently n+1 is a prime power and

    D_(n+1) < U_(n+1) + criticalMellinAtomWeight(n+1)^2/4.

This local valley law and its global consequence are now formalized in
`CCMPrimeMomentFirstContact`. If U_(n+1)<U_n and U_(n+1)<-1, a later
D_k is negative. Otherwise every subsequent step must descend; the square
identity forces m_k-sqrt(k)<-1, and each entering weight spends at least
half its mass from D. Divergence of actual M contradicts D>=0. Therefore
nonnegative D on k>=N forces U_k>=min(U_N,-1) on that tail.

Final leaf57414 and all9-public-declaration axiom audit24541 exited0.
Only the three standard axioms occur; unique umbrella import added without
an umbrella build. Global lint89088 failed on16 other unreachable modules.
Full proof and audit: P3:sz-prime-moment-first-contact.

## Negative potential escape plan (closed by the continuation below)

The first-contact theorem removes the permanently descending-tail obstacle
under the contrary nonnegative-forcing assumption. It does not force an
actual deep descent. The next conjecture is that U_n is unbounded below
on every integer tail. This would produce cofinal negative D, but would
still not prove the candidate eventual sign or the canonical-head target.

The following is the next paper argument to formalize, not a Lean result.
For T>=0 extend U to the actual continuous potential

    U(T)=sqrt(exp T)*(primeMassHalf(exp T)+2)-exp T-psi(exp T)-1.

The previously checked critical Abel identity gives
U(T)=exp(T/2)*(1+J(T)/2)-1. The corpus provides the exact Laplace transform
of E in Re z>1/2:

    L_E(z)=-(logDeriv G(z+1/2)+1)/(z+1/2), G(s)=(s-1)*zeta(s).

Integration by parts for J, retaining J(0)=0, consequently gives

    L_U(s)=-logDeriv G(s)/(s*(2*s-1)), Re s>1.

Assume U has a global lower bound -B. The density U+B+1 is at least1 and
has an exponential envelope. Its positive-measure Laplace transform has
a finite real abscissa c>=0. If c>1/2, the displayed continuation is
analytic at c: G has no positive real zero, and the rational denominators
are nonzero. The existing Landau singularity theorem contradicts this.
Thus c<=1/2. Real analytic uniqueness now identifies the positive Laplace
transform with L_U(s)+(B+1)/s for every real s>1/2.

Multiplying by s-1/2 and approaching from the right gives the proposed
contradiction

    0 <= -logDeriv G(1/2) = 2+gammaHardyPhaseRate(0) < 0.

The final strict sign is already in
`two_gammaHardyPhaseRate_zero_add_four_neg`; the equality uses the source
identities `logDeriv_zeta_eq`, `logDeriv_zeta_eq_logDeriv_xi`,
`re_logDeriv_xi_criticalLine`, and `logDeriv_Gammaℝ_of_re_pos`.
For real statements take real parts of the complex logarithmic derivatives.
The actual U Laplace admission and positive-measure continuation argument
still need Lean proofs. The central equality and strict negative sign
passed scratch audit32049, with only the three standard axioms. This
auxiliary check does not establish potential escape.

Integer escape cannot be inferred by ignoring entries. For x in [n,n+1],
U(log x) is a concave quadratic in sqrt(x), with constant pre-entry M and psi;
its limiting value at n+1 equals the post-entry value because jumps
cancel. Hence U(log x)>=min(U_n,U_(n+1)). This exact interpolation, also still
to formalize, transfers a contrary integer lower bound to the continuous
potential and allows the Landau contradiction to apply.

Search1221798 was partial with pending compiler coverage; a subsequent
lexical search returned direct Laplace-source hits without freshness
metadata. Neither search supplies the missing estimate as a hypothesis.

The central scratch imports were `ZetaLogDerivZeroDistance`,
`XiEdgeLogDerivativeBlindness`, `CCMActualHeadCoherentQuantileGammaNoGo`,
and `VisibleCoprimeZetaZeroJet`. The last import supplies
`zetaResidueUnit_ne_zero_of_ofReal_pos`; initial probe37887 failed only
because that import was missing. At s=1/2 take real parts of
`logDeriv_zeta_eq` and `logDeriv_zeta_eq_logDeriv_xi`; simplify with
`re_logDeriv_xi_criticalLine 0` and `logDeriv_Gammaℝ_of_re_pos`.
This proves `(-logDeriv zetaResidueUnit (1/2 : Complex)).re =
2+gammaHardyPhaseRate 0`. `two_gammaHardyPhaseRate_zero_add_four_neg`
then proves strict negativity. No new production receiver was added.

## 2026-10-04 continuation: source Laplace admission closed

`CCMPrimeMomentPotentialLaplace` now proves the continuous definition, exact
arithmetic source identity, exponential admission, and

    integral_0^infinity exp(-s*T)*U(T) dT
      = -logDeriv G(s)/(s*(2*s-1)), s>1.

Final leaf audit38295 exited0 without diagnostics. The finite integration
by parts and vanishing terminal term retain J(0)=0; the result does not
assume RH or a sign for either Chebyshev cumulative. The source identity
also passed in this production audit. Its full axiom audit and umbrella
wiring await the dependent escape theorem.

The corpus's existing `not_eventually_nonneg_of_negative_real_laplace_residue`
keeps compact-head corrections and only requires analyticity along the
real ray. Apply it to g(T)=(U(T)+B)*exp(-T/4), whose transform shifts the
negative central residue to the lemma's endpoint 1/4. This avoids a new
global zero-free hypothesis. The current escape scratch also contains the
exact concave-cell interpolation and first-contact consequence. Its first
check77770 failed on local analytic composition, scalar-cast and rational
algebra details, with no failure in the integer transfer or first-contact
argument. No escape theorem is certified yet; sorryAx in that failed
scratch's downstream reports is not acceptable evidence.

Deep source search1221960 was partial with compiler coverage pending. A
lexical follow-up directly found the negative-residue theorem; that result
provides no freshness metadata. Sources and Lean signatures were checked.

The source first-contact proof exposes a stronger conjecture than cofinal
negative forcing: D_n is unbounded below on every tail. Replace the
contrary lower bound D>=0 by D>=A, and the deep-descent barrier U<-1 by
U<A-1. At a valley, D<U+1<A is impossible; on a permanently descending
tail, D=U+y^2>=A still forces y<-1. The unchanged entry dissipation makes
D+M/2 nonincreasing, contradicting M->infinity and D>=A. Thus a lower
bound D>=A forces U>=min(U_start,A-1), which the proposed potential escape
contradicts. This translation argument is being checked in scratch, not
yet a certified strengthening. It addresses the positive-square obstacle
at arbitrary discrepancy depth, not a numerical optimization.

Scratch35106 now proves continuous escape, exact cell interpolation,
integer escape, and cofinal negative D. All three terminal axiom reports
contain only propext, Classical.choice, Quot.sound. Rational factorization
2*(s+1/4)*(s-1/4) resolved the residue cancellation without increasing
heartbeats. Remaining diagnostics were tactic-style warnings, corrected
in the production candidate. The arbitrary-level strengthening is now
being checked separately; the final production/axiom audits remain due.

Search1222173 was partial, with compiler coverage mostly pending or stale
and semantic retrieval timing out. Candidate/source/proposed-ingredient
sections were inspected; irrelevant residue and Hodge hits supplied no
missing forcing theorem. The source's exact nonlinear balance was also
read: action+dissipation+2*exp(-T/2)*D=ageMoment+terminalEntropy. Thus
unbounded negative D alone does not control its critical normalization or
the other terms and is not a canonical-head sign proof.

The arbitrary-level first-contact strengthening passed scratch89827
with standard axioms, then production audit37824 without diagnostics.
It proves U_(n+1)<U_n and U_(n+1)<A-1 imply some later D_k<A.
Consequently D>=A on a tail forces U>=min(U_start,A-1). The previous
zero-level API is retained as a specialization. Potential escape now
supplies the producer for unbounded negative D, rather than only D<0.
The dependent escape leaf's final audit is running.

Production escape audit95916 found one tactic-control-flow regression in
warning cleanup: the limit proof's `convert` had two goals, while the
replacement semicolon chain solved only the function equality. Replaced
that chain with separate `rfl` and `norm_num` bullets. No mathematical
argument changed; re-audit is required and running.

Global lint44412 exited1 with14 unrelated unreachable-module errors; no
error named the three prime-moment leaves. The two new leaves each have
one umbrella import. No umbrella or full build was run.

## Current verified frontier

All three production leaf audits have passed: source Laplace38295,
generalized first contact37824, and negative escape87799. The new terminal
theorem is `ccmPrimeMomentDiscrepancy_negative_escape`: for all real B
and natural N, some n>=N satisfies D_n<-B, with no mathematical premises.
Full dependency-closed proof and final axiom audit are recorded in
P3:sz-prime-moment-potential-escape. The missing deep-descent producer is
closed. The original eventual-sign conjecture remains open; it is not
proved by cofinal escape or by unbounded unnormalized amplitude.

The prior hard target was control of the actual joint critical expression
J(T)/2+exp(-T/2)*y(T)^2, followed by propagation through the complete
age/dissipation/terminal balance to the canonical-head joint sign. Keep
the positive square, actual prime entries, compact head and physical
normalization. No new conditional RH receiver is warranted.

Final axiom audit16658 exited0 for all24 public declarations across the
three leaves; every report contains exactly the standard three axioms.

The next concrete sign obstruction is return from the now-proved deep
negative discrepancy basins. At an actual entry with w=Lambda(n)/sqrt(n)
and pre-entry mass m=1+M_before/2,

    Delta D = w*(m-sqrt(n))+w^2/4.

Any later return to D>=0 must accumulate enough positive signed admission
work to repay the entire basin depth. The hard remaining task is to
exclude such returns on every sufficiently late tail using the actual
joint primitive/quadratic arithmetic, or find an actual countermechanism.
No entrywise sign, independent-prime phase law, or bound on unnormalized D
supplies that estimate. This is an attack on the original eventual sign,
not a new conditional RH theorem. The complete canonical-head balance
still needs its own propagation proof even if this estimate succeeds.

## Upper-return obstruction closed (2026-10-04)

`CCMPrimeMomentUpperContact` proves an actual return comparison, not an
assumed arithmetic barrier. Starting with mass above sqrt(n), a first
subsequent contact must occur, or U would be nondecreasing despite its
proved negative escape. D increases until contact, where U(log(m_k^2))
equals D_k. Every upward D crossing therefore forces a potential crossing.
Actual negative D escape supplies a starting value below any chosen A.
Consequently D_n<A eventually iff U(T)<A eventually, for every real A.

The eventual-sign problem is now reduced to the linear tail inequality

    J(T)<-2+2*exp(-T/2).

The positive square cannot create independent eventual finite-ceiling
returns. This does not bound it pointwise, prove the linear inequality,
or give a uniform negative margin after critical normalization. The
canonical-head joint sign still needs the full signed propagation.

Final leaf73270 and all4-public-theorem axiom audit72769 passed; only the
standard three axioms. One umbrella import, no umbrella build. Lint67589
failed on14 other unreachable modules. P3:sz-prime-moment-upper-contact
contains the complete proof, audit, and exact timing limitation of the
return witness.

At the constructed contact, the actual quantile boundary equals log(m_k^2)
and floor(m_k^2)=k. Existing source formulas then have zero terminal
entropy mismatch. The contact-to-entropy consequence has not been
exported separately in Lean. A next signed-balance attempt can use this
matched head while retaining age and bulk dissipation; their sign is not
provided by matching. No unconditional RH conclusion is claimed.

## Direct linear-primitive attack after upper contact

Current hard producer is U(T)<0 eventually, equivalently
J(T)<-2+2*exp(-T/2). For x=exp(T), exact source algebra rewrites this as

    sqrt(x)*primeMassHalf(x)-psi(x) < (sqrt(x)-1)^2.

The left side is the existing routePAbelMassPrimitive. This is the actual
prime-versus-polar signed Riesz comparison; it is not supplied as a
premise to a new RH receiver. The source whole-tail upper bound is still
open.

Search1222739 was partial with pending coverage and local-runtime
semantic deadline. Candidate/source/ingredient sections were inspected.
Source inspection checked CCMCriticalMellinPolynomialCancellation: all
fixed polynomial savings still multiply exp(-T/2), so their absolute
primitive bounds do not produce a constant upper ceiling for signed J.
CCMCriticalMellinRieszMobiusRenewal retains the full divisor cube and
collapses it exactly to negative von Mangoldt renewal; it supplies no
independent positive probabilistic correction. The remaining comparison
is exactly with the polar continuum. Neither mechanism was retired as
false, and no absence/novelty claim follows from the search.

A deeper actual-Abel comparison search is now running as86480; no Lean build or production edit has begun in
this direct-sign turn. The task is still the signed upper barrier, not
another algebraic equivalence.

### Critical normalization: residue and normalized valleys

The completed-source Stirling correction is strictly negative, but its
weld leaves an uncontrolled signed completed response. It does not prove
the primitive tail bound. Search1222789 completed retrieval with snapshot
coverage; compiler metadata remains largely pending/stale. Its suggested
Abel remainder ingredients concern other carriers, not this sign.

New conjecture for the actual forcing: there is c>0 such that, on every
integer tail, D_n < -c*sqrt(n). This closes a qualitative normalization
gap left by unscaled negative escape; it is not eventual negativity.

Paper mechanism under investigation:

1. Put kappa=-(2+gammaHardyPhaseRate(0))>0. Adding c*exp(T/2)
   to U adds c to the negative central residue. For 0<c<kappa,
   the same compact-head Landau argument forces U(T)<-c*exp(T/2)
   cofinally. Square-root cell concavity transfers this to integers.
2. Normalize W_n=U_n/sqrt(n). Its exact increment has sign of
   psi(n)+1-sqrt(n)*sqrt(n+1). Both Chebyshev oscillation signs
   therefore supply arbitrarily late increasing and decreasing steps.
3. Minimize W on a finite interval starting with a decreasing step,
   containing a low W value, and ending with an increasing step. An
   interior minimizing index is a prime-entry valley, with W<=-c.
4. At that valley, n<=psi(n)+1<n+Lambda(n); the entering weight
   Lambda(n)/sqrt(n) tends to zero. Hence m_n<sqrt(n)-c/4 for all
   sufficiently late such valleys and D_n=m_n^2-psi(n)-1
   <-c*sqrt(n)/4. Every prime and positive square is retained.

This is a proposed dependency-closed paper mechanism, not a Lean claim.
Check the adjacent square-root midpoint bounds carefully in step4.
Next: audit the residue extension, exact normalized increment, finite
valley selection, and actual critical forcing conclusion. No computation,
RH premise, or sign hypothesis is permitted in the final conclusion.


### Critical negative amplitude closed

P3:sz-prime-moment-critical-escape now records a complete paper and Lean
proof: there exists c>0 such that every integer tail contains n>=1 with
D_n<-c*sqrt(n). The positive displacement square is controlled at actual
normalized valleys, selected using BOTH proved Chebyshev oscillation signs.
This is a critical normalized amplitude, not merely unscaled divergence.

Final production audits7468/32271 and all9 public axiom queries61451 pass;
only propext, Classical.choice, Quot.sound occur. New leaf
CCMPrimeMomentCriticalEscape is wired once. Global lint42518 reports37
unrelated unreachable modules and no error for either touched leaf.

The eventual-sign conjecture remains open. Next direct attack: bound
signed recovery from these actual negative valleys enough to prevent
later upward crossings of the linear primitive barrier. Preserve the
full signed Chebyshev history and the canonical age/dissipation/terminal
balance; cofinal negative amplitude alone supplies neither bound.
