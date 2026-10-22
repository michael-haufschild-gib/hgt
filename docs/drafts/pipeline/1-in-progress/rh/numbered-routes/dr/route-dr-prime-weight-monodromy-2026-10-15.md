# DR: prime-weight continuation and the first-trace obstruction

Status: in progress. The RH-facing construction is not proved.

The target remains an actual Euler-marked Kummer root on the strict right
half-plane. This card tests a source construction; it does not substitute
another conditional criterion for that construction.

## Exact candidate

For Re(s)>1 define the Euler germ

    L_i(s) = product_p (1-i*p^(-s))^(-1).

Equivalently its Dirichlet coefficient at n is i^Omega(n), where Omega counts
prime factors with multiplicity. Define its pole-cleared germ by

    F_i(s) = exp(i*Log(s-1)) * L_i(s),

using the logarithm on Re(s-1)>0. Candidate: the finite Z/4 grading of these
coefficients admits a source-defined, single-valued meromorphic continuation
of F_i to Re(s)>1/2, agreeing with this germ.

The candidate is exact and falsifiable, but its continuation claim is not
an available theorem. A construction from the finite grading is the issue
being tested. Meromorphy, rather than an assumed absence of zeros or poles,
would be sufficient to eliminate the original Kummer obstruction.

## Why this would control the actual divisor

Write, on Re(s)>1,

    G_z(s) = sum_p sum_(k>=2) (z^k-z)*p^(-k*s)/k.

For |z|<=1 this series converges normally on Re(s)>1/2. On any compact
subdomain, |p^(-s)|<=p^(-sigma) for some sigma>1/2, and the k>=2 tail is
bounded by a constant times p^(-2*sigma); sum over primes is bounded by the
convergent sum over positive integers. The same compact argument establishes
holomorphy. Thus exp(G_z) is an explicit analytic unit there.

Euler logarithms give the local identity

    L_z = exp(z*log(zeta) + G_z),
    F_z = exp(z*log((s-1)*zeta) + G_z).

Here E(s)=(s-1)*zeta(s) has its removable value E(1)=1 filled in; it is not
the pointwise product of totalized Lean functions at s=1.
The second formula uses continuation of the marked logarithm, not a
single-valued logarithm whose existence is being assumed. At a finite-order
zero rho of E(s)=(s-1)*zeta(s), of order m, a positive meridian changes F_z
by exp(2*pi*i*z*m). Its logarithmic derivative has residue z*m. A nonzero
meromorphic germ has an integer logarithmic-derivative residue. For z=i,
i*m can be an integer only when m=0. Consequently meromorphic continuation
of F_i would force E to have no zeros in the strict right half-plane and
would give all Kummer roots there. Conversely, zero-freeness supplies an
analytic logarithm on this simply connected domain and hence F_i.

Topologically this is the same integral sheet-return charge used by DR:
the character m -> exp(-2*pi*m) detects the integer charge faithfully in
one source. It changes the detector; it does not annul the charge.

This is an exact detector of the missing continuation, not an independent
proof of it. The order/monodromy calculation is ordinary local analytic
theory and is not being claimed as new scientific knowledge.

## Attempted construction from the finite grading

For a finite prime set P, let L_(z,P) be the finite Euler product. The
four character factors satisfy the exact polynomial norm identity

    product_(z in {1,i,-1,-i}) L_(z,P)(s)
      = product_(p in P) (1-p^(-4*s))^(-1).

The right side has an unconditional analytic, nonvanishing limit on
Re(s)>1/4. It supplies the total graded determinant, not the individual
character factors. In the logarithm, the four first-trace coefficients sum
to zero. The individual character-i factor retains i*sum_p p^(-s).
Removing all k>=2 terms therefore leaves precisely the first prime trace.
The finite grading has cancelled that term in the total norm; it has not
constructed it in an individual character sector.

The same issue occurs in a Hilbert--Schmidt construction. With the cyclic
four-state matrix C and prime diagonal p^(-s), the full matrix trace at
each prime is zero and the grouped determinant is well defined. The
individual eigenspace projection recovers the divergent first trace.
Regularized determinants supply exp(G_i), which is already a unit, while
the missing scalar exponential still has the original local charge.

There is also a pole-normalization issue at finite stages. L_(i,P) is a
unit at s=1, so multiplying it by (s-1)^i introduces nontrivial monodromy
there. The infinite source cancels that monodromy through zeta's actual
pole. Thus even the pole-filled finite/infinite comparison must be proved;
it is not a limit of identically trivial marked covers on a neighborhood
of 1. Treating the pole counterterm as an unramified finite-stage unit
would be incorrect.

Verdict: BRIDGE. The residue test is valid; the proposed finite-grading
construction does not yet prove its continuation premise. Do not count
ordinary meromorphic-ODE or determinant criteria as progress on RH.

## Corpus audit and boundaries

The actual `LocalDivisorJetEulerResidueParity.lean` source proves that its
canonical alternating jet form is nondegenerate exactly at even jet
length. This eliminates a pairing-only parity proof before implementation.

`XiPoleClearedFirstTraceHalfODE.lean` already gives an Euler-anchored ODE
equivalent to the first root rung. Replacing its coefficient 1/2 by i
changes the divisibility detector, not the need to produce a global solution.

`PrimeFirstTraceCompleteNoEscapeUniversalityLaw.lean` and
`PrimeFirstTraceTopologicalNonlinearRiggingNoEscapeUniversalityLaw.lean`
rule out closed extensions for their specified prime-Hardy source topology,
including nonlinear closed graphs and exact-norm riggings. Their explicit
null sequence uses signed, growing two-prime coefficients. These theorems
must not be overstated as impossibility of every construction on the fixed
arithmetic curve. They do prevent citing a generic completion theorem in
that topology as the missing first-trace producer.

The two current corpus searches completed without partial retrieval. Their
compiler coverage is mostly pending/stale; source reading and explicit
Lean checks, not retrieval scores, determine what is verified. External
audit is omitted under the user's instruction. No numerical experiment is
part of this candidate.

## Open core and next proof obligation

OPEN CORE: construct the individually marked character-i source across
Re(s)>1/2, or derive a source restriction forcing its monodromy to be
meromorphic. A construction of the total four-character norm or the
regularized higher-trace factor does not discharge this obligation.

Before any new Lean module: locate additional arithmetic structure that
controls the individual first trace, prove its applicability to this exact
source, and finish the resulting paper proof. Do not formalize the detector
as if it were a producer. DR and the unconditional RH goal remain active.

## Verification and audit

The scratch command `lake --old env lean /tmp/hgt_dr_prime_weight_audit.lean`
exited 0. It checked two exact ingredients: the four-character local norm
polynomial, and the meromorphic residue obstruction with an arbitrary
continuous regular correction. Precisely, if finite-order meromorphic
germs f,g satisfy logDeriv(g)=i*logDeriv(f)+q off the center, with q
continuous at the center, then ord(f)=0. Both axiom checks returned only
`propext`, `Classical.choice`, `Quot.sound`. An initial filter-type inference
error was corrected before this successful run. These are scratch checks
of standard ingredients, not an integrated new theorem or verification of
the source continuation conjecture.

No repository Lean source was changed. No full/umbrella build, numerical
experiment, external search, lint rerun, or index rerun was performed.

Anti-theatre: no new scientific theorem or zero-free region was obtained.
The finite-grading construction was followed down to its surviving first
trace rather than accepted from the total norm identity. The continuation
conjecture remains unproved. The next attempt must attach an actual
single-character period to the source across the strip; further residue
criteria, total norms, or generic completion machinery would repeat this
cycle. No step was deferred because of difficulty or effort.
