# BAG local transverse-defect grid law

Route: signed physical BAG cubic. Paper proof and production/standard-axiom audits complete.
Corpus basis: literal prime-square base/tag in ChiRamanujanCriticalGridSource,
its public Fourier laws, and exact defect in ChiPrimeGaussianCubicTransverse.

## Exact all-test signed law

For a prime p let b(a)=1_(a=0)-1/p on F_p, t=1/p-1/p^2, and
C(Phi)=Phi(0)-sum_a Phi(a)/p, for ANY complex function Phi on F_p.
Multiplication by a nonzero field element permutes the field. The zero
row has sum p*Phi(0); each nonzero row has sum sum(Phi). Consequently

    sum_(a,b) Phi(ab) = p*Phi(0)+(p-1)*sum(Phi).

Expanding the two centered factors proves the exact four-placement law:

    sum_(a,b) b(a)b(b)Phi(ab) = -(1-1/p)*C(Phi),
    sum_(a,b) b(a)t Phi(ab) = t*(p-1)*C(Phi),
    sum_(a,b) t b(b)Phi(ab) = t*(p-1)*C(Phi),
    sum_(a,b) t*t Phi(ab) = t*t*(p*Phi(0)+(p-1)*sum(Phi)).

In particular, the untagged multiplicative pushforward has mass
-(p-1)^2/p^2 at zero and (p-1)/p^2 at each nonzero point. It is exactly
-(1-1/p) times the original centered base distribution. The zero atom and
the surrounding mass must be retained together. For the additive character
Phi(a)=e(n*a/p), orthogonality gives zero at n=0 and -(1-1/p) at EVERY
nonzero n. Thus zero-by-local-orthogonality is false.

## Literal source attachment

Map a in F_p to the prime-square grid node k=p*val(a). This is injective,
and its range is exactly the p-divisible nodes. At this node the ACTUAL
ramanujanGridBase is b(a), while ramanujanGridTag is t. The base vanishes
at every node outside this range, so every full base-weighted grid sum is
exactly the field sum, for every test. This includes zero and all
nonprimitive nodes, with no truncation or limiting operation.

The physical prime-frequency phase at these nodes is exactly

    e(p*(k/p^2)*(l/p^2)) = e(a*b/p).

Therefore the complete two-variable prime-square sum, weighted by both
literal bases, equals -(1-1/p). This is an exact signed source value,
not an estimate based on variation or an omitted constant mode.

## Boundary and next hard problem

The tag identities above are its restriction to the p-divisible subgroup;
the full tag also has primitive prime-square support. No global tagged
CRT product or full R^4 lifted-defect law is claimed. The local law alone
cannot replace the actual growing physical profile by a complete-period
average. The full signed pole/near-cone/tail coupling, all sectors and
complex norm o(N/log^2 N) remain open, as do growing moments, moving cofactors,
common-height self-return and RH. Positive survivor of the failed local
zero conjecture: the entire signed pushforward operator, not only a
negative example. Its exact statements are now Lean verified.

## Audit and search log

ChiRamanujanTransverseDefectGrid: 194 lines,17 public declarations.
Production86909 passes with empty log, lake --old env lean leaf -o.
Axiom89006 passes all17, only propext/Classical.choice/Quot.sound. The earlier
axiom69946 printed all17 correctly but its extra name probes had unresolved
universe levels; explicit universe parameters fixed that scratch-only error.
Index49770 passes, all17 exact API rows and one umbrella import verified.
Lint58246 has33 unrelated unreachable modules, all inspected, no new-leaf
or proof-debt finding; global lint not clean. No new axioms, numerical
experiment, full build, heartbeat change, subagent or commit.

Search84667 is nonpartial65786/no errors; all20 candidates/20 arguments and
its ingredient inspected. The residualProfile_le_sq suggestion concerns a
different Szego profile and gives no BAG cancellation. Search76592 is PARTIAL
65789 with interrupted text/source retrieval and a local-runtime reranking
deadline; all available20/20 and the ingredient inspected. Ramare energy
splitting does not identify the required defect. No absence claim made.
Search88818 is nonpartial65794/no errors; all20/20 and ingredient inspected.
It supplies units-sum and additive Fourier mechanisms, but addChar_sum plus
estermannAddTwistEntire does not prove weighted physical cancellation.
All have incomplete background refresh and mostly pending/source-only
compiler metadata. Source reading confirms KloostermanBilinear gives a
fixed-modulus norm q, not a new growing signed saving.

The proved law is for tests of the product. The full physical transition
also depends separately on both tangential coordinates. For a general
profile H(a,b), the next exact fibre formula must retain

    zero fibre: (1-1/p)^2 H(0,0)
      -(1-1/p)/p*(sum_(a!=0) H(a,0)+sum_(b!=0) H(0,b));
    nonzero delta fibre: p^(-2)*sum_(a!=0) H(a,delta/a).

Its two-variable finite Fourier expansion contains actual Kloosterman
inverse fibres. This next formula is not yet formalized; still less is its
full R^4 lifted-source attachment or a uniform signed physical estimate.
Do not replace H by a constant or a separable stationary approximation.
