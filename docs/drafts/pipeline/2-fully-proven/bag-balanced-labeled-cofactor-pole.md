# BAG signed balanced labels and numerator cofactors

- Route: actual signed BAG cubic.
- Stage: dependency-closed paper proof; both production leaves and all31 axiom audits pass.
- Corpus basis: ChiRamanujanCriticalGridSource, ChiRamanujanShiftedCubicTrace,
  ChiRamanujanDistinguishedPrimeLabels, ChiRamanujanWeightedDistinguishedCubic;
  mathlib principal-character L-series and continuation.
- No growing physical saving or RH proof.

## Balanced trace [PROVED HERE]

For finite prime set S write A=product_(p in S)(1-1/p),
a_p=log(p)/p, b_p=log(p)/(p-1), L=sum_p a_p.
The actual grid base and distinguished tag are (1-z)c_z(i) and
(1-z)z*c_z(i+1). For labels p,q,r, sum their normalized cubic over EVERY
valuation pair at every retained prime, with weight product_l l^(-i_l-j_l).
Retain p!=r AND q!=r, the exact two physical label exclusions; p=q is allowed.

For a local prime l, the established complete shifted trace is
z^(-c)*c_z(a+b-c)/(1-z)^2, where a,b,c are the three label indicators.
At l=r the exclusions force a=b=0,c=1, giving -(1-z)^(-3).
At every other prime c=0 and a+b>=0, giving (1-z)^(-2), including p=q.
Multiplication and the exact grid normalization give

    label trace = -A*b_r*a_p*a_q.

All local sums are absolute. Finite products and the finite label sum may
therefore be interchanged. Summing the two remaining labels factors a square:

    complete noncontracting trace = -A*sum_r b_r*(L-a_r)^2.

A and all a_p,b_p are positive. With at least two primes, each row has a
positive retained summand. With at most one, every row is zero. Thus the
trace is nonpositive, and strictly negative iff S contains distinct primes.
This exact negative square formula is the positive structural survivor of
the proposed balanced cancellation; it does not retire BAG.

## Cofactor completion [PROVED HERE; LEAN VERIFIED]

The valuation-support restriction used in the finite trace also restricts
numerator primes. The actual finite denominator grid does not do that.
For R=product S, keep every positive numerator cofactor coprime to R.
Its Dirichlet series C_S(s) is the principal-character series modulo R.
For Re(s)>1 it sums absolutely and equals

    C_S(s)=zeta(s)*product_(p in S)(1-p^(-s)).

The current mathlib principal-character continuation proves this identity
away from s=1 and residue A at 1. This includes S empty, R=1; the L-series
zero-index convention excludes n=0 even though it is coprime to 1.

Define the finite weighted labeled Euler expression F_S(s,t) using the
established complete weightedShiftedLocal formula, retaining the fixed source
z=1/p and the two independent weights x=p^(-s),y=p^(-t). For Re(s),Re(t)>0,
its full finite-prime valuation sum is absolute. At (1,1) it is the complex
cast of the balanced trace above, by uniqueness of HasSum. Every local Euler
expression is rational in x,y with possible denominators only x,y,1-x,1-y
and the fixed 1-z. None vanish at (1,1); hence F_S is continuous there.

The full mixed source indexed by retained-prime valuations and TWO positive
coprime numerator cofactors has absolute sum F_S(s,t)*C_S(s)*C_S(t) in
Re(s),Re(t)>1. Multiplication of the two independent punctured limits gives

    lim_(s,t)->(1,1) (s-1)*(t-1)*F_S(s,t)*C_S(s)*C_S(t)
      = -A^3*sum_r b_r*(L-a_r)^2.

Both complex variables and both physical label exclusions remain. For two
or more retained primes the coefficient is strictly negative, not zero.
No unordered critical rational HasSum or uniform prime-set limit follows.

## Open mathematical obligations

The mixed-source formula still needs a proved rational reindexing to the
complete denominator-restricted source and a justified pairing with the
actual growing physical test. The pole, all integer lifts, the full Mellin
line and the entire near-cone/tail region cannot be discarded. Prove their
combined signed o(N/log^2 N) action; then growing moments, moving cofactors
and common-height self-return. These are the hard remaining BAG problems.

## Audit log

ChiRamanujanBalancedLabelTrace (190 lines,13 public declarations) passes
production3062 with empty log. ChiRamanujanCofactorPole (308 lines,18 public
declarations) passes production30300 with empty log. Both final audits use
lake --old env lean on the leaf with explicit olean output, without a full
or umbrella build. Combined axiom6422 passes all31 declarations with only
propext, Classical.choice and Quot.sound. Index92350 passes; all31 exact
module/name API rows and each single umbrella import are verified.

Lint73204 exits1 with25 unrelated unreachable-module errors, all inspected;
no new-leaf or proof-debt finding. Global lint is not clean. Development
heartbeat failures were eliminated by splitting continuity and using explicit
HasSum arguments, never by raising limits. No mathematical premise was added.
The earlier combined probe's universe-inference error is superseded by the
successful final all31 axiom audit.

Searches37838 and95868 are nonpartial with complete inventories65755/65757.
Search5904 for the next rational reindexing is PARTIAL (source_retrieval
interrupted), with complete inventory65761. Background refresh is incomplete
and compiler metadata mostly pending/source-only. All candidate lemmas,
source arguments and proposed ingredient sets were inspected. The proposed
Deninger-ray ingredient in5904 is unrelated and rejected. No absence claim.

Completed scratch sources are removed; logs and search JSON are retained.
No numerical experiments, subagents, added axioms, heartbeat changes,
full/umbrella builds or commits. RH goal remains ACTIVE.
