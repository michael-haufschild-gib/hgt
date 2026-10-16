# FU: structural cancellation research

Status: in progress. Target: one unconditional structural theorem that removes
an actual obstruction in FU; no improved estimate, RH receiver, or numerical
certificate qualifies.

## Evidence and constraints

Read the FU entry in the current frontier map and the corresponding Lean
sources. Corpus searches cover all Lean areas; focused searches inspect
MobiusDivisor machinery. Search metadata reports source-only declarations and
incomplete semantic coverage, so source statements and final Lean checks are
authoritative. No external search or novelty audit is requested or performed.

The canonical square-root processed core has unbounded normalized energy.
Terminal balancing and prime-exhaustive geometric checkpoints exist, but their
collars leave gaps and do not pay the completed action at earlier cutoffs.
Positive processed-core squares lose the signed background/copy covariance.
The literal logarithmic counting measure pays copied diagonals exactly but
leaves cumulative signed correlation unresolved.

## Conjecture ledger

1. Use monotone positive residual energy to propagate checkpoint payment.
   Rejected by existing nonempty-energy and growing-core obstructions.
2. Remove the large-dilation-prime restriction from the two-scale fibre law.
   Likely elementary from the all-label product interpolation already proved;
   insufficient structural progress even if formalized. Do not pursue as the
   requested contribution.
3. Investigate simultaneous source-faithful control of several prescribed
   prime interactions. Existing inherited-core construction controls one
   prescribed insertion, with an explicit delayed net-repayment obstruction.
   Determine whether joint control removes a real compatibility obstruction
   or merely repackages sequential one-prime preparation.

## Surviving conjecture: prescribed prime cube preparation

For every nonempty inherited finite prime core P and every finite disjoint
target prime block T, there is an actual helper core S beyond any prescribed
prime bound such that every nonempty alternating Boolean difference is
strictly positive at every intermediate target subset, on one common
eventual integer-cutoff tail. This strengthens the initial edge-only
conjecture to strict complete monotonicity of the entire prescribed cube.
The same S works for every intermediate subset, every order of difference,
and every ordering of the target insertions.

Precisely, write Q(M,C) for `mobiusDivisorSelectionEnergy M C` and κ(C)
for its fixed-core quadratic coefficient. For every such P,T there is W>0
such that for every B there is a prime set S, disjoint from P union T,
all of whose primes exceed B, with sum(p in S) 1/sqrt(p)<=W, satisfying

    sum(E subset D) (-1)^|E| κ(P union S union A union E) > 0

for every A subset T and every nonempty D subset T minus A. There is also
one M0 such that, simultaneously for all these A,D and every integer M>=M0,

    sum(E subset D) (-1)^|E| Q(M,P union S union A union E) > 0.

Grade one gives strict insertion contraction. Higher grades give a common
strict complete-monotonicity law rather than independently chosen signs.
The closed Lean capstone quantifies over finite sets of `Nat.Primes`,
anchors the inherited core at 2, and has no analytic or arithmetic premise.

This differs from the existing common-reserve construction: target primes
are prescribed in advance, rather than chosen as a new reserve pair. It also
differs from sequential single-target preparation: later preparation must
preserve all previously arranged signs, including all intermediate cores.

### Dependency-closed paper mechanism

Write E_P(t) for the literal finite Euler multiplier at 1+it and
w_P(t)=|Mellin(head_P)(1+it)|^2. The corpus proves w_P continuous,
nonnegative, integrable, and strictly positive at zero. The exact release
coefficient for p is a strictly positive arithmetic factor times
integral w_P(t) cos(t log p) dt. Disjoint insertion of A multiplies w_P by
|E_A|^2, with no change of source or contour.

Let R={1} union T and k=card R. At scale X_n=exp(2 pi N_n/d), select in each
window (r X_n,(1+eta_n)r X_n] actual primes of inverse-square-root mass tending
to s. Choose eta_n decreasing to zero and below 1/(max R+1), so the windows
are disjoint. The prime-window supply theorem permits N_n>=n+1 for every n.
Each window has cardinality ceil(s sqrt(r X_n)); its square-weight mass tends
to zero. Thus the actual helper Euler product differs pointwise by o(1) from

exp(-s sum_{r in R} exp(-it(log X_n+log r))).

Both products have a common global bound, independent of n, from their
bounded total inverse-square-root mass. Their squared moduli therefore have
the same integrals against each of the finitely many integrable signed tests.

The model squared modulus is exp(-2s sum_{r in R} cos(theta+t log r)), with
theta=t log X_n. If any target cos(t log p)<=0, the pair r=1,p contributes at
least -sqrt(2), and each other term at least -1. The whole exponent is then
at most 2s(k-2+sqrt(2)). On a sufficiently short interval [0,d], every target
cosine is at least 1/2 and every inherited/intermediate weight is uniformly
positive. The periodic gate max(0,-cos(theta)-c) selects phases where the
model is at least exp(2sb) times this gate, with
k-2+sqrt(2)<b<kc<k. Shrink d so phase displacements preserve this inequality.
Because log X_n=2 pi N_n/d, the gate has exactly its fixed positive mean on
[0,d], for every positive N_n. A sufficiently large s makes this positive
contribution exceed every negative contribution, simultaneously for the
finite family of intermediate states and target primes.

Dominated convergence transfers all strict signs to a single actual S_n.
The existing exact release identity and fixed-core energy limits transfer
them to the original finite energies for every sufficiently large integer
cutoff. Finiteness supplies one common threshold for the whole cube.

For higher Boolean differences, the density-normalized single-prime
multiplier is 1-c_p cos(t log p), c_p=2 sqrt(p)/(p+1)>0. Alternating
differences are consequently integrals of products of target cosines times
positive intermediate weights. A negative product contains a negative
factor, so the same phase-gap argument applies without a new analytic input.

No claim about total net helper cost or an exhaustive infinite schedule
follows. Those remain separate from finite sign compatibility.

### Attack and quantifier audit

The existing theorem producing negative mixed curvature beyond every fixed
core does not contradict this statement: its adverse prime pair can depend
on the prepared core, while this theorem fixes the entire finite target
block first and then constructs the preparation. No claim covers all
future primes with a single fixed core. The construction does cover all
vertices and all nonempty faces of the prescribed block, not sampled faces.

Sequential use of the one-prime theorem does not supply this conclusion:
each new preparation changes all earlier spectral weights. A common
phase-selection construction pays the compatibility requirement directly.
The helper budget is chosen before the lower bound on helper primes; the
cutoff threshold follows preparation and is common to every face.

Verdict: SURVIVES PRELIMINARY ATTACK against the available Lean corpus.
External novelty is neither checked nor claimed, as instructed.

## Formalization progress

- Reusable one-prime analytic machinery exposed in `PrimePreparation`;
  original module directly checked without changing its public theorems.
- Finite disjoint prime-cluster synthesis directly checked.
- Common positive selection for arbitrary finite compatible signed tests
  directly checked.
- Exact all-order Boolean spectrum and complete prescribed-cube theorem
  written; direct checks and final audits in progress.

## Work sequence

1. Establish exact corpus frontier and attack candidate statements.
2. Complete a dependency-closed paper proof for a surviving structural claim.
3. Formalize the exact result, wire leaf imports, run direct leaf and axiom
   audits, then formal lint. No full builds or numerical experiments.
4. Evaluate significance honestly; continue if the result fails the target.

Pre-existing modified files include the frontier map and unrelated native
theta modules. Preserve their changes.
