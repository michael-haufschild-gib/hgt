# Polynomial left factors of the actual marked Xi source

- **ID:** RH-XIPLF-20261007
- **Stage:** 3-formalized; seven actual-source checks and nineteen public axiom audits passed
- **Parent:** `../1-in-progress/xi-marked-joint-monodromy.md`
- **Predecessor:** `../3-formalized/xi-joint-cubic-galois.md` (ten modules and all 59 public axioms audited)
- **Verdict:** BRIDGE; novelty not certified

## Exact competing conjectures

For every real a, put d_a(s)=xi(s) exp(-a*s). If P is a complex polynomial
and h is entire with P(h(s))=d_a(s) for every s, then P has degree one.
The initial one-distinct-root conjecture was strengthened after the corpus
audit located an unconditional simple-zero provider. No simple-zero premise
is assumed. Independently, every nonzero value of d_a occurs on every
half-plane Re(s)>R, R>=1.

Competing possibility: a polynomial with two distinct zero-fiber points admits
an entire lift, assigning those fibers to opposite ends of the critical strip.
This is the next obstruction to attack after the finite joint cubic quotient.
No claim about all finite covers or the full fundamental-group image follows
until the corresponding covering and descent steps are proved.

## Corpus and primary evidence

Deep query completed with partial=true and complete inventory 68177, but large
pending/stale compiler coverage. Candidate lemmas and source arguments were
inspected. No ready two-value directional-separation theorem was accepted.
Evidence: `/tmp/rh-xi-two-value-strip-search-20261007.json`.
Exact text search for Biernacki/separated zeros found no named theorem in the
Lean corpus. Existing actual cubic growth and strip-separation leaves supply
the narrower predecessor mechanism; generic polynomial transport needs audit.

[Bergweiler--Eremenko, 2020](https://link.springer.com/article/10.1007/s40315-020-00349-2),
Theorem A, states Biernacki's exclusion of finite-order transcendental entire
functions whose zeros and one-points accumulate in distinct single directions.
Theorem 1.1 supplies a sector version. The paper and its
[arXiv record](https://arxiv.org/abs/2002.00376) were opened.
This is a classical parent theorem, not a new theorem claimed here.

[Garunkstis, 2021](https://inmabb.criba.edu.ar/revuma/pdf/v62n1/v62n1a14.pdf),
Lemma 1.3, proves the analogous one-distinct-root property for the compact
Selberg zeta function by a different value-distribution argument. The same
paper cites Liao--Yang for primeness of Riemann zeta. Neither statement has
yet been verified as applying to completed, exponentially tilted Xi. Audit
the cited ancestry before any novelty claim.

## Proposed proof mechanism, still under dependency audit

1. Polynomial inversion bounds give h order at most one, while actual Xi
   growth on the positive real ray forces log|h(x)-b|/x to be unbounded for
   every fixed b. Finite-zero Hadamard rigidity then makes every b-fiber infinite.
2. If b is a root of P, every h=b point is an actual Xi zero, hence lies in the
   bounded-width critical strip. Actual d_a tends uniformly to zero on both
   strip tails. Small polynomial sublevel sets separate into neighborhoods of
   the finitely many roots of P. Connectedness forces h to choose one such
   neighborhood on each tail.
3. Infinitely many points in each root fiber and discreteness on compact sets
   leave at most two roots of P. If two remain, each fiber lies, apart from
   finitely many points, in a different vertical tail. Normalize those roots
   to 0 and 1. Their preimages then accumulate in the two opposite vertical
   directions, contrary to Biernacki's theorem.
4. Complex polynomial factorization gives P=c*(X-b)^m.

**SUPERSEDED MECHANISM:** the directional-separation proof above remains a valid
candidate, but the following half-plane argument removes its finite-order,
strip-tail and zero-fiber dependencies. No Biernacki formalization is needed
for this target.
The broad conjecture that arbitrary two fibers confined to one strip force
finite exponential type is not needed and is not being asserted.

## Dependency-closed paper proof via the modular covering

### Quantitative analytic input

An analytic function f on Re(s)>1 omitting 0 and 1 satisfies
|f(x)| <= exp(C*x) for x>=2, with C depending on f. Here is a proof using
the existing modular covering, without assuming Schottky as a new premise.

1. Pull back f by s=1+(1+z)/(1-z) to the unit disk and lift through the
   modular covering: f(s(z))=lambda(tau(z)), tau=i(1+g)/(1-g), |g|<1.
   The corpus proves existence and holomorphy of this lift.
2. Put a=|g(0)|<1 and r=|z|. Schwarz--Pick gives
   1-|g(z)|^2 >= (1-r^2)*(1-a)^2=:D.
   With y=Im(tau), the Cayley formula and triangle inequality give
   max(y,1/y) <= (1+|g|)/(1-|g|) <= 4/D.
3. Send tau into the SL(2,Z) fundamental domain, obtaining w. Its height
   Y satisfies Y>=sqrt(3)/2>4/5 and Y<=max(y,1/y). Indeed
   Y=y/|c*tau+d|^2; if c=0, d=+/-1, and otherwise |c|>=1.
4. For Y>=4/5 put q=exp(-pi*Y)<1/4. The theta series give
   1/3 <= |thetaThree(w)|, |thetaFour(w)| <= 5/3, and
   1/3 <= |exp(-pi*i*w/4)*thetaTwo(w)| <= 11/3.
   For the last estimate subtract the two leading terms; bound the rest
   by the two-sided geometric sum 1+2q/(1-q)<=5/3. Thus lambda(w),
   1-lambda(w), and their inverses have bounds <=K*exp(pi*Y), with one
   absolute K. Each of the six anharmonic transforms is bounded by
   another absolute constant times exp(pi*Y). The modular transformation
   law gives |lambda(tau)|<=K'*exp(pi*max(y,1/y)).
   The ratios lambda/(lambda-1) and (lambda-1)/lambda are bounded using
   1+1/(lambda-1) and 1-1/lambda, avoiding an erroneous doubled exponent.
5. Consequently |f(s(z))|<=K'*exp(C/(1-r)). At x>=2 choose
   z=(x-2)/x in [0,1), so 1/(1-r)=x/2. Absorb K' into exp(C'*x).

Every ingredient has a classical paper proof: theta geometric tails,
SL(2,Z) reduction, the modular covering and Schwarz--Pick. Corpus locations
include `Bottcher/ModularLambdaProperness`, `ModularLambdaOmittingMarty`,
`ModularLambdaCovering`, `DiskSchwarzPick`, and `HTGeometry/ModularDiskChart`.
The new quantitative assembly still needs Lean verification.

### Application to actual Xi

Suppose b!=c are roots of P and P(h)=xi*exp(-a*s). On Re(s)>1 the actual
source is nonzero, so (h-b)/(c-b) omits 0 and 1. The input above makes h(x)
at most exponential. A fixed polynomial in h(x) is also at most exponential.
This contradicts actual Xi's superlinear logarithmic growth on the positive
real ray, which is unchanged by any fixed exponential tilt. Therefore P
has at most one root. It is nonconstant by the same growth contradiction;
the fundamental theorem of algebra supplies a root. Factorization over C
now gives exactly P=c0*(X-b)^m, c0!=0, m>=1.

This argument also exposes the positive survivor: a holomorphic polynomial
lift of a zero-free, superexponentially growing half-plane source can omit
at most one finite value on that half-plane. Perfect-power factors survive;
no conclusion about odd Xi multiplicities or RH has been added.

**Stronger survivor, returned to paper/novelty audit before Lean:** for every
real R>=1 and every w!=0, there exists s with Re(s)>R and
xi(s)*exp(-a*s)=w. Proof: this source already omits 0 there; omitting w would
give the same exponential ray bound and contradict its superlinear growth.
Thus its range on each such half-plane is exactly C minus {0}. This concerns
nonzero a-points, not Xi zeros or their simplicity. It would in particular
put actual marked augmentation zeros arbitrarily far right. Corpus search
for this exact value-surjectivity consequence completed with partial=false
and complete inventory 68186. All 20 candidate lemmas and 20 source arguments
were inspected; none supplied the exact consequence. Compiler freshness
remains incomplete. Primary searches did not establish novelty. The paper
argument is accepted as a classical Schottky consequence; Lean remains open.

### Hostile/ancestry audit

[Jenkins, 1955, Theorem 1](https://doi.org/10.4153/CJM-1955-010-4)
gives the classical disk estimate with growth exponent (1+r)/(1-r).
Its primary PDF was opened and its statement and proof inspected. Our
half-plane consequence is classical; constants are deliberately unoptimized.
The modular proof above supplies the dependency chain needed by this corpus.
No novelty claim is made for Schottky or the polynomial-factor application.
Exact Xi/tilt ancestry remains to be resolved before calling this new science.

Deep Biernacki query: partial=true, complete inventory 68181, no accepted
separation lemma. Reciprocal-zero query: partial=false, complete inventory
68182, no accepted ready first-reciprocal-sum bound. Large pending/stale
compiler coverage persists. Evidence is in the dated `/tmp/rh-*-search-20261007.json`
files. Neither result is treated as exhaustive compiler verification.

## Historical formalization checkpoint (superseded by final audit below)

- `HTGeometry/ModularThetaNormBounds.lean`: four public theta estimates;
  scratch source check and targeted `lake --old build +...` passed.
- `HTGeometry/ModularHeightBounds.lean`: three public modular/Cayley height
  estimates; scratch source check and targeted build passed.
- `HTGeometry/ModularLambdaGrowth.lean`: three public bounds; scratch and
  targeted build passed.
- `HTGeometry/SchottkyDiskGrowth.lean`: disk estimate; scratch and targeted
  build passed.
- `HTGeometry/SchottkyHalfPlaneGrowth.lean`: three half-plane/polynomial
  estimates; scratch and targeted build passed.
- `RHTower/XiTiltRayGrowth.lean`: superlinear growth above any threshold and
  exclusion of every fixed exponential ray bound; scratch and targeted build passed.
- No actual Xi classification or value-surjectivity theorem is yet claimed
  formalized. Umbrella wiring, final source checks, axioms and cleanup remain.

## Stronger degree-one conjecture exposed by the corpus

`RHTower/Zeta23SimpleCriticalDensity.lean` states and proves unconditional
`two_thirds_simpleCritical_epsilon` and
`eventually_pos_xiPosZeroCount_of_zeta23`. Together they supply a simple
critical Xi zero. The stronger existing theorem
`DeletionMixedRefinement.exists_high_simple_critical_xi` in
`RHTower/ArithmeticJointJetExclusion.lean` already supplies such zeros above
every height, so reuse it. All three compiler/axiom probes passed: only
`propext`, `Classical.choice`, `Quot.sound`. Evidence:
`/tmp/rh-xi-simple-zero-api.log`.

**New exact target, through paper and ancestry audit before Lean:** if h is
entire and P(h(s))=xi(s)*exp(-a*s), then P.natDegree=1. Paper proof: the
Schottky argument gives P=c*(X-b)^m. At a simple Xi zero rho, the exponential
factor is a unit, so the source has analytic order one. The composition has
order m*ord_rho(h-b). Thus m=1. Existence of the simple zero is to be derived
from the corpus theorem, not introduced as a premise. This still does not
assert primeness against arbitrary transcendental left factors.

The earlier statement that perfect powers survive describes the Schottky
argument alone. It is not an assertion that the full corpus cannot exclude
them. Dedicated deep query completed partial=false, inventory68189; all
candidate lemmas and source arguments inspected. It surfaced the existing
simple-zero provider. Primary searches have not certified novelty; this
remains a BRIDGE assembly of classical results and actual corpus inputs.

Latest checkpoint: the actual degree-one/nonzero-value assembly is in its
final scratch check. Six supporting leaves are promoted and targeted builds
passed. No live search remains. Nineteen-public-theorem axiom audit is drafted.

## Final audit and exact endpoints

All seven targeted builds and final `lake env lean` checks of actual repository
sources passed. All nineteen public theorem closures contain only `propext`,
`Classical.choice`, `Quot.sound`. Seven imports occur exactly once in their
theorem-area umbrellas. Seven proof scratches were removed after exact source
comparison. No heartbeat changes, admissions, new axioms, or computations.

The three public endpoints in `RHTower/XiPolynomialLeftFactors.lean` are:

- `exists_xi_tilt_eq_of_nonzero`: every nonzero value occurs on Re(s)>R
  for every R>=1 and every real exponential tilt a.
- `xi_polynomial_left_factor_root_unique`: all roots of a polynomial left
  factor coincide.
- `xi_polynomial_left_factor_natDegree_eq_one`: every polynomial left factor
  with an entire right factor has degree exactly one. The actual simple-zero
  provider is proved in the imported corpus, not assumed as a premise.

Evidence: `/tmp/rh-xi-polynomial-left-verification.json`,
`/tmp/rh-xi-polynomial-left-axioms.log`, the seven `/tmp/rh-final-*.log` files,
and `/tmp/rh-xi-polynomial-left-build.log`. Index refresh passed. Global lint
failed only on six unrelated unwired leaves: `R:WeilConeVonMangoldtZetaPencil`
and `H:ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. No own-leaf error;
do not describe the global gate as clean.

## Scientific assessment and continuation

The target removes all nonlinear polynomial left-factor obstructions. It
still supplies no critical-line selection law, arbitrary transcendental
primeness, full fundamental-group image, or RH proof. BRIDGE: formal corpus
frontier advanced, novelty relative to literature not certified. Much effort
formalized classical quantitative Schottky theory; avoid treating this as a
research discovery. No step was deferred for difficulty. Corpus search
preceded proof work and exposed the stronger actual simple-zero input.

Next card: `../2-fully-proven/xi-finite-cover-monodromy.md`. Attack
single-coordinate finite-cover pullback connectedness. Its selected next
increment excludes Laurent outer factors on entire nowhere-zero lifts;
the general compact-curve reduction remains explicitly separate.
