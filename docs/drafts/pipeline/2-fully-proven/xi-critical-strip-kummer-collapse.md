# Test analytic critical-strip collapse of the global marked Kummer tower

- **ID:** RH-XCSKC-20261007
- **Stage:** 2-fully-proven; selected exact source claims formalised and audited
- **Parents:** `../2-fully-proven/xi-signed-factor-divisor-independence.md` and
  `../2-fully-proven/xi-legendre-complete-halving-criterion.md`
- **Objective:** distinguish the proved global division classes from their actual
  behavior over the analytic domain containing the nontrivial zeros.

## Competing conjectures and exact target

Global square classes could survive analytic restriction, partly collapse, or all
signed-factor classes could become units with analytic roots on the critical strip.
The selected conjecture is the last. On U={s:0<Re(s)<1}, prove each
F_n=1-n^(-s)xi(s) and lambda_n=1+n^(-s)xi(s) has a nonvanishing analytic square
root. After extending scalars to the meromorphic field of U, all marked radicands
xi*F_n should therefore have the single class xi. Their finite joint marked algebra
should split into 2^(|S|-1) copies of the common quadratic extension for nonempty S,
provided the surviving Xi class is proved nonsquare on U.

After choosing any such marked component, both the original and translated
sections should have halves: Xi becomes square by dividing a marked root by the
analytic root of F_n, and every lambda_n is already square. Thus the proved global
independence would be carried by divisors outside the RH strip. This is a precise
base-change classification to test, not an RH proof or a claim that global results
were false.

## Initial paper mechanism (historical conjecture wording)

The newly checked exact positive-kernel formula gives |xi(s)|<=xi(Re(s)).
For 0<=t<=1, convexity of the real exponential gives pointwise
exp((t-1/2)x)<=(1-t)exp(-x/2)+t exp(x/2).
Integrate against the positive Riemann kernel. Endpoint values xi(0)=xi(1)=1/2
would imply |xi(s)|<=1/2 on the closed strip. For n>=2, |n^(-s)|<=1 there,
so both signed factors have real part at least 1/2. Their images lie in the right
half-plane, where a single analytic square-root branch exists and never vanishes.

Consequently all marked radicands have the same square class after analytic
base change. A previously proved odd-order Xi zero, together with its location in
U, should certify that this class remains nonzero before adjoining a marked root.
Finite multiquadratic algebras then split exactly as above. This requires a genuine
analytic function field and scalar-extension construction; a local germ field or
an unexplained completion cannot substitute for either.

On such a component write v^2=xi and w_n^2=F_n, with w_n chosen already over U.
Then u_n=v*w_n and U_n=w_n+i*beta_n*v has inverse w_n-i*beta_n*v.
The component deck involution v->-v acts by U_n->U_n^(-1), whereas the previously
studied extra global common-root involution negates both v and w_n and sends
U_n->-U_n. This distinction may identify the surviving normal/phase data once
all global halving obstructions collapse. It is also unproved here.

## Initial evidence and limits

A documented deep corpus search is running. Exhaustive direct-bound-name search
found `DeBruijnNegativeTimeDirichletModel.norm_xi_le_of_re`, a coarser kernel bound
on [-3/2,5/2], and the new `norm_xi_le_real_axis`; no sharp strip bound has yet been
identified. The source already has an even positive superexponential Riemann kernel.
Need audit actual integrability, branch APIs, analytic-domain field construction,
and odd-zero location before any implementation or result claim.

The only size bound here certifies where a source divisor is absent. It does not
exclude Xi zeros or provide an estimate-based RH route. The research target is the
geometric base-change boundary and the positive normal/phase data surviving it.

- [x] Complete initial corpus and external parent audit; novelty not certified.
- [x] Prove sharp closed-strip bound and analytic roots of both signed factors.
- [x] Construct the actual analytic-domain field restriction and common class.
- [x] Construct the actual infinite marked embedding and quadratic compositum;
  prove actual halving for every original and translated source section there.
- [x] Prove literal finite tensor-product splitting into quadratic components;
  final actual-source and public axiom audits pass.
- [x] Audit the two distinct involution actions and surviving prime-labelled data.

## External parent audit and hostile verdict

[Lagarias–Montague, The Integral of the Riemann xi-Function](https://arxiv.org/pdf/1106.4348),
Lemma 3.1 and its cited classical kernel ancestry, supplies the known cosine-kernel
parent. [DLMF 25.4](https://dlmf.nist.gov/25.4) fixes the normalization and reflection.
[Stacks Lemma 10.143.4](https://stacks.math.columbia.edu/tag/00U3) supplies the finite
etale algebra/product-of-separable-fields parent. None states this source's
analytic base-change classification; none establishes its novelty either.
The initial deep corpus search was partial despite full inventory coverage.
Exact source searches locate the required positive kernel, global signed-factor
independence, odd Xi zero, and unconditional location of every Xi zero in U.
`Bottcher/MeromorphicField` supplies analytic fraction fields and restrictions;
`HTGeometry/MeromorphicPlaneField` supplies the actual global meromorphic carrier.
The scalar-extension bridge between those representations still requires proof.

Verdict: **BRIDGE**. Analytic unit roots and finite etale splitting are classical.
The useful falsifiable source statement is total collapse of the extra global
classes on the actual RH domain, not a new general Kummer principle. The result
would forbid reading global nondivisibility as a local RH obstruction.

## Dependency-closed paper proof of the exact classification

Kernel integrability follows from its proved superexponential decay, for every
real exponential weight. Convexity bounds the weight for 0<=t<=1 by its endpoint
chord. Positivity permits integration. The endpoint integrals are xi(0)=xi(1)=1/2,
so xi(t)<=1/2. The existing absolute-value integral inequality then gives
|xi(s)|<=1/2 throughout the closed strip. If n>=2 there, |exp(-s log n)|<=1.
Both 1 plus and 1 minus this product have real part >=1/2. Define their roots by
exp(log(f(s))/2), using the principal logarithm on the right half-plane.
These are analytic and nonzero on U and square to f; no choice of local germs is
substituted for a single branch on U.

Let K=M(C), A=M(U), with restriction K->A. The identity theorem makes restriction
injective. Choose an odd-order Xi zero from GlobalParityWall; BornTemperatureFactorType
places it in U. An A-square would have even meromorphic order at that point,
contradicting its odd analytic order. Thus Xi remains nonsquare in A.

For any nonempty finite set S of actual distinct labels n>=2, global independence
of Xi and the F_n implies independence of Xi*F_n: every nonempty packet equals a
power of Xi times a nonempty F packet and is nonsquare. The finite marked field
K_S therefore has degree 2^|S|, and is presented by the independent quadratic
equations u_n^2=Xi*F_n. Tensoring that presentation with A and dividing each u_n
by its nonzero analytic root w_n gives equations v_n^2=Xi. The first equation
defines the genuine quadratic field B=A(v). Every subsequent equation factors
over B as (X-v)(X+v), with coprime factors since characteristic is zero and v!=0.
Repeated Chinese remaindering yields A tensor_K K_S isomorphic to
the product of 2^(|S|-1) copies of B. This is an algebra statement; tensoring a
field does not in general remain a field. Infinite finite-stage components
are compatible sign choices relative to one label; no finite count is asserted
for the infinite tensor product.

On every finite component, mapped source P_n and Q_n satisfy the already proved
halving criteria once their marked coordinates are present. Xi is a square in B
and every lambda_n is already an A-square, so both have actual halves. For all
labels choose the compatible marked embedding into B using u_n=v*w_n; its
injectivity follows from being a nonzero field homomorphism. All other compatible
sign choices give the same halving conclusion. Constructing this embedding, not
assuming an arbitrary algebra structure, is part of the formal target.

Finally U_n=w_n+i*beta_n*v has inverse w_n-i*beta_n*v because
w_n^2+beta_n^2*v^2=F_n+d_n=1. The B/A involution fixes w_n,beta_n,i and negates v,
so sends U_n to its inverse. The separate global extension over the infinite
marked field fixes u_n and negates v, hence also w_n=u_n/v, so sends U_n to -U_n.
These are different base fields and different involutions; no contradiction
or unproved descent identification is hidden in the distinction.

### First analytic check passes

The sharp closed-strip bound and explicit analytic nonvanishing roots pass a
scratch Lean check without diagnostics. Promoted `XiCriticalStripFactorRoots`
and wired its import; targeted build and final direct source audit remain pending.
The proof actually establishes the factor claims for n>=1, because log(n)>=0
is the only label condition needed. This strengthening has the same closed paper
proof; it does not assert any corresponding stronger global independence theorem.

The actual-domain meromorphic carrier and faithful restriction from M(C) are in
scratch validation. The focused deep search was partial with coverage still
pending; useful hits confirmed existing fraction-field restriction and codiscrete
equality tools, not an existing all-meromorphic domain carrier. All retrieved
applicability claims are checked against source and Lean rather than assumed.

### Genuine domain field checked in scratch

`MeromorphicDomainField` passes scratch without diagnostics and is promoted and
wired. It represents all meromorphic functions on a nonempty connected open
domain using equality near every point, proves its field structure, constructs
faithful restriction from the actual `MeromorphicPlane`, and proves analytic
removability of meromorphic square roots of analytic functions. This avoids
asserting an unproved identification between the existing fraction carrier and
all meromorphic functions. The actual strip square/nonsquare application is
prepared next; no tensor-product splitting theorem is yet formalised.

### Source square-class collapse checked in scratch

`XiCriticalStripField` passes scratch without diagnostics and is promoted/wired.
It defines the actual StripField over the global base, proves Xi nonsquare there,
proves every signed factor with n>=1 square, and proves every marked radicand
nonsquare while the product of any two marked radicands is square. The odd-zero
argument uses the unconditional existing open-strip location, not RH.
Both prerequisite targeted builds pass. Targeted source build and the prepared
actual infinite marked-field embedding/common quadratic compositum are queued.

### Component construction and scalar compatibility audit

All three promoted leaves now have passing targeted builds. The fourth scratch
constructs the embedding of the actual global algebraic closure into the analytic
closure, proves every marked generator lands in StripField(sqrt(Xi)), and hence
embeds the whole infinite marked field there. It also proves that adjoining its
image over StripField gives the entire quadratic field: the image of root_0,
divided by the already square factor_2, supplies sqrt(Xi). This is the actual
compositum, not an assumed field extension or a tensor product silently treated
as a field. Its point-halving consequences are being checked against the existing
actual source-extension criteria.

Initial scratch errors were scalar-tower rewrite ambiguity/direction and an
`omega` proof-term mismatch under the broad local classical DecidableEq instance
used for affine Point compatibility. Explicit tower parameters and elementary
Nat inequalities replace those proof terms; no axiom or resource limit changes.
The component check is rerunning. Final source and public axiom audits are pending.

### Actual infinite marked component passes scratch

The corrected fourth scratch passes without diagnostics. Promoted and wired
`XiCriticalStripMarkedComponent`: an actual K-algebra embedding of the whole
Marked field into StripField(sqrt(Xi)); exact equality of its analytic compositum
with that quadratic field; degree two; and actual halves of every original and
translated source section. The affine Point compatibility instance is narrowed
to the component field in the promoted source, avoiding an unrelated override
of Nat equality. Its targeted build and all four final direct-source checks are
running, followed by axiom audits of 53 named public declarations (generated
structure projections/anonymous instances excluded from that count).

The literal finite tensor-product splitting remains a separate unformalised
paper theorem. The compositum theorem is not silently substituted for it.
Next task: obtain finite etale components, show each is the common quadratic
field using the source generators, then count components from exact finrank.
The two deck actions and the surviving normal/phase data remain to be audited.

### Four-module final verification

All four targeted builds pass. Final `lake env lean` checks of each actual source
pass with empty diagnostic logs. All 53 named public declarations pass individual
`#print axioms` audits: only `propext`, `Classical.choice`, and `Quot.sound` occur.
The audit count excludes compiler-generated structure projections and anonymous
instance names; the instances are dependencies of the checked source theorems.
Imports are wired. Index/lint are running; no global lint PASS is claimed.
Owned obsolete implementation scratches were removed after these final checks.
Authoritative source/axiom logs remain under `/tmp/rh-*20261007.log` and
`/tmp/rh-xi-strip-axioms.log`.

Anti-theatre assessment: **BRIDGE**, no certified novelty and no RH zero-location
premise discharged. A real uncertainty in this route is resolved: independent
global division classes cannot be read as obstructions on the analytic RH strip.
The whole infinite marked field, rather than only each finite label, is covered.
Classical analytic and field-theoretic mechanisms account for the proof. The
next hard obligation is the literal finite scalar-extension algebra, followed
by the surviving normal/phase comparison; work was not deferred for difficulty.
Two small quadratic-field identification helpers are prepared for that finite
splitting proof and remain scratch-only until checked and source-instantiated.

Index passes. The final lint snapshot fails on twelve unrelated unwired leaves:
RHTower/AbsolutelyConvergentZetaSignRigidity, LeeYangPrimeStabilityNoGo,
LeeYangRestrictionZeroCount, ZetaTwistedFirstMomentUniform;
HTGeometry/ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, PolydiskRadialLogarithm,
PolynomialSegmentArgument, TernaryLatticeCubic. No error names any of these four
owned modules. This is not a global lint PASS. Logs:
`/tmp/rh-xi-strip-{index,lint}-20261007.log`.

### Finite tensor splitting implementation checkpoint

`QuadraticRootFieldEquiv` passes scratch and targeted build; promoted/wired.
`CommonQuadraticGenerators` passes scratch; promoted/wired, target build running.
These identify a field generated by nonempty scaled roots of a common nonsquare
with the exact quadratic root field. The prepared `EtaleCommonQuadratic` scratch
applies the classical finite etale decomposition, proves the identification on
every component using all generators, combines the component equivalences, and
counts copies from finrank. No component is sampled.

Prepared source scratch `/tmp/rh-xi-strip-finite-tensor.lean` defines the actual
finite marked intermediate field, proves its degree from the previously audited
independent radicands, forms the literal StripField tensor product, exhibits its
scaled-root algebra generators, and targets an algebra equivalence to
2^(|T|-1) copies of stripQuadraticField for every nonempty finite T. These latter
scratch claims are unverified until the generic leaf builds. This implements
the existing dependency-closed paper argument; it adds no source assumption.

### Exact deck-action audit and implementation plan

All three finite-splitting helpers now pass their targeted builds. The literal
source tensor scratch is resolving a Lean scalar-map instance elaboration
mismatch; the defining tensor relation is used directly instead. No mathematical
claim or algebra structure is weakened. Final source checks remain pending.

The focused corpus search for quadratic conjugation/norm-one marked units is
nonpartial with complete file inventory (68,098 files), but compiler coverage has
pending/stale entries. It locates `quadConj_involutive`, `quadConj_root`, and the
existing quadratic-tower automorphisms, not a stronger source strip theorem.
The exact primary parent is [Milne, Fields and Galois Theory](https://www.jmilne.org/math/CourseNotes/FT.pdf),
Example 5.24 and Corollary 5.25: quadratic norm and cyclic norm-one units. The
deck-action distinction remains **BRIDGE**, not a new norm principle.

For the actual chosen marked embedding, set w_n=image(u_n)/v rather than silently
identifying it with the canonical analytic branch. Its square is F_n. Since F_n
is already square in A, any of its roots in B lies in A (the two roots differ only
by sign). Thus the B/A involution fixes this exact w_n and negates every image(u_n).
It follows on the actual source unit square root U_n=w_n+i*beta_n*v that
U_n^2=image(1-2*d_n+2*i*y_n) and sigma(U_n)=U_n^(-1). The reciprocal identity
uses (w_n+i*beta_n*v)(w_n-i*beta_n*v)=F_n+d_n=1.
Over the separate global common-halving field, the Marked-linear involution fixes
u_n,i,beta_n and negates v, so w_n and U_n both negate. Squaring fixes the original
unit, as required. These calculations close the exact source-action proof before
Lean implementation. Source unit-root identities and the conjugation wrapper
are being prepared in scratch; none is yet claimed checked.

### Literal finite splitting and source unit-root checks pass

`XiCriticalStripFiniteTensor` and `QuadraticRootConjugation` pass scratch and their
targeted builds. Both are promoted and wired. The source relation elaborates
cleanly as a literal tensor; the generic finite-etale theorem consumes it via the
proved canonical scalar-map formula. No local instance replacement or elaborator
resource setting was needed. The main theorem is the actual algebra equivalence
and exact component count, not only a dimension equality.

`XiKummerUnitRoots` also passes scratch with no diagnostics, is promoted/wired,
and is in targeted build. It gives the exact source U_n square and reciprocal
identities in every extension containing the Xi root. The actual global and
analytic deck actions are now prepared in a dependent scratch. Final direct
source checks and named public axiom audits of these new leaves remain pending.

### Both actual deck actions pass scratch; exact surviving coefficient

`XiKummerDeckActions` passes scratch with no diagnostics. It constructs both
actual quadratic involutions, proves that the strip action fixes the exact
factor roots determined by the chosen marked embedding, negates every marked
root, and inverts the unit roots and original unit representatives. The global
Marked-linear action negates the unit roots. A local explicit inherited Module
instance resolves an expensive typeclass search; no heartbeat change was used.
The leaf is promoted/wired and in targeted build.

The positive coefficient statement now has a dependency-closed paper proof:
U_n-sigma(U_n)=2*i*beta_n*v, by the reciprocal identity already checked. Since
2, i, v are nonzero, division recovers beta_n exactly. Taking ratios recovers
beta_n/beta_m, independent of all factor-root branch signs and the common root.
The recovered function is the original entire exponential beta_n, so its
analytic continuation across the branch divisor is explicit. This does not
assert that v is a uniformizer at a multiple Xi zero, or supply a real-form
condition on the coefficient. The scalar size/phase of beta_n at zeros remains
an open RH receiver input. Exact algebraic recovery is being formalised next.

### Eight-leaf final audit started

`XiStripPrimeCoefficients` passes scratch after explicit final cancellation,
is promoted/wired, and its targeted build is followed by all eight actual-source
checks and 54 named public axiom audits. This cycle comprises the four generic
algebra helpers, literal finite tensor theorem, source unit roots, exact deck
actions, and prime-coefficient recovery. The earlier four leaves and their 53
named declarations already passed final audits and are not rechecked.

Index passes. Current authoritative lint fails only on seven unrelated unwired
leaves: RHTower/ZetaLineTwistedSeriesMoment, ZetaSquareMobiusDetilting;
HTGeometry/ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No owned-cycle module is
named. No global lint PASS is claimed. Logs:
`/tmp/rh-strip-classification-{index,lint}-20261007.log`.

The subsequent source descent work is now closed in
`../5-failed/xi-marked-reflection-descent.md`: the one-sided lift fails, and its
minimal paired reflection completion is formalised and audited.

## Final selected-source verification and boundary

All eight new leaves pass targeted builds and final `lake env lean` checks of
their actual source paths, with empty diagnostic logs. All 54 named public
declarations pass individual axiom audits using only `propext`, `Classical.choice`,
and `Quot.sound`. Combined with the previously audited four leaves, this cycle
has 12 leaves and 107 named public declarations. Generated declarations and
anonymous instances are not included in that count; checked theorems include
their actual dependencies. The eight-leaf audit files are
`/tmp/rh-strip-finite-{axioms.lean,axioms.log,audit-names.txt,audit-check.py}`;
direct-source logs are `/tmp/rh-<Leaf>-final-20261007.log`.

The formal source claims are the analytic unit roots, actual-domain restriction,
Xi nonsquareness, actual infinite marked embedding and exact quadratic compositum,
actual source halves there, literal finite tensor equivalence and component count,
both exact source involutions, and recovery of every prime coefficient and ratio.
The paper's universal wording about all compatible sign choices remains a paper
corollary of the source halving criteria rather than a separately exported Lean
theorem. This card therefore remains at fully-proven rather than claiming every
paper quantifier has a dedicated formal wrapper. No geometric normal-bundle or
simple-zero assumption is added.

Index passes; the seven unrelated lint errors above remain the final snapshot
for these leaves. No global lint PASS is claimed. Obsolete owned implementation
and API scratches are removed after the final checks; audit evidence is retained.

Final verdict: **BRIDGE**. Classical analytic roots and Kummer theory explain the
mechanism. No scientific novelty is certified, and no RH zero-location premise
is discharged. The useful boundary is exact: global independent division classes
collapse on the RH strip, yet their prime-labelled odd coefficients survive.
Their real-form constraint remains open. The exact descent boundary is recorded in
`../5-failed/xi-marked-reflection-descent.md`, including the formalised positive
paired completion, exact degrees and unchanged strip compositum.
