# Functional-equation descent of the actual global marked tower

- **ID:** RH-XMRD-20261007
- **Stage:** 5-failed for the one-sided lift; positive completion formalised and audited
- **Type:** closed no-go with exact positive completion; classical BRIDGE
- **Parent:** ../2-fully-proven/xi-critical-strip-kummer-collapse.md
- **Statement:** the actual one-sided global marked tower admits no lift of
  functional-equation reflection; its smallest reflection-stable completion
  doubles the independent label classes.

## Exact competing conjectures

Let K=M(C), tau(s)=1-s, R(f)=f composed with tau, and
F_n(s)=1-exp(-s log n)*Xi(s), for integer n>=2. The actual field Marked is
generated over K by u_n^2=Xi*F_n. Test:

1. The Xi functional equation lifts to a ring automorphism of Marked extending R.
2. No ring homomorphism Marked->Marked extends R, because every reflected
   radicand Xi*F_n(1-s) remains nonsquare in Marked.

The second conjecture has the paper mechanism below. It is not an RH assumption:
it concerns divisors outside the critical strip where the extra classes live.
This is holomorphic functional-equation reflection. No antiholomorphic lift
claim is silently substituted for it.

## Corpus and external audit

The first focused hybrid search was partial despite complete file inventory and
returned no candidates. Broader lexical search plus direct source reads located
`MeromorphicReflection` and `MeromorphicReflectionTransport`, constructing
reflection on the analytic fraction-field carrier. They do not provide reflection
on the actual all-meromorphic `MeromorphicPlane` carrier. The Kummer-labelled
RouteR reflection theorem concerns a different landing, not this marked field.
The existing `XiSignedFactorSquareClasses` gives independent original signed
classes, while `not_isSquare_markedExtension_of_twists` tests every finite twist
in the actual infinite tower.

[Milne, Fields and Galois Theory](https://www.jmilne.org/math/CourseNotes/FT.pdf),
Kummer theory, gives the parent classification by subgroups of square classes.
Thus stability of a radical field under a base automorphism requires stability
of its square-class subgroup. This is a classical mechanism, not a novelty claim.
The exact source boundary and strongest completion statement still need audit.
Provisional verdict: **BRIDGE**; no scientific novelty certified.

## Paper mechanism and positive completion

Reflection is an involutive automorphism of K by meromorphic composition and the
identity theorem. It fixes Xi by its functional equation. Write
G_n=F_n composed with tau=1-exp((s-1)log n)*Xi(s).

An original factor F_m and reflected factor G_n cannot share a zero. If they did,
Xi(s)=exp(s log m)=exp((1-s)log n), and equality of absolute values would force
Re(s)=log n/(log m+log n), strictly between zero and one. The already proved
strip bound gives |Xi(s)|<=1/2 there, whereas |exp(s log m)|>1. Contradiction.
Distinct reflected factors have disjoint divisors by reflecting the existing
original-factor separation. Every reflected factor has an odd zero: reflection
preserves nonsquareness, and the existing entire-square criterion supplies an
odd zero. Xi is nonzero at every such factor zero.

Take any nonempty finite reflected packet and choose an odd zero of one factor.
Every other reflected factor, every original factor, and Xi is nonzero there.
The packet times any Xi power and original packet has odd order, hence is not a
meromorphic square. If the reflected packet is empty, the existing original
independence theorem applies. Consequently Xi and all F_n,G_n are independent
modulo squares. In particular Xi*G_n remains nonsquare after adjoining every
sqrt(Xi*F_m): any hypothetical root lies at a finite stage, where the exact
Kummer twist criterion contradicts the packet statement. Applying a putative
lift to u_n^2=Xi*F_n would give such a root. Thus conjecture 1 fails if these
source steps check.

The positive survivor is stronger than the absence of a lift. Adjoin, in the
same algebraic closure, all v_n^2=Xi*G_n. The paired radicands are independent,
so a finite set S of labels generates degree 2^(2*|S|), and relative degree
2^|S| over its one-sided field. The two infinite one-sided fields intersect
exactly in K: finite-stage Kummer monomial bases for the disjoint independent
families have only the constant monomial in common. Their joint field has an
involutive semilinear automorphism R(a), u_n<->v_n. Define it on each finite
monomial basis; multiplication respects the paired quadratic relations, these
maps agree under inclusion, and their squares are identity. Any extension of
the original field carrying a lift must contain the reflected roots, so this
is its smallest such completion, up to the prescribed K-embedding. Over the
analytic strip, both sets of extra factors are already squares; the completion
has the same common quadratic compositum A(sqrt(Xi)).

## Remaining obligations

The involution has a shorter alternative construction. Reflection preserves the
actual strip domain and fixes Xi. It therefore lifts to the already constructed
quadratic strip field while fixing its chosen square root of Xi: apply
`AdjoinRoot.mapRingEquiv` to the invariant polynomial X^2-Xi and transport through
the quadratic root-field equivalence. The lift squares to identity on both base
and generator. The embedded paired global field is stable because each radical
is carried to a root of its partner's radicand, hence to either sign of the
chosen partner. Restrict and transport the involution to the actual global
paired field. Choosing each reflected root as the image of its original root
gives exact swaps without changing the generated field. This also connects the
global completion directly to its common analytic strip component. The argument
is classical quadratic descent; it adds no RH location premise or novelty claim.

- [x] Complete exact source/parent hostile audit; distinguish formal claims from
  the paper mechanism above.
- [x] Construct R on actual MeromorphicPlane and prove its source formulas.
- [x] Prove the complete mixed packet criterion and no-lift result.
- [x] Formalise the positive paired completion, exact degrees, intersection,
  involution and minimality. Do not retire the no-go before its survivor closes.

## No-go closure

- **Killing mechanism:** an original radicand is carried to a square class absent
  from the whole original tower; exact source theorem passes Lean and targeted build.
- **Positive survivor:** smallest paired reflection completion with exact rank,
  trivial intersection of the two one-sided fields, and an involutive lift.
- **Insight:** global functional-equation descent needs both orientations of
  the marked family, even though their analytic strip components coincide.
- **Status:** all twelve source leaves pass targeted builds and final direct
  actual-source checks. All 99 named public declarations pass the standard-only
  axiom audit. The positive survivor is fully formalised: every nested finite
  packet has relative degree 2^(cardinality difference), the two infinite
  orientations intersect in the base, and the paired field has an involutive
  reflection with normalized root swaps. Minimality is proved among intermediate
  fields of the same fixed global algebraic closure, even against fields carrying
  only a ring-homomorphism lift. Its analytic strip compositum remains quadratic.

## Log

- 2026-10-07 — Exact next descent conjecture recorded while finishing the prior
  strip deck-action audits. No RH zero-location premise discharged.
- A second partial hybrid search for prescribed radical signs locates the
  existing quadratic tower machinery. Direct verification found
  `exists_algEquiv_neg_index` in QuadraticTowerSquareClasses: every individual
  finite independent root sign flip exists. These flips can correct any
  semilinear lift's square on the paired completion. Actual-carrier reflection
  and source factor-separation scratches are prepared; neither is promoted.
- Exact finite-packet implementation will use the already proved odd-divisor
  obstruction: isolate one odd factor, multiply by the remaining entire factors
  and any Xi power, all nonzero at that point. Finite product compatibility of
  `ofMeromorphic` transports that actual analytic product to the global field.
  This is the same complete paper proof above, organised to avoid duplicating
  product/representative bookkeeping for each orientation.
- The source separation leaf now passes scratch and targeted build. The generic
  finite-packet helper is resolving explicit differentiation/representation
  arguments; no mathematical premise or resource limit changes.
- Prepared source packet/no-lift and paired-radical degree scratches. The positive
  intersection proof is sharpened to finite linear disjointness from exact degree
  multiplication, then extraction of finite label supports for every element of
  an arbitrary adjoin. A nonpartial corpus search found the precise mathlib
  `LinearDisjoint.of_finrank_sup` and `inf_eq_bot` parents; no new general field
  intersection principle is claimed. All these downstream scratches are unverified.
- Final source construction now passes scratch. A dependent adjoin induction
  caused a Lean elaboration timeout; the proof was replaced by subfield closure:
  pull back the embedded field through reflection, push that subfield to the
  original algebraic closure, and use closure on the base and every generator.
  No heartbeat limit was changed. All twelve leaves are wired. The external
  all-public audit manifest contains 99 named declarations; generated declarations
  are excluded from that count, and transitive axiom closure is checked.
- Final completion targeted build passed. The guarded all-public audit passed
  for all 99 names, using only `propext`, `Classical.choice`, and `Quot.sound`.
  Direct checks of the twelve actual source files are still running in chain
  35844; global lint and cleanup remain pending.

## Final formal audit

All twelve leaves are wired exactly once. Every targeted build and every final
`lake env lean` invocation on the actual source files passed. The twelve final
logs are empty. The separate `/tmp` axiom audit checked all 99 named public
declarations and their transitive dependencies: only `propext`, `Classical.choice`,
and `Quot.sound`. Generated declarations are excluded from the stated count.

The leaves are `MeromorphicPlaneReflection`, `EntireOddFactorPackets`,
`IndependentRadicalIntersections`, `MeromorphicDomainReflection`,
`QuadraticSemilinearInvolution`, `InvariantFieldEmbedding`,
`XiReflectedFactorSeparation`, `XiReflectedSquareClasses`,
`XiPairedRadicalDegrees`, `XiPairedFieldIntersection`, `XiStripReflection`, and
`XiPairedReflectionCompletion`, in their HTGeometry/RHTower theorem areas.

Indexes were refreshed. The authoritative repository lint gate fails on six
unrelated unwired HTGeometry leaves: `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`, and `LabeledCosineDescent`. No new-cycle leaf is
named. This is not a global lint pass. Evidence is retained in
`/tmp/rh-reflection-{axioms,index-20261007,lint-20261007}.log` and the twelve
`/tmp/rh-<Leaf>-reflection-final-20261007.log` files.

Twelve obsolete proof scratches were removed after comparison with the audited
sources; the only differences were three reviewed module documentation headers.
No full or umbrella build, numerical research computation, admission, added axiom,
heartbeat increase, commit, or push was used.

The failed route is specifically functional-equation descent on the original
one-sided marked field. The paired completion survives with the exact laws above.
It does not establish componentwise real descent or locate Xi zeros. The full
RH goal remains open and active.
