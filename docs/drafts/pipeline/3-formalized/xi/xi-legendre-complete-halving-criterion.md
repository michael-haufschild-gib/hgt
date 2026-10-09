# Complete halving criterion for the actual Xi Legendre sections

- **ID:** RH-XLCHC-20261007
- **Stage:** 3-formalized
- **Parents:** `../2-fully-proven/xi-global-kummer-parity-transport.md`,
  `../2-fully-proven/xi-exponential-translate-square-rigidity.md`, and
  `../2-fully-proven/xi-signed-factor-divisor-independence.md`
- **Objective:** close the sufficiency gap between necessary square coordinates
  and actual halves in the affine elliptic-curve group.

## Exact target and competing alternatives

For every field extension E of the actual infinite marked field, the base-changed
original section P_n has a half iff xiMarked is square in E. The translated
section Q_n has a half iff both xiMarked and lambda_n=1+d_n are square in E.
This is stronger than the existing nondivisibility statements. It tests whether
square-coordinate obstructions are complete or conceal a further obstruction.
No additional analytic hypothesis or comparison premise may be assumed.

The smallest fields containing halves should consequently be M(sqrt(xi)) for
P_n and M(sqrt(xi),sqrt(lambda_n)) for Q_n, with degrees two and four.
For finitely many distinct Q labels, the joint degree should be 2^(|S|+1).
The signed-factor card supplies square-class independence; the present missing
step is actual sufficiency in the point group, followed by precise field objects.

## Corpus and source audit

The documented deep search for Legendre halves and Kummer division fields completed
with full inventory coverage (`partial=false`) but returned irrelevant square-root
and Legendre-symbol hits. Follow-up lexical searches and exhaustive relevant source
text searches found the existing `LegendreDoublingSquare.lean` necessary conditions
and the actual source sections. No existing sufficient halving theorem was identified.
All candidates remain subject to toolchain checks; no retrieved suggestion is an axiom.

Classical parent: [Zarhin, Division by 2 on elliptic curves](https://arxiv.org/abs/1605.09279).
Its explicit three-square-root construction has already been read in this session.
The contribution sought here is its exact application to the actual source field and
sections, not a novelty claim for the classical construction.

## Dependency-closed paper proof

Let E have characteristic zero and let lambda be different from zero and one.
For a point (x,y) on y^2=x(x-1)(x-lambda), assume y is nonzero. Existing doubled
coordinate identities prove that a half forces x and x-1 to be squares.
Conversely choose a^2=x, b^2=x-1; then a,b are nonzero. Set c=-y/(ab).
The curve equation gives c^2=x-lambda and abc=-y.

Put X=(a+b)(a+c), Y=-(a+b)(a+c)(b+c).
Then X-1=(a+b)(b+c), X-lambda=(a+c)(b+c), and
Y^2=X(X-1)(X-lambda). None of a+b, a+c, b+c is zero: their vanishing would
force respectively 1=0, lambda=0, or lambda=1. Hence Y is nonzero and (X,Y)
is nonsingular. Its tangent slope is -(a+b+c). Direct substitution in the
existing affine group formulas gives doubled coordinates (x,y). This proves
actual halving iff the two coordinates x,x-1 are squares.

For P_n, x=d=beta^2*xi and x-1=-F. The source has y^2=dF, with all beta,d,F,y
nonzero and i^2=-1 in the marked field. Thus both coordinates are squares over
E exactly when xi is square: a root of d gives a root i*y/sqrt(d) of -F.
For Q_n, x=lambda/d and x-1=1/d. Their simultaneous squareness is equivalent
to squareness of d and lambda, hence of xi and lambda. Nonsingularity and
lambda distinct from zero and one follow from the already proved source
nonvanishing statements and persist under every field embedding.

## Hostile audit and verification boundary

**SURVIVES PAPER ATTACK.** The signs in Y and abc=-y are essential: the wrong
choice constructs a half of -P. The proof must use the actual affine group law,
not merely verify the cubic equation. All denominators have explicit nonzero
proofs. The criterion deliberately excludes y=0; actual P_n and Q_n satisfy it.
It does not claim a theorem for singular Legendre parameters.

- [x] Paper formulas, competing alternatives, corpus and classical-source audit.
- [x] Verify generic sufficient construction in Lean and actual group doubling.
- [x] State and discharge the two-coordinate iff criterion.
- [x] Instantiate for original and translated sections over arbitrary extensions (scratch PASS; final source audit pending).
- [x] Construct minimal fields and establish their degrees, including every finite joint label set (scratch checks PASS).
- [x] Targeted build, final actual-source checks, axioms, imports, index/lint.

No RH zero-location premise is discharged by this halving criterion. It makes
an existing geometric receiver exact and separates common from label-dependent
division data. No completion or arithmetic normal-cycle comparison is asserted.

### Generic construction checkpoint

`LegendreHalvingCriterion.lean` is promoted and its targeted build passes.
Both `exists_half_of_square_roots` and `exists_half_iff_square_coordinates`
passed a clean scratch check. The proof uses `Point.add_self_of_Y_ne` and verifies
both doubled coordinates, including the sign. No new smoothness assumption is
needed for the actual source, where lambda, lambda-1, and both y-coordinates
already have unconditional nonvanishing proofs.

The source-extension implementation is currently in
`/tmp/rh-xi-legendre-halving-criterion.lean`. It defines the mapped source curve,
proves equality with its actual base change, maps both coordinate sections,
and aims for exact halving iff criteria over every field extension of Marked.
Its first pass found notation and local decidable-equality issues; corrected
check underway. No source-extension result claimed before that check passes.

For exact degrees, `QuadraticSubextension.finrank_adjoin_eq_two` and
`QuadraticTowerSquareClasses.isSq_or_isSq_mul_of_span` provide existing pieces.
The next field step will construct explicit intermediate fields and prove their
minimality, rather than treating a field name or square-class rank as a degree proof.

### Finite-family degree mechanism

The degree statement for arbitrary finite label sets can be proved without an
ordering choice. Induct on a finite family S of independent base square classes.
Maintain simultaneously (i) degree 2^|S| and (ii) every base scalar becoming square
in the generated field has a square twist by a subset of S. At an insertion i,
(ii) and base independence show d_i remains nonsquare, so the new step has degree
two. The existing quadratic span theorem says a scalar becoming square at that
step was square already or becomes square after multiplying by d_i. Apply (ii)
and either retain the previous subset or insert i. This closes the induction.
For the source family, index the common Xi class by `none` and lambda_n by
`some n`; the already formal exact packet criterion supplies every independence
condition. The finite field generated by the common root and roots at labels T
then has degree 2^(|T|+1). For nonempty T its minimality follows from the source
halving iff criteria, one label at a time. Empty T is explicitly the common
quadratic field, not the field of an empty collection of halving tasks.

### Actual extension criteria and quadratic field kernel pass Lean

The corrected source scratch passes without diagnostics. Promoted
`RHTower/XiLegendreHalvingCriterion.lean` and wired its import. It proves the two
unconditional source iff criteria for every field extension of Marked, with
explicit mapped curves and sections; `sourceCurveOver_eq_baseChange` verifies
that the curve is the actual scalar extension. Its targeted build is queued.
The leaf imports only the translated-section parent, avoiding unnecessary
positive-kernel and square-class-independence dependencies.

`HTGeometry/QuadraticAdjoinSquareKernel.lean` also passes scratch and targeted
build. Its six public lemmas give root membership, minimal quadratic adjunction,
exact one-step square-class kernel, and degree four for two independent roots.
These remain generic helpers until the prepared actual source fields are checked.
The source field scratch `/tmp/rh-xi-halving-fields.lean` defines chosen roots in
an algebraic closure of Marked, minimal fields admitting halves, and degrees two
and four. The generic finite-family induction is separately prepared in
`/tmp/rh-multiquadratic-adjoin-degree.lean`. Both checks are queued, sequentially
with the source criterion build. Final actual-source and axiom audits remain open.

The multiquadratic deep search returned full inventory coverage but partial
retrieval. Its useful hit was the already inspected quadratic-subextension degree
lemma; unrelated quaternion and number-field degree hits were not imported.

### Actual minimal fields of degrees two and four checked

`XiLegendreHalvingCriterion` targeted build passes. The generic finite-family
induction passes scratch and targeted build as
`HTGeometry/MultiquadraticAdjoinDegree.lean`. Its theorem proves exact degree
and the finite-support square-twist kernel together.

The source field scratch passes without diagnostics and is promoted as
`RHTower/XiLegendreHalvingFields.lean`. It defines `HalvingClosure`,
`commonHalvingField`, and `translatedHalvingField n`, proves each field's
minimality for admitting an actual half, constructs the corresponding existence
statements, and proves degrees two and four. Targeted build underway.
The six-module closure (including finite joint fields) still needs final direct
source checks and public axiom audits.

The prepared joint-field scratch `/tmp/rh-xi-joint-halving-fields.lean` applies
the Option-indexed independent family, defines the joint field, and aims to
prove its exact degree and minimality for every finite nonempty label set.
This is now the remaining source instantiation check. All field results are
stated as least fields admitting the requested halves. The classical inference
that they contain all four halves also uses rationality of Legendre two-torsion;
no separate formal all-four-halves coordinate-membership theorem is claimed.

Lean integration note: force the same local classical `DecidableEq` instance
for intermediate-field points as the source API uses; the default subtype
instance is mathematically equivalent but gives a different elaborated `Point.add`.
A local high-priority instance resolved this mismatch without altering any theorem
statement, adding an axiom, or changing a resource limit. Explicit `and_congr`
handles coercions in the field membership criterion.

### Six-module implementation complete; final audits running

The corrected joint-field scratch passes without diagnostics. Promoted and wired
`RHTower/XiLegendreJointHalvingFields.lean`. It proves independence of the actual
Option-indexed radicands, exact degree 2^(|T|+1) of `jointHalvingField T`, its
minimality for admitting all requested translated halves when T is nonempty,
and existence of those halves. All five prerequisite leaves already passed their
targeted builds; the sixth build is running, followed by final direct source
checks for all six leaves and `#print axioms` for all 40 public declarations
(including the closure type abbreviation). No final audit PASS claimed yet.

The next domain-boundary question is recorded separately in
`../0-backlog/xi-critical-strip-kummer-collapse.md`; it does not weaken any proved
global field theorem. Its initial deep search has finished with full inventory
coverage and `partial=true`, mostly irrelevant hits. A direct source-name search
located the existing kernel integrability and coarser strip-bound lemmas.

### Final verification, 2026-10-07

All six targeted builds pass. Final `lake env lean` checks of each actual source
pass with empty diagnostic logs. All 40 public declarations were individually
audited by `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound`
occur. The finite joint field has exact degree 2^(|T|+1), and its minimality for
the collection of translated halving tasks explicitly requires T nonempty.

Imports are wired and `scripts/formal_tools.py index` passes. The authoritative
lint gate fails on eight unrelated currently unwired leaves: ZetaTwistedFirstMomentUniform,
ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, PolydiskRadialLogarithm,
and PolynomialSegmentArgument. No error names an owned module from this cycle.
Logs: `/tmp/rh-legendre-halving-{index,lint}-20261007.log`,
`/tmp/rh-legendre-halving-axioms.log`, and the six leaf-specific final logs.

Anti-theatre verdict: **BRIDGE**, classical halving and Kummer mechanisms.
This closes a real sufficiency/minimality gap in the source geometry but does
not certify scientific novelty or discharge an RH zero-location premise.
Next work tests the actual analytic-domain boundary before attaching further
RH significance to these global division fields. No difficulty-based work
deferral was used. Obsolete implementation scratches were removed after audit.

## Lean certificate (2026-10-09)

Every claim of the card, including the all-four-halves coordinate membership, is proved
unconditionally.

| Card claim | Lean declaration |
|-|-|
| Explicit three-root half in the affine group law | `LegendreDoubling.exists_half_of_square_roots` |
| Halving iff `x`, `x-1` square (non-two-torsion point) | `LegendreDoubling.exists_half_iff_square_coordinates` |
| `P_n` has a half over `E` iff `ξ` square in `E` (every extension) | `XiGlobalKummer.sourceSectionOver_has_half_iff` |
| `Q_n` has a half over `E` iff `ξ`, `λ_n` square in `E` | `XiGlobalKummer.translatedSectionOver_has_half_iff` |
| Least fields `M(√ξ)`, `M(√ξ,√λ_n)` admitting halves; degrees 2, 4 | `commonHalvingField_le_iff_has_half`, `translatedHalvingField_le_iff_has_half`, `commonHalvingField_finrank`, `translatedHalvingField_finrank` |
| Joint field: degree `2^(|T|+1)`, least field for all halves (`T` nonempty) | `jointHalvingField_finrank`, `jointHalvingField_le_iff_has_halves` |
| Two-torsion of a Legendre curve is `{0,(0,0),(1,0),(λ,0)}`, four points | `LegendreDoubling.add_self_eq_zero_iff`, `LegendreDoubling.ncard_twoTorsion` |
| A point with a half has exactly four halves | `LegendreDoubling.ncard_halves`; source: `sourceSection_ncard_halves`, `translatedSection_ncard_halves` |
| Every half over `L` of a base point with a base half is the image of a base half | `LegendreDoubling.half_eq_pointMap` (with additive injective `pointMap`) |
| All four halves of `P_n` have coordinates in `M(√ξ)`; any one half generates it | `XiGlobalKummer.sourceHalf_coordinates_mem`, `adjoin_sourceHalf_coordinates` |
| All four halves of `Q_n` have coordinates in `M(√ξ,√λ_n)`; any one half generates it | `translatedHalf_coordinates_mem`, `adjoin_translatedHalf_coordinates` |
| Coordinates of all halves of `Q_n`, `n ∈ T`, generate the joint field | `translatedHalfCoordinates_subset`, `adjoin_translatedHalfCoordinates` |

Audit.
- `lake env lean` passes with no diagnostics on the nine modules
  `HTGeometry/{LegendreDoublingSquare, LegendreHalvingCriterion, LegendreHalfCoordinates,
  QuadraticAdjoinSquareKernel, MultiquadraticAdjoinDegree}` and
  `RHTower/{XiLegendreHalvingCriterion, XiLegendreHalvingFields, XiLegendreJointHalvingFields,
  XiLegendreHalfCoordinates}`.
- Axiom audit over every declaration of these modules: 97 declarations, only `propext`,
  `Classical.choice`, `Quot.sound`.
- All nine modules are wired once into `HTGeometry.lean` / `RHTower.lean`.

## Log (promotion)

- 2026-10-09: two-torsion classification, four-halves count and coordinate membership of every
  half formalized (`LegendreHalfCoordinates`, `XiLegendreHalfCoordinates`); promoted to stage 3.
