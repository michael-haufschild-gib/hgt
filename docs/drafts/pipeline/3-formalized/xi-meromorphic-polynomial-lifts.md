# Polynomial lifts in the global meromorphic plane

- **ID:** RH-XIMPL-20261007
- **Stage:** 3-formalized; paper proof, actual source and axiom audits passed
- **Parent:** `../2-fully-proven/xi-finite-cover-monodromy.md`
- **Verdict:** BRIDGE, classical pole removal and actual polynomial rigidity

## Exact target

For real a, complex polynomial P and element h of the corpus's global
meromorphic plane field, if P(h)=xi(s)*exp(-a*s), then P.natDegree=1.
There is no entire-representative assumption on h. This excludes meromorphic
roots of P(X)-d_a for every nonlinear P. It does not by itself prove
irreducibility of P(X)-d_a in degrees above three.

The competing possibility is only an implementation hazard: a representative
may assign arbitrary finite values at its poles. All pole arguments must use
punctured germs and meromorphic normal forms, not pointwise equalities at a
pole. This is a BRIDGE increment, not a new beyond-literature conjecture.

## Dependency-closed paper proof

Let f be a meromorphic representative. If P is nonconstant, split it over C:
P(X)=c product_j(X-b_j), with c nonzero, including root multiplicities.
At a pole z of f, let m=ord_z(f)<0. Every f-b_j has the same order m,
so ord_z(P(f))=degree(P)*m<0. An entire right side has nonnegative order,
a contradiction. Thus f has only removable singularities. Filling them by
normal form gives an entire function h; continuity extends P(h)=d_a at
every filled point. The predecessor polynomial-left-factor theorem forces
degree one. The constant-P case is excluded by actual d_a ray growth.

Every input is existing standard local meromorphic order calculus,
factorization over C, removable singularities, and the actual Xi endpoint.
No uniformization, RH premise, numerical computation, or new axiom.

## Evidence and next steps

The existing `HTGeometry/MeromorphicPlaneCubicRoot.lean` implements the
same local-order/normal-form method for (f-3)*f^2. Its full source was read.
Generalize in a new leaf, keeping that audited predecessor unchanged.
Deep query `meromorphic polynomial composition entire remove poles analytic
order leading coefficient` completed partial=true, inventory68201; malformed
local-model JSON at filter_and_judge. All twenty candidate and twenty source
statements inspected, including the existing cubic pole-removal proof. Output:
`/tmp/rh-meromorphic-polynomial-lift-search-20261007.json`.
A four-theorem generic scratch and API probe passed. Promoted and wired
`HTGeometry/MeromorphicPolynomialLift.lean` and
`RHTower/XiMeromorphicPolynomial.lean`. Both targeted builds and both final
`lake env lean` actual-source audits passed. All five public declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The generic endpoint preserves the original field element as well as the
polynomial equation in its entire representative. Actual endpoint reuses
`xiCubicParameterElement` rather than creating a second source-field definition.

Evidence: `/tmp/rh-xi-meromorphic-polynomial-build.log`,
`/tmp/rh-xi-meromorphic-polynomial-axioms.log`, and
`/tmp/rh-final-{MeromorphicPolynomialLift,XiMeromorphicPolynomial}.log`.
Formal lint has ten unrelated unwired HTGeometry modules (ApertureConeCalculus,
ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal,
BoundaryCoronaCStarAlgebra, CosineCornerCoordinates, CosineCornerMarker,
CosineCornerSequence, CosineCornerUnfolding, CosineProductNonrealFibers).
No owned failure; no claim of globally clean lint.

Scientific assessment: this is a classical bridge, not new scientific knowledge.
The formal frontier moved from entire to arbitrary meromorphic polynomial lifts;
the rational and higher-genus cases remain separate work. No stronger
irreducibility or RH conclusion follows from this increment alone. Corpus
search exposed reusable cubic machinery; no task was skipped for effort.

The next rational-map reduction, after this increment, must account for
inner meromorphic poles as well as finite poles of the outer map. A Möbius
coordinate sending an outer pole to infinity makes the inner lift entire;
little Picard then leaves a polynomial or a Laurent expression. This is a
paper mechanism only until the coordinate change, coprime denominators, and
removable extension are proved in the actual meromorphic field.
