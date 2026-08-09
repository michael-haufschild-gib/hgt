# Central-promotion/admission exchange and quotient-obstruction law

- **ID:** ULF-RLM-11
- **Stage:** 2-fully-proven
- **Type:** CROSS-MODE MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [INTERNAL FRONTIER AUDITED]
  [EXTERNAL PARENTS AUDITED] [CROSS-MODE EXCHANGE LAW] [LEAN-PROVED]
  [NO PROJECT AXIOMS] [NOT RH]

## 1. Mechanism question

Central promotion adjoins a coefficient that remembers composition history.  Admission promotion
restricts which coefficient values are legal.  The open exchange question is:

> When does adjoining a history compensator commute with restricting the admitted coefficient
> doctrine?

This compares two unlike promotion modes without invoking any proof route.

## 2. Frontier

### Internal

- ULF-OPM-6 proves that a compensator (kappa) closes associatively exactly when its promotion
  differential vanishes.
- ULF-OPM-7 proves that algebraic exactness and admitted exactness are distinct.
- `OmegaObstruction.lean` defines subgroup/lattice-valued cocycles and proves their stability under
  admitted gauge updates.
- No certified theorem identifies subgroup-valuedness with closure of the promoted carrier or with
  an exact exchange law between central and admission promotions.

### External

Central extensions and their classification by (H^2) are standard.  Joshi--Spallone,
*Central Extensions and Cohomology*, arXiv:2307.14658, gives a modern topological classification and
lifting criterion.  Dekimpe--Hartl--Wauters, arXiv:1103.4052, gives cocycle-level maps in the
seven-term exact sequence.  Higher central-extension classification in semi-abelian categories is
developed by Rodelo--Van der Linden, arXiv:1502.05282.

The theorem below is therefore a mechanism bridge, not an isolated cohomology novelty claim.  Its
field content is the exact cross-mode selector and the singular countermodel.

## 3. Failed conjecture

### Conjecture 0

If an ambient central promotion is associative, every coefficient admission restriction inherits
an associative promoted law.

### Verdict: [FALSIFIED]

Take (M=A=\mathbb Z), (kappa(x,y)=xy), and admit only coefficients killed by reduction modulo
two.  Bilinearity makes (kappa) a 2-cocycle, so the ambient promotion is associative, but
(kappa(1,1)=1) is not admitted.  The admitted subcarrier is not even closed under the promoted
binary operation.

### Stronger replacement

The exchange selector must be coefficient landing, not ambient associativity.

## 4. Exact definitions

Let (M) be an additive monoid, (A,B) additive commutative groups, and
(q:A\to B) an additive reporter.  Let

\[
 (x,a)\star_\kappa(y,b)
  =(x+y,a+b+\kappa(x,y)).
\tag{1}
\]

The admitted coefficient subgroup is (\ker q).  Define

\[
 \operatorname{Adm}_q(\kappa)
 \quad\Longleftrightarrow\quad
 q(\kappa(x,y))=0\quad\text{for all }x,y.
\tag{2}
\]

Equivalently, every compensator value lies in (\ker q).

## 5. The exchange theorem

### Theorem 5.1

For every (q) and (kappa), the following are equivalent:

1. (operatorname{Adm}_q(kappa));
2. the admitted carrier (M\times\ker q) is closed under (1);
3. the observed compensator (q\kappa) vanishes identically.

When these conditions hold, (1) restricts uniquely to a promoted operation on
(M\times\ker q), and inclusion into (M\times A) preserves the operation.  If the ambient
promotion is associative, so is the restricted promotion.

If they fail, some pair (x,y) has (q(\kappa(x,y))\ne0).  That value is the exact
central/admission exchange obstruction: ambient central closure exists, but admission after central
promotion is impossible without enlarging the admitted coefficient law.

### Proof

Assume (1).  If (a,b\in\ker q), additivity gives

\[
 q(a+b+\kappa(x,y))=q(a)+q(b)+q(\kappa(x,y))=0,
\]

so the admitted carrier is closed.  Conversely apply closure to ((x,0)) and ((y,0)); the second
coordinate of their product is (kappa(x,y)), hence it lies in (\ker q).  This proves
(1) iff (2).  The definition of a kernel proves (1) iff (3).

Under these conditions, the restricted operation is forced by compatibility with the injective
coefficient inclusion, proving uniqueness.  Associativity follows by applying inclusion to the two
restricted schedules and using ambient associativity; injectivity reflects equality.

Failure of (3) gives the displayed nonzero obstruction and proves nonclosure by the same zero-input
pair.

## 6. Interaction with the promotion differential

By ULF-OPM-9,

\[
 \mathfrak a_{q\kappa}=q(\mathfrak a_\kappa).
\tag{3}
\]

Thus ambient associativity forces the quotient obstruction (q\kappa) itself to be a cocycle.  A
nonzero (q\kappa) is not a failed associator; it is a closed, persistent obstruction to the
admission exchange.  This separates two failure modes:

| test | nonzero output | forced response |
|---|---|---|
| promotion differential (\mathfrak a_\kappa) | binary closure fails | higher coherence |
| admission reporter (q\kappa) | coefficient landing fails | enlarge/change admission |

## 7. Exact singular countermodel

Let (q:\mathbb Z\to\mathbb Z/2\mathbb Z) be reduction modulo two and
(kappa(x,y)=xy).  Then

\[
 \mathfrak a_\kappa(x,y,z)=0
\]

for all integers, because

\[
 xy+(x+y)z=yz+x(y+z).
\]

But (q(\kappa(1,1))=1\ne0).  Therefore:

1. the ambient integer central promotion is associative;
2. the even-coefficient admitted carrier is not closed;
3. reduction modulo two detects the exact exchange obstruction;
4. higher promotion is not forced--admission change is.

This is the smallest bifurcation laboratory separating higher-coherence birth from singular
admission birth.

## 8. Hostile audit

1. **Is this merely subgroup closure?** Algebraically yes.  Field significance is the exact
   selector coupling two certified promotion modes and distinguishing it from the associator test.
2. **Does nonzero (q\kappa) prove a nontrivial cohomology class?** No.  It proves nonclosure for
   the fixed admission reporter.  Gauge/cohomology claims require additional hypotheses.
3. **Could another operation on (M\times\ker q) exist?** Yes, but not one whose inclusion
   preserves the declared ambient promoted operation.  Compatibility is load-bearing.
4. **Does associativity select the admission doctrine?** No.  The reporter (q) remains declared;
   source genesis is still open.
5. **Positive survivor:** central and admission promotions have a complete exchange criterion,
   exact quotient residual, and sharp associative/nonadmitted countermodel.

All proof obligations are dependency-closed on paper and survived hostile review.

## 9. Lean certification

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveCentralAdmissionExchange`.

Lean certifies:

1. admission iff restricted-carrier closure;
2. admission iff quotient compensator vanishes;
3. construction and uniqueness of the restricted promoted operation;
4. descent of ambient associativity;
5. the associative integer-multiplication/mod-two nonadmission countermodel;
6. one closed capstone containing all singular-countermodel conclusions.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.  It uses no `sorry`,
`admit`, project axiom, `opaque`, `unsafe`, `native_decide`, or computational certificate.

## Log

- 2026-08-09 -- ambient-associativity conjecture falsified; coefficient-landing exchange theorem
  and mod-two singular countermodel closed on paper, survived hostile audit, and promoted to Stage
  2.
- 2026-08-09 -- theorem family formalized in Lean, wired into universal-law-field umbrella, and
  promoted to formal certification.
