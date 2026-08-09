# Promotion-observation naturality, kernel migration, and false-closure law

- **ID:** ULF-OPM-9
- **Stage:** 2-fully-proven
- **Type:** PROMOTION/OBSERVATION EXCHANGE LAW
- **Statement:** Promotion differentiation commutes with additive observation. An observed binary
  promotion is associative exactly when the source associator lands in the observer kernel; a
  faithful observer cannot create false closure.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [PROMOTION-OBSERVATION EXCHANGE] [CHARGE MIGRATION] [LEAN-CERTIFIED] [NOT RH]

## 1. Observing a compensator

Let `M` be an additive monoid, let `A,B` be additive abelian groups, let

\[
 \kappa:M\times M\to A
\]

be a binary compensator, and let

\[
 q:A\to B
\]

be an additive observer. Define the observed compensator

\[
 (q\kappa)(x,y)=q(\kappa(x,y)).
 \tag{PO.1}
\]

## 2. Naturality of law birth

### Theorem 2.1

\[
 \boxed{
 \mathfrak a_{q\kappa}(x,y,z)
 =q\bigl(\mathfrak a_\kappa(x,y,z)\bigr).}
 \tag{PO.2}
\]

### Proof

Expand the promotion differential from ULF-OPM-6 and use preservation of addition and subtraction
by `q`. QED.

This is the exact exchange law between observation and higher-law birth. Observation does not
produce a different associator by magic; it transports the source associator.

## 3. Kernel-migration criterion

### Theorem 3.1

The observed promoted binary operation is associative if and only if

\[
 \mathfrak a_\kappa(x,y,z)\in\ker q
 \quad\text{for all }x,y,z.
 \tag{PO.3}
\]

### Proof

By ULF-OPM-6, observed associativity is equivalent to vanishing of the observed associator. Apply
`(PO.2)`. QED.

Therefore observed closure has two sharply different explanations:

1. genuine source closure: `a_kappa=0`;
2. false closure: `a_kappa!=0` but the charge migrates into `ker q`.

The residual has been hidden, not resolved.

### Corollary 3.2 -- faithful reflection

If `q` is injective, the observed promoted law is associative if and only if the source promoted law
is associative.

### Proof

Injectivity makes `ker q=0`; apply Theorem 3.1. QED.

## 4. Exact mod-two false closure

Use the cubic compensator from ULF-OPM-6,

\[
 \kappa_3(x,y)=x^2y,
 \qquad
 \mathfrak a_{\kappa_3}(x,y,z)=2xyz.
 \tag{PO.4}
\]

Let

\[
 q:\mathbb Z\to\mathbb Z/2\mathbb Z
\]

be reduction modulo two. Then

\[
 q(2xyz)=0
\]

for all `x,y,z`, so the observed promoted operation is associative. But at `(1,1,1)` the source
associator equals `2`, hence the source promoted operation is not associative.

This is a minimal exact false-closure laboratory: one observer reports a complete binary law while
the lifted rulebook requires a ternary coherence.

## 5. Mechanism consequence

No-go shadows now have a precise interpretation. When a promotion residual disappears under an
observer, ask whether:

- it vanished before observation;
- it entered the observer kernel;
- it became inadmissible under completion.

Only the first is genuine resolution. The second is kernel migration (this theorem); the third is
admission-relative singularity (ULF-OPM-7).

This turns the vague slogan “observation hides curvature” into an exact law valid for any additive
promotion differential.

## 6. Sharp boundaries

1. Additivity of the observer is load-bearing.
2. The theorem governs the algebraic associator; topological continuity is a separate admission
   test.
3. Kernel migration does not itself construct a compensating higher reporter.
4. Approximate observers require quantitative stability not proved here.
5. No proof route, positivity, recurrence, HT, or RH claim appears.

## Lean certification

Formalized without project axioms in
`GaloisForLFunctions.HTGeometry.ConstitutivePromotionObservationExchange`:

1. observed compensator;
2. exact promotion-differential naturality;
3. observed associativity iff all source associators lie in the observer kernel;
4. injective-observer reflection;
5. integer cubic compensator modulo two: source nonclosure and observed closure;
6. bundled exchange-law theorem.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Log

- 2026-08-09 -- observation/promotion exchange identified as exact kernel-migration law.
