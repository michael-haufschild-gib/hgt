# Failed conjecture: functional-equation-fixed signature is neutral

- **ID:** ULF-CRSM-F1
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** A complete group-like response fixed by functional-equation reversal must equal
  the identity signature.
- **Status:** `[FALSIFIED] [EXACT COUNTERMODEL] [POSITIVE SURVIVOR PROMOTED]`

## Conjecture

Let \(g\) be a group-like complete response signature and let the functional equation act by an
antipode-like involution. If the functional equation fixes \(g\), conjecture that \(g=1\).

## Exact killing theorem

A functional equation can combine inversion with a nontrivial involutive relabelling \(\theta\).
The fixed equation is

\[
 \theta(g)=g^{-1}.
\]

In the complete tensor Hopf algebra on primitive letters \(a,b\), let \(\theta(a)=b\) and
\(\theta(b)=a\). Then

\[
 X=a-b\ne0,
 \qquad
 \theta(X)=-X,
 \qquad
 g=\exp X\ne1,
 \qquad
 \theta(g)=g^{-1}.
\]

Thus twisted-antipode fixedness does not imply neutrality.

The current literal corpus proves even less: the functional equation permutes Dyson response
letters but does not reverse word order. On a free ordered response algebra, an order-preserving
letter permutation can agree with a sign-compensated twisted antipode through grade two only after
all letter commutators vanish. Therefore applying antipode rigidity directly would either be
ill-typed or would abelianize away the ordered memory.

## Strongest positive survivor

The fixed signatures are classified exactly by

\[
 Q_\theta=\exp(\mathcal P^-),
\]

where \(\mathcal P^-\) is the anti-invariant primitive log-signature sector. They form a reflection
space under \(xy^{-1}x\), not a subgroup. Ordinary multiplication of two fixed signatures remains
fixed exactly when they commute, and its first escaped logarithmic grade is the reflection-even
commutator \([X,Y]/2\).

A source-marked family of involutions selects neutrality exactly when its common odd sector is zero;
stable selection requires the corresponding joint reversal Gramian to be bounded below.

Full paper proof:

`../../../2-fully-proven/universal-law-field/constitutive-reflection-space-mechanics/twisted-antipode-response-reflection-fusion-grade-reconstruction-and-joint-properness-law.md`

## New insight

Functional equation is a grading mechanism. It becomes a selector only through independent source
reversals with a proper joint response. Common recovery is information-neutral and cannot provide
that missing equation.

## Lean status

No new Lean was written during this research-phase audit. The common-recovery neutrality input is
already Lean-certified in `HTGeometry.ConstitutiveFunctionalEquationPacketLift`; the new
reflection-space and joint-Gramian theorem remains to be formalized after hostile paper review.

## Log

- 2026-08-14 -- conjecture proposed, killed by the two-letter sheet-swap countermodel, and positive
  survivor promoted.
