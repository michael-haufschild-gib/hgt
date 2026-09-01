# Positive-integer two-product diagonal-gauge rigidity law

- **ID:** `ULF-TPDG-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** additive-successor / Dirichlet-formation intersection exposed by corpus facts
  F126--F129
- **Statement:** A group-valued diagonal action on positive-integer packets which preserves both
  ordinary additive fusion and multiplicative/Dirichlet fusion is uniquely the identity action.
- **Status:** `[PROVED HERE] [UNCONDITIONAL] [NOT RH] [LEAN CERTIFIED]`

## 1. Big-picture higher law

Selection may come from an **intersection of source symmetries**, not from another observer,
curvature, energy, or producer. Literal positive integers carry two genuinely distinct formation
operations:

\[
  m\boxplus n=m+n,
  \qquad
  m\boxtimes n=mn.
\]

Ordinary Cauchy packet formation sees \(\boxplus\); Dirichlet formation sees \(\boxtimes\).
Neither operation alone selects horizontal grade. The new law asks for one diagonal action to be a
symmetry of both without identifying the products. Their common diagonal symmetry group is trivial.

This is not initial-semiring collapse: no quotient equates addition and multiplication, no
cotangent module is killed, and the two products remain separate. Rigidity comes only from requiring
one source action to preserve both multiplication tables.

## 2. Corpus audit before theorem

- `DirichletMaurerCartanMellinOrbitLaw`: horizontal logarithmic grade is a genuine
  derivation/automorphism law for Dirichlet convolution, so multiplicative formation alone admits
  nonneutral grades.
- `VonMangoldtAdditiveLogJetDirichlet`: literal successor incidence supplies a distinct additive
  formation organ.
- `PrimeRadialFusionNaturality`: prime-ray Cauchy fusion is exactly positive-prime-power projection
  of Dirichlet convolution; this relates, but does not identify, depth-Cauchy and Dirichlet organs.
- `SourceNormalClockCurvatureLaw`: a single raw square-clock additive compatibility already detects
  neutral radial rate, but only as a receiver attached to that chosen clock.
- `ConstitutiveFunctionalEquationPacketLift`: functional-equation packet lifting is strictly
  information-neutral; it transports a grade but cannot remove it.
- Corpus search for simultaneous additive/multiplicative diagonal-weight classification returned no
  theorem implementing the common-symmetry intersection below.

## 3. Definitions

Let \(P=\mathbb N_{>0}\), let \(G\) be any group, and let \(w:P\to G\). A **two-product
diagonal gauge** satisfies, for all \(m,n\in P\),

\[
  w(m+n)=w(m)w(n), \tag{A}
\]
\[
  w(mn)=w(m)w(n). \tag{M}
\]

On packet atoms \(\delta_n\), the diagonal map \(D_w\delta_n=w(n)\delta_n\) preserves atomwise
ordinary Cauchy fusion exactly when (A) holds and preserves atomwise Dirichlet fusion exactly when
(M) holds. Thus theorem classifies common diagonal atom symmetries of the two packet products.

## 4. Main theorem: common gauge space is a point

**Theorem 4.1 (two-product diagonal-gauge rigidity).** For every group \(G\), every two-product
diagonal gauge \(w:P\to G\) satisfies

\[
  w(n)=1_G\qquad(n\in P).
\]

Consequently any two such gauges are equal and their moduli space is a singleton.

**Proof.** Apply (M) to the multiplicative unit:

\[
  w(1)=w(1\cdot1)=w(1)^2.
\]

Cancellation in \(G\) gives \(w(1)=1_G\). Induct on positive integers. The base is proved. If
\(w(n)=1_G\), then (A) gives

\[
  w(n+1)=w(n)w(1)=1_G.
\]

Hence \(w\equiv1_G\). Pointwise equality proves uniqueness. ∎

## 5. Radial-grade prediction

For \(a\in\mathbb R\), define the positive radial weight

\[
  w_a(n)=n^a.
\]

It always preserves multiplicative formation:

\[
  w_a(mn)=w_a(m)w_a(n).
\]

**Corollary 5.1.** It preserves ordinary additive atom fusion for all positive \(m,n\) iff
\(a=0\).

**Proof.** If additive compatibility holds, evaluate it at \((m,n)=(1,1)\):
\(2^a=1\), hence \(a=0\). Conversely \(w_0\equiv1\). ∎

This predicts an exact theorem in the radial-clock organ from joint packet-product symmetry: one
additive atom square is enough to kill every nonneutral multiplicative radial character.

## 6. Exact RH closure and open occurrence law

For a Xi occurrence with centered horizontal grade \(a=\Re\rho-\tfrac12\), existing corpus
dictionaries close RH once \(a=0\) is proved. The present theorem would provide that implication if
literal Xi source formation generated **one and the same diagonal action** on positive-integer atoms
which:

1. is the existing multiplicative Mellin/radial action; and
2. preserves literal ordinary additive packet fusion before divisor specialization.

Then Theorem 4.1 forces the action to be identity; equivalently Corollary 5.1 forces \(a=0\), and the
existing horizontal-grade dictionary proves RH.

Hostile audit found no such occurrence theorem. The Mellin action is a Dirichlet-algebra action;
ordinary additive convolution is a distinct source operation, and exact mixed subdivision makes
power characters grade eigenvectors rather than additive-convolution automorphisms. Imposing the
second preservation law would therefore insert neutrality. The rigidity theorem survives as a
classification and a sharp test for future source constructions, but this direct RH lift is retired.

## 7. Scope and non-circularity

- Theorem 4.1 and Corollary 5.1 are unconditional algebraic statements on pre-divisor positive
  integers.
- No Xi zero, RH-equivalent boundedness, positivity, descent, compactness, or fixed-support premise
  occurs in either proof.
- The theorem narrows the common-symmetry model class, but it does not yet prove that Xi formation
  lies in that class.
- `CANNOT-70` remains respected: operations are not collapsed; only their automorphism intersection
  is classified.

## 8. Lean plan

Lean module `GaloisForLFunctions.HTGeometry.TwoProductDiagonalGaugeRigidity` formalizes
`TwoProductDiagonalGauge`, identity gauge, pointwise rigidity, `Unique` common-gauge space, actual
packet atoms and their two fusions, the iff-classification of simultaneous atom preservation,
multiplicative radial law, and additive-radial iff-neutral theorem. Direct compile and targeted
module build pass. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-09-01 — corpus audit completed; theorem and radial corollary proved on paper; Lean scratch
  passed.
- 2026-09-01 — packet-level iff-classification added; targeted Lean build and axiom audit passed;
  direct Xi occurrence lift killed by domain audit.
