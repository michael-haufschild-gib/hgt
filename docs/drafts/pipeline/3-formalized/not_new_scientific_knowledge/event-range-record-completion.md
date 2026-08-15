# A faithful complementary record completes an event

- **ID:** `event-range-record-completion`
- **Stage:** 3-formalized
- **Type:** EXACT LINEAR-ALGEBRA RECONSTRUCTION / PHYSICS BOUNDARY
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `noninvertible-event-complementary-record-boundary.md`
- **Research target:** `../../1-in-progress/actuality-conservation-boundary-colligation-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/EventRangeRecordCompletion.lean`

## Exact theorem

Let \(K\) be a field, let \(V,W\) be finite-dimensional \(K\)-vector spaces with
\(\dim V=\dim W\), and let
\[
T:V\longrightarrow W
\]
be linear. Write
\[
I_T=\operatorname{im}T,
\qquad
C_T=\operatorname{coker}T=W/I_T.
\]
For a linear record \(R:V\to C_T\), define the transmitted-plus-recorded completion
\[
\widehat T_R:V\longrightarrow I_T\oplus C_T,
\qquad
v\longmapsto (Tv,Rv),                                             \tag{1}
\]
where the first component is corestricted to \(I_T\).

Then:

1. \(\widehat T_R\) is injective exactly when the ordinary product map
   \((T,R):V\to W\oplus C_T\) is injective;
2. \(\dim V=\dim(I_T\oplus C_T)\);
3. if \((T,R)\) is injective, then \(\widehat T_R\) is a linear equivalence
   \[
   V\xrightarrow{\;\sim\;}I_T\oplus C_T.                          \tag{2}
   \]

Thus a visible event can be noninvertible while its transmitted-plus-recorded completion is
invertible.

For a complex ten-to-ten event of rank six,
\[
\dim I_T=6,
\qquad
\dim C_T=4,                                                       \tag{3}
\]
and every faithful cokernel-valued record gives an exact
\[
\mathbb C^{10}\simeq \mathbb C^6\oplus\mathbb C^4                 \tag{4}
\]
completion.

## Proof

The only difference between \(\widehat T_R\) and \((T,R)\) is that the first component of
\(\widehat T_R\) remembers the proof that \(Tv\) lies in \(\operatorname{im}T\). Equality of the
corestricted values is equivalent to equality of their values in \(W\). Hence the two maps have
the same fibres and item 1 follows.

Quotient dimension gives
\[
\dim I_T+\dim(W/I_T)=\dim W.
\]
Together with \(\dim V=\dim W\), this proves item 2. An injective linear map between
finite-dimensional spaces of equal dimension is surjective, proving item 3 and `(2)`.
For \(\dim V=\dim W=10\) and \(\dim I_T=6\), quotient dimension gives `(3)`, and `(2)` gives
`(4)`. \(\square\)

## What this theorem says—and does not say

The theorem distinguishes two statements that must not be conflated:

1. **reconstruction:** once a faithful complementary record \(R\) is supplied, transmitted data
   plus record reconstruct the source exactly;
2. **selection:** the bare event \(T\) does not canonically choose \(R\).

The parent card proves the second boundary by the independent automorphism freedom of
\(\ker T\). Consequently, `(2)` cannot by itself identify \(C_T\) with spacetime, make \(R\)
physical, select a Lorentzian structure, or derive a dynamical law. Any proposed physics must
derive the record from source structure that is absent from the bare linear map.

One exact source-structured case is already closed. If \(A^2=1\), its projectors
\[
P_A=(1+A)/2,\qquad Q_A=(1-A)/2
\]
satisfy \(P_A+Q_A=1\), and \(Q_A\) canonically supplies the complementary record for continuation
\(P_A\). The prior involution theorem gives
\[
\operatorname{coker}P_A\simeq\operatorname{im}Q_A.
\]
Transporting \(Q_A\) through this equivalence and applying `(2)` now gives the source-selected
completion
\[
V\xrightarrow{\;\sim\;}\operatorname{im}P_A\oplus\operatorname{coker}P_A. \tag{5}
\]
No arbitrary record remains after \(A\) is supplied. What remains open is why a physical event
selects this involution and why its two faces have the claimed physical meanings.

The exact positive survivor is:

> **Noninvertibility need not mean destruction. It can mean a change of output type: one face is
> transmitted possibility and the complementary face is a record. Reversibility returns only for
> the complete two-faced event.**

This is the algebraic bridge needed by the event--spacetime reciprocity conjecture. It is not
evidence that nature uses that bridge.

## Hostile novelty audit

`[NOT NEW MATHEMATICS]`

The proof is quotient dimension, rank--nullity, and the finite-dimensional
injective-if-and-only-if-surjective criterion. Quantum dilation, complementary-channel, and
no-hiding results occupy stronger operator-theoretic relatives:

- W. F. Stinespring, *Positive functions on \(C^*\)-algebras*, Proc. AMS **6** (1955);
- D. Kretschmann, D. Schlingemann, and R. F. Werner,
  *The information-disturbance tradeoff and the continuity of Stinespring's representation*,
  arXiv:quant-ph/0605009;
- S. L. Braunstein and A. K. Pati,
  *Quantum information cannot be completely hidden in correlations: implications for the
  black-hole information paradox*, arXiv:gr-qc/0603046.

No publication may claim `(1)`--`(4)` as new mathematics or new physics.

## Lean formalization

The unconditional formalization is in
`formal/GaloisForLFunctions/HTGeometry/EventRangeRecordCompletion.lean`.
Its capstone declarations are:

- `eventRangeRecordCompletion_injective_iff`;
- `eventRangeRecordCompletion_finrank`;
- `eventRangeRecordCompletion_bijective`;
- `eventRangeRecordCompletionEquiv`;
- `rankSixEvent_rangeRecordCompletion_dimensions`; and
- `rankSixEventRangeRecordCompletionEquiv`.

The source-involution specialization is integrated in
`formal/GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean` through:

- `involutionCokernelRecord`;
- `involutionContinuation_prod_cokernelRecord_injective`; and
- `involutionRangeRecordCompletionEquiv`.

No physical axiom, choice of record, spacetime interpretation, dynamics, or numerical
computation occurs in either module. The source-specialized result assumes only the explicit
algebraic condition \(A^2=1\); Lean does not assert that nature supplies \(A\).

## Verification

- pinned-toolchain scratch proofs: passed;
- direct
  `lake env lean GaloisForLFunctions/HTGeometry/EventRangeRecordCompletion.lean`: passed;
- direct
  `lake env lean GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean`: passed;
- final
  `lake build GaloisForLFunctions.HTGeometry.EventInvolutionComplement`: passed
  (`2948/2948`);
- axiom audit of all generic and source-specialized capstones: only `propext`,
  `Classical.choice`, and `Quot.sound`;
- `scripts/formal_tools.py lint`: passed; and
- generated formal declaration indexes regenerated.

## Research consequence

The theorem moves the open problem. It is no longer “show that lost information can be placed in
an environment,” nor “find a finite algebraic selector after an involution is supplied.” The exact
missing object is:

> an independently physical law that selects the event involution or a stronger source object,
> makes its complementary comparison a change in the type of admissible future possibilities,
> and whose iterated composition uniquely yields causal, gauge, and continuum dynamics.

Until that selector is constructed, the theorem remains bridge machinery rather than a physical
law.
