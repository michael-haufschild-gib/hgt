# Unitary symmetry fracture conserves the lost and created defect

- **ID:** `symmetry-fracture-unitary-defect-conservation`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE THEOREM / BRIDGE / NOT NEW MATHEMATICS
- **Parent:** `../../1-in-progress/actuality-conservation-boundary-colligation-law.md`
- **Status:** `[DEPENDENCY-CLOSED PAPER PROOF] [UNCONDITIONAL LEAN]`
- **Physics status:** `[NO PHYSICAL INTERPRETATION PROVED]`

## The question exposed by the corpus

The existing \(4/6/4\) event theorem proves that a maximal symmetry-preserving map loses four
source directions and leaves four target directions unproduced.  It does not identify those
spaces.  Equal dimensions are not actuality conservation.

The missing mathematical question is:

> If the visible symmetry-preserving event is only one part of a complete reversible event, does
> the complementary part canonically transport the lost source defect into the new target defect?

The answer is yes.

## Setup

Let \(V\) be a finite-dimensional complex Hilbert space.  Let
\[
A^2=1,\qquad A^\dagger=A
\]
be a self-adjoint involution and define
\[
P=\frac{1-A}{2},\qquad Q=1-P=\frac{1+A}{2}.
\]
Thus \(P,Q\) are complementary orthogonal projections.  Let \(U:V\to V\) be unitary and define
\[
T=UQ,\qquad S=UP.
\]
The map \(T\) is the part of \(U\) that preserves the source involution character, while \(S\) is
the complementary part.

## Theorem — unitary symmetry-fracture defect conservation

The following identities hold:
\[
\begin{aligned}
U&=T+S,\\
TA&=T,& SA&=-S,\\
T^\dagger T&=Q,& S^\dagger S&=P,\\
T^\dagger S&=0,& S^\dagger T&=0,\\
TT^\dagger+SS^\dagger&=1.
\end{aligned}                                                   \tag{1}
\]
Consequently,
\[
1-T^\dagger T=S^\dagger S=P,\qquad
1-TT^\dagger=SS^\dagger.                                       \tag{2}
\]
Moreover,
\[
\ker T=\operatorname{im}P,\qquad
\ker T^\dagger=\operatorname{im}S.                              \tag{3}
\]
Under the Hilbert-space realization
\(\operatorname{coker}T\cong\ker T^\dagger\), the restriction
\[
S:\ker T\longrightarrow\operatorname{coker}T
\]
is a unitary equivalence, with inverse induced by \(S^\dagger\).

Thus the complete unitary \(U\) does not merely force equal defect dimensions.  Its
symmetry-transmuting component is the exact missing arrow:
\[
\boxed{\text{lost source defect}\ \xrightarrow[\;\simeq\;]{\,S\,}\
       \text{new target defect}.}                               \tag{4}
\]

## Proof

Since \(A^2=1\) and \(A^\dagger=A\),
\[
P^2=P,\qquad Q^2=Q,\qquad PQ=QP=0,\qquad P+Q=1,
\]
and both projections are self-adjoint.  Therefore
\[
T+S=U(Q+P)=U.
\]
The identities
\[
QA=Q,\qquad PA=-P
\]
give \(TA=T\) and \(SA=-S\).

Using \(U^\dagger U=1\),
\[
T^\dagger T=QU^\dagger UQ=Q,\qquad
S^\dagger S=PU^\dagger UP=P,
\]
and the cross terms vanish because \(QP=PQ=0\).  Using \(UU^\dagger=1\),
\[
TT^\dagger+SS^\dagger
=U(Q^2+P^2)U^\dagger
=U(P+Q)U^\dagger
=1.
\]
This proves (1) and (2).

If \(x\in\operatorname{im}P\), then \(Qx=0\), hence \(Tx=0\).  Conversely, if \(Tx=0\), applying
\(U^\dagger\) gives \(Qx=0\), so \(x=(P+Q)x=Px\).  Therefore
\(\ker T=\operatorname{im}P\).

The cross identity \(T^\dagger S=0\) gives
\(\operatorname{im}S\subseteq\ker T^\dagger\).  Conversely, if \(T^\dagger y=0\), then
\(QU^\dagger y=0\), hence \(U^\dagger y=PU^\dagger y\), and
\[
y=UU^\dagger y=UPU^\dagger y\in\operatorname{im}S.
\]
This proves (3).  Finally \(S^\dagger S=P\) and \(SS^\dagger=1-TT^\dagger\) show that \(S\) and
\(S^\dagger\) restrict to mutually inverse isometries on the two defect spaces. \(\square\)

## Exceptional \(4/6/4\) corollary

For the ten-dimensional source involution already formalized in
`EventInterfaceIndex.lean`, assume
\[
\operatorname{tr}A=2.
\]
Then \(P\) has complex rank four and \(Q\) has complex rank six.  Therefore:

- \(T\) transmits six directions;
- \(\ker T\) has dimension four;
- \(\operatorname{coker}T\) has dimension four; and
- \(S\) is the exact unitary transport between those four-dimensional defects.

The existing \(4/6/4\) numerical index is therefore the visible shadow of a stronger
self-dual completion law.

## What this does and does not establish

The theorem is standard projection/unitary-defect algebra, adjacent to partial-isometry defect
spaces, [Julia operators and Halmos dilations](https://arxiv.org/abs/1803.09329), and unitary
completions. It is not claimed as new mathematics.

It does establish a missing exact bridge:

```text
source involution + complete unitary event
                ↓
symmetry-preserving partial event T
  + symmetry-transmuting complement S
                ↓
ker T ≃ range S ≃ coker T.
```

It does **not** prove:

- that a physical event supplies a canonical \(U\);
- that the exceptional pure pair selects the required real form and source involution;
- that \(T\) is matter/gauge transport;
- that \(\operatorname{im}S\) is causal spacetime;
- that event-to-event variation of \(S\) is gravity; or
- any dynamics or empirical prediction.

Those are physical conjectures and remain at Stage 1.

## Formal certificate

Lean module:
`formal/GaloisForLFunctions/HTGeometry/SymmetryFractureDefectConservation.lean`.

Main declarations:

- `symmetryPreserving_add_transmuting`;
- `symmetryPreserving_mul_involution`;
- `symmetryTransmuting_mul_involution`;
- `symmetryPreserving_adjoint_mul_self`;
- `symmetryTransmuting_adjoint_mul_self`;
- `symmetryPreserving_final_add_transmuting_final`;
- `symmetryPreserving_initial_defect_eq_transmuting_initial`;
- `symmetryPreserving_final_defect_eq_transmuting_final`;
- `symmetryPreserving_ker_eq_record_range`;
- `symmetryTransmuting_range_eq_preservingAdjoint_ker`;
- `symmetryCreatedReporter_ker_eq_preserving_range`;
- `symmetryPreservingCokernelEquivRecordRange`; and
- `symmetryPreservingCokernelEquivRecordRange_transmuting`.

Verification:

- direct foreground check:
  `lake env lean GaloisForLFunctions/HTGeometry/SymmetryFractureDefectConservation.lean`;
- final module audit:
  `lake build GaloisForLFunctions.HTGeometry.SymmetryFractureDefectConservation`;
- result: `2948/2948` jobs built successfully; and
- printed axioms for the two defect identities, kernel/range theorem, adjoint-kernel theorem, and
  cokernel realization are exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Physical hunch exposed, not proved

> **Spacetime is the quantum symmetry that could not survive an event.**

Expanded:

> Complete quantum evolution conserves every distinction, but objective actualization changes
> how some distinctions transform.  The symmetry-preserving part remains available as inherited
> physical identity.  The symmetry-transmuting remainder reappears as new causal geometry.
> Gravity is the event-to-event holonomy of that remainder.

The theorem makes this hunch sharper because “lost equals new” is no longer merely a
kernel--cokernel dimension coincidence.  If source-complete physical evolution really supplies
the unitary completion, its odd component is the canonical defect equivalence.

## Collision and hostile boundary

1. **Julia/Halmos collision.** Unitary defect completion is established operator theory.  No
   novelty can rest on (1)--(4).
2. **Stinespring false positive.** Every quantum channel admits nonunique environmental
   dilations, and unitary dilation has its own continuity failures
   ([Shirokov](https://arxiv.org/abs/1712.03219)). A freely chosen \(U\) does not define objective
   spacetime.
3. **Transported-frame false positive.** Relative to a transported involution, any \(U\) can make
   the odd component disappear.  The source involution and target observable representation must
   be selected independently of \(U\).
4. **Flat-laboratory false positive.** Ordinary symmetric gates can have nonzero odd components
   relative to a chosen grading without producing gravity.
5. **Broken-symmetry gravity collision.** Cartan-geometric gravity already gives broken symmetry a
   geometric role ([Wise](https://arxiv.org/abs/1112.2390)). Novelty cannot be “symmetry breaking
   creates geometry”; it must lie in the source-selected nonconjugate representation fracture,
   exact defect transport, and objective-event interpretation.
6. **Exceptional landing gap.** Only a source-complete exceptional event law selecting both
   nonconjugate representations and the completion can give (4) physical content.

The positive survivor is exact but presently only a bridge.
