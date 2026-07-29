# Event symmetry-recognition defect

- **ID:** `event-symmetry-recognition-defect`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE THEOREM / BRIDGE / NOT NEW MATHEMATICS
- **Parent:** `../../1-in-progress/event-generated-comparison-law.md`
- **Status:** `[DEPENDENCY-CLOSED PAPER PROOF] [UNCONDITIONAL LEAN]`
- **Physics status:** `[NO PHYSICAL INTERPRETATION PROVED]`

## Question

Suppose one event transports a carrier between two endpoint symmetry laws. How much of the
transport fails to preserve the meaning of that symmetry?

## Definition

Let \(A,B,T\in M_n(\mathbb C)\), where \(A\) is the source action, \(B\) is the target action, and
\(T\) is a proposed transport. Define the recognition defect
\[
\Delta_{A,B}(T)=BT-TA.                                      \tag{1}
\]
It vanishes exactly when \(T\) intertwines the two endpoint actions.

## Theorem

For \(A,B,C,S,T\in M_n(\mathbb C)\),
\[
\Delta_{A,C}(ST)
=\Delta_{B,C}(S)T+S\Delta_{A,B}(T).                         \tag{2}
\]

For the target identity action and source involution \(A\), let
\[
P_A=\frac{1-A}{2},
\qquad
S_A(T)=TP_A.
\]
Then
\[
\boxed{\Delta_{A,1}(T)=2S_A(T).}                            \tag{3}
\]
In particular,
\[
\Delta_{-1,1}(T)=2T,
\qquad
\Delta_{1,1}(T)=0.                                         \tag{4}
\]

Equation `(1)` is the matrix realization of the already formalized `eventSeamDefect`.

## Proof

Direct expansion gives
\[
\begin{aligned}
\Delta_{B,C}(S)T+S\Delta_{A,B}(T)
&=(CS-SB)T+S(BT-TA)\\
&=CST-SBT+SBT-STA\\
&=CST-STA\\
&=\Delta_{A,C}(ST),
\end{aligned}
\]
which proves `(2)`.

For `(3)`,
\[
\Delta_{A,1}(T)
=T-TA
=T(1-A)
=2T\frac{1-A}{2}
=2S_A(T).
\]
Putting \(A=-1\) and \(A=1\) gives `(4)`. \(\square\)

## Exact exceptional reading

The existing representation-fracture corpus independently supplies:

- a six-direction sector on which the relevant source and target central actions agree; and
- a four-direction quaternionic sector on which the source central action is \(-1\) and target
  central action is \(+1\).

Equations `(3)`--`(4)` therefore say that recognition defect vanishes on the shared six-sector and
is twice the transported map on the changed four-sector. Combined with the existing exact
rank-four record theorem, the symmetry-transmuting component is not a small perturbation: it
occupies the complete complementary event support.

This is only an exact algebraic shadow. It does not prove that the source action is weak isospin,
that the target action is causal frame symmetry, that transport is an objective event, or that
recognition defect is a force.

## Novelty boundary

Equations `(1)`--`(2)` are the ordinary failure-to-intertwine operator and its covariant Leibniz
law. Equation `(3)` is elementary involution-projector algebra. None is new mathematics.

The possible physical discovery remains the source law that:

1. selects the two nonconjugate endpoint actions;
2. creates rather than supplies \(T\);
3. makes the four-sector an external causal identity;
4. composes these event-created identities into gravity; and
5. derives exactly the Standard Model internal responses and one finite prediction.

## Formal certificate

Lean module:
`formal/GaloisForLFunctions/HTGeometry/EventSymmetryRecognitionDefect.lean`.

Unconditional declarations:

- `eventSymmetryRecognitionDefect`;
- `eventSymmetryRecognitionDefect_compose`;
- `eventSymmetryRecognitionDefect_target_identity`;
- `eventSymmetryRecognitionDefect_source_neg_identity`;
- `eventSymmetryRecognitionDefect_source_identity`; and
- `eventSymmetryRecognitionDefect_toLin'`.

Verification:

- direct foreground check:
  `lake env lean GaloisForLFunctions/HTGeometry/EventSymmetryRecognitionDefect.lean`;
- final module audit:
  `lake build GaloisForLFunctions.HTGeometry.EventSymmetryRecognitionDefect`;
- result: `2953/2953` jobs built successfully; and
- printed axioms for all five theorems are exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
