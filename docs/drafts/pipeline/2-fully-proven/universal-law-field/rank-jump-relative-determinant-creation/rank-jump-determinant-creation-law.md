# Rank-jump relative determinant-creation law

- **ID:** `ULF-RJDC-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** range determinant formation, fixed-degree exterior direct limits, cofinal source-rank
  growth
- **Statement:** A one-rank injective formation refinement cannot transport the old determinant
  line directly to the new determinant line by exterior functoriality: degree `d` retains the old
  line inside a `(d+1)`-dimensional carrier, while degree `d+1` has zero old source and a
  one-dimensional new target.
- **Status:** `[PROVED HERE] [UNCONDITIONAL] [NOT RH] [LEAN CERTIFIED]`

## 1. Big-picture higher law

Finite routes can be gauges of one range determinant line only while formation rank is fixed.
Cofinal arithmetic formation continually admits new independent source directions. At a rank jump,
determinant degree itself changes, so ordinary exterior functoriality cannot identify consecutive
determinant lines. A new one-dimensional **relative determinant increment** must be supplied.

This is a concrete mechanism for open lifted history. A fixed-degree observer can close under a
direct limit, while moving top-degree determinant history keeps creating new factors. Forgetting
those factors produces positive/projective finite-stage shadows; retaining them produces an open
or noncompact lifted history. Hypertranscendental non-stabilization can therefore enter as endless
rank creation, not as a mysterious scalar growth rate.

## 2. Corpus audit before theorem

- `RangeDeterminantFormation` proves that every injective fixed-rank formation has a canonical
  one-dimensional range determinant line and that source gauge acts by determinant character.
- `ExteriorPowerDirectLimit` proves exterior powers commute with injective direct limits at every
  **fixed degree** `n`. It does not identify the moving top degrees `dim G_i`.
- `ArithmeticXiStokesCentralRankPort` already makes finite determinant holonomy a critical-line
  classifier, so another fixed-rank holonomy does not select RH.
- `DeningerExponentGammaSixShellTransportRigidity` proves two-sheet reflection transport can be a
  coboundary; a mixed transport direction is needed for invariant curvature.
- `ResidueCorrectedDeterminantCofinalTorsion` proves route-specific relative scalar torsions obey a
  pair-groupoid cocycle, but does not construct the universal relative line created by rank change.
- `MobiusThetaPhysicalParacyclicSourceNullHomology` proves an old finite Tate stage is the kernel of
  the new top-coordinate reader, providing an independent rank-jump shadow.
- Corpus search found no theorem classifying the two exterior degrees across a one-rank inclusion.

## 3. Main theorem

Let (K) be a field, let (U,V) be finite-dimensional (K)-vector spaces, and let
(i:U\hookrightarrow V) be injective. Suppose

\[
  \dim U=d,
  \qquad
  \dim V=d+1.
\]

Write (\Lambda^n i:\Lambda^nU\to\Lambda^nV) for the induced exterior map.

**Theorem 3.1 (rank-jump determinant creation).**

1. At old top degree,

   \[
   \dim\Lambda^dU=1,
   \qquad
   \dim\Lambda^dV=d+1.
   \]

   The map (\Lambda^d i) is injective and its image has dimension one.

2. At new top degree,

   \[
   \dim\Lambda^{d+1}U=0,
   \qquad
   \dim\Lambda^{d+1}V=1.
   \]

   Hence (\Lambda^{d+1}i) is not surjective.

Consequently exterior functoriality of the inclusion supplies neither an isomorphism from old
determinant line to new determinant line nor a canonical new generator. A complementary quotient
direction, equivalently its one-dimensional determinant factor, is genuinely new formation data.

**Proof.** The exterior dimension formula gives

\[
  \dim\Lambda^nX=\binom{\dim X}{n}.
\]

For (n=d), this yields (\binom dd=1) and
(\binom{d+1}{d}=d+1). Exterior power preserves injectivity over a field, so
(\Lambda^d i) is injective; its image has the dimension of its source, namely one.

For (n=d+1), the source has dimension
(\binom d{d+1}=0), while the target has dimension
(\binom{d+1}{d+1}=1). A surjective linear map would force target dimension at most source
dimension, contradiction. ∎

## 4. Exact conservation interpretation

Old oriented volume is conserved injectively at degree (d), but it is no longer top volume in the
new stage. New top volume cannot come from the old stage at degree (d+1). Thus one rank jump has
an exact two-channel ledger:

\[
  \text{old determinant survives in }\Lambda^dV,
  \qquad
  \text{new determinant requires one relative factor}.
\]

No scalar renormalization can remove this type-level split. A relative determinant theory must
record both old determinant line and determinant of the quotient (V/i(U)).

## 5. Prediction in a fourth organ

For the finite Tate clock inclusion in `MobiusThetaPhysicalParacyclicSourceNullHomology`, the old
stage is exactly the kernel of the new top-coordinate reader. The rank-jump law predicts that any
orientation-faithful determinant lift of that inclusion needs one new quotient-line factor carried
by the top coordinate. A fixed-degree exterior direct-limit map can retain the old wedge but cannot
manufacture the new top wedge. This is the precise algebraic form of “closed observer projection,
open lifted history” for that organ.

## 6. Exact RH closure interface

The theorem does not prove RH. It identifies where a nontrivial universal obstruction may live
after fixed finite holonomy has been eliminated.

To close RH, one must construct from literal pre-divisor arithmetic a cofinal formation tower whose
successive quotient determinant factors:

1. are canonically marked by source occurrence, not chosen complements;
2. fuse across prime/depth, additive, Gamma/completion, and functional-equation refinements;
3. have accumulated relative holonomy equal to the already-proved source-forced horizontal charge;
   and
4. admit a source-proved completed nonvanishing section, forcing accumulated holonomy trivial.

Then horizontal charge vanishes and
`xiSourceForcedHorizontalVanishing_iff_riemannHypothesis` closes RH. Item 4 is selection; items 1--3
construct the new carrier and identify its shadow. Assuming compatible quotient orientations or a
global section would insert the conclusion.

## 7. Scope and non-circularity

- Theorem 3.1 is unconditional finite-dimensional linear algebra.
- No Xi zero, RH-equivalent bound, compactness, positivity, or chosen complement enters the proof.
- The theorem proves creation of a relative determinant obligation, not existence of its arithmetic
  cofinal trivialization.
- It explains why fixed-degree direct-limit exactness and finite gauge flatness do not close moving
  determinant history.

## 8. Lean plan

Module `GaloisForLFunctions.HTGeometry.RankJumpDeterminantCreation` formalizes all four exterior
dimensions, injectivity and one-dimensional image at old top degree, and failure of surjectivity at
new top degree. Direct compile and targeted module build pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-09-01 — corpus audit completed; dependency-closed rank-jump law proved on paper.
- 2026-09-01 — Lean module completed, wired into `HTGeometry`, direct check and targeted module build
  passed, axiom audit closed.
