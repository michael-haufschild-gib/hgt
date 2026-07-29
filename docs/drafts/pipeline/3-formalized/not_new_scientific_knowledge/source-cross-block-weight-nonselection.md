# Total reciprocal-square weight does not select a higher cross block

- **ID:** source-cross-block-weight-nonselection
- **Stage:** 3-formalized
- **Type:** THEOREM + NO-GO (paper + Lean)
- **Parent:** `minimal-source-quadratic-square-isotropy.md`
- **Statement:** At the next balanced rank, full support and fixed total reciprocal-square weight
  admit biunitarily inequivalent cross-polarity blocks. Source calibration must determine a full
  singular spectrum, not one norm.
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/SourceCrossBlockWeightNonselection.lean`

## Goal

Test whether the minimal common scalar can be generalized by fixing one total positive weight,
for example trace of \(D^\dagger D\), after requiring full-rank cross-polarity transfer.

## Gates

- [x] exact invariant
- [x] explicit full-rank equal-weight counterexample
- [x] complete paper proof `[PROVED HERE]`
- [x] unconditional Lean theorem
  `weightedCrossBlocks_not_biunitarilyEquivalent`
- [x] final target build and axiom audit
- [ ] generated index and project-wide lint
- [ ] source selector for the full singular spectrum

## Biunitary equivalence

For \(B,C\in M_2(\mathbb C)\), write \(B\sim_{\rm biu}C\) if

\[
C=UBV
\]

for unitary \(U,V\). This is the frame equivalence of a cross block under independent unitary
changes on its two graded sides.

If \(B\sim_{\rm biu}C\), then

\[
|\det B|^2=|\det C|^2.                                       \tag{CB1}
\]

Indeed,

\[
|\det(UBV)|^2
=|\det U|^2|\det B|^2|\det V|^2
=|\det B|^2.
\]

## Equal-weight nonselection theorem

`[PROVED HERE]`

Set

\[
B_1=\begin{pmatrix}1&0\\0&8\end{pmatrix},
\qquad
B_2=\begin{pmatrix}4&0\\0&7\end{pmatrix}.                    \tag{CB2}
\]

Both are invertible and

\[
\operatorname{tr}(B_1^\dagger B_1)
=1^2+8^2
=65
=4^2+7^2
=\operatorname{tr}(B_2^\dagger B_2).                         \tag{CB3}
\]

But

\[
|\det B_1|^2=64,\qquad
|\det B_2|^2=784.                                             \tag{CB4}
\]

By `(CB1)`, \(B_1\not\sim_{\rm biu}B_2\).

## Exact killing mechanism

The following data remain insufficient:

- cross-polarity support;
- nonzero transfer;
- full rank;
- fixed total reciprocal-square trace; and
- independent-unitary frame invariance.

They do not determine the distribution of positive weight among singular directions.

Thus replacing projective normalization by one Frobenius/Hilbert--Schmidt norm does not solve the
physical calibration problem.

## Strongest positive survivor

For a higher cross block, invariant physical weight is not one number. It is at least the complete
singular spectrum—or equivalently, all spectral moments of \(B^\dagger B\) in finite dimension.

The first two independent invariants in this \(2\times2\) example are

\[
\operatorname{tr}(B^\dagger B),\qquad |\det B|^2.
\]

One fixes total weight; the other measures its distribution.

## Lean certificate

`[LEAN-PROVED]`

Declarations:

- `BiunitarilyEquivalent`
- `detNormSq_eq_of_biunitarilyEquivalent`
- `firstWeightedCrossBlock`
- `secondWeightedCrossBlock`
- `firstWeightedCrossBlock_det`
- `secondWeightedCrossBlock_det`
- `weightedCrossBlocks_equal_totalSquare`
- `weightedCrossBlocks_not_biunitarilyEquivalent`

No `sorry`, `admit`, axiom declaration, opaque declaration, unsafe declaration, or unproved
hypothesis occurs.
Final audit:

```text
lake build GaloisForLFunctions.HTGeometry.SourceCrossBlockWeightNonselection
✔ Built GaloisForLFunctions.HTGeometry.SourceCrossBlockWeightNonselection
Build completed successfully (2953 jobs).
```

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile novelty audit

This is a concrete singular-value decomposition consequence. Door grade: `[BRIDGE]`.

It does not derive any physical singular value, force coupling, or dimension.

## Consequence for source-generated ternary reciprocity

Positive bar-to-ternary reconstruction must preserve and derive more than:

- support projection;
- projective orbit;
- rank; or
- one norm.

It must source-select the entire calibrated spectral measure of every irreducible cross block,
then relate those measures across gravity, gauge, Higgs, and matter sectors.

## Log

- 2026-07-29 — constructed equal-total-weight full-rank cross blocks.
- 2026-07-29 — proved determinant modulus obstructs biunitary equivalence.
- 2026-07-29 — promoted full singular-spectrum selection to mandatory source law.
- 2026-07-29 — final target build and axiom audit passed.
