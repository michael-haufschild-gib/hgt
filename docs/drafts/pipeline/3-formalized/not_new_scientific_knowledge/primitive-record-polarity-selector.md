# Source polarity selects the paired quadratic successor record

- **ID:** primitive-record-polarity-selector
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Parent:** `primitive-record-quadratic-successor-classification.md`
- **Statement:** On a two-channel primitive record, symmetry and oddness under the
  retained/created source polarity uniquely select the nondegenerate paired projective tensor
  orbit.
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/PrimitiveRecordPolaritySelector.lean`

## Goal

Repair the first finite nonuniqueness obstruction. Primitive data alone admit inequivalent
rank-one and rank-two higher-record laws. Test whether a datum already present in the
involution-selected event source can select one without importing the successor law.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure finite model, exact attack
- [x] complete paper proof `[PROVED HERE]`
- [x] unconditional Lean theorem `odd_symmetric_nonzero_projectivelyCongruent_pair`
- [x] final module build, generated index, and axiom audit
- [ ] physical source theorem deriving polarity and oddness
- [ ] higher-arity extension

## Setup

Let \(k\) be a characteristic-zero field and let \(P=k e_+\oplus k e_-\). The involution

\[
J=\begin{pmatrix}1&0\\0&-1\end{pmatrix}
\]

labels one primitive direction as retained and the other as created. A symmetric first
higher-record tensor is a matrix

\[
q=\begin{pmatrix}a&b\\b&d\end{pmatrix}.
\]

Say that \(q\) is **source-odd** when

\[
J^{\mathsf T}qJ=-q.                                             \tag{P1}
\]

Oddness says that the new tensor transfers across retained/created polarity; it has no
self-sector.

## Polarity-selection theorem

`[PROVED HERE]`

If \(q\) is symmetric and satisfies `(P1)`, then

\[
q=b\begin{pmatrix}0&1\\1&0\end{pmatrix}.                        \tag{P2}
\]

If \(q\ne0\), then \(b\ne0\), so \(q\) lies in the single projective congruence orbit of the
rank-two paired tensor. In particular, the rank-one self tensor

\[
\begin{pmatrix}0&0\\0&1\end{pmatrix}
\]

is excluded.

### Proof

Direct multiplication gives

\[
J^{\mathsf T}qJ=
\begin{pmatrix}a&-b\\-b&d\end{pmatrix}.
\]

Comparing with \(-q\) gives \(a=-a\) and \(d=-d\). Characteristic zero implies
\(a=d=0\), while the two off-diagonal equations are automatic. Symmetry identifies the two
cross-coefficients, proving `(P2)`. If \(q\ne0\), its remaining coefficient \(b\) is nonzero;
rescaling the one-dimensional top record layer removes \(b\). This is exactly projective
congruence.

## Lean certificate

`[LEAN-PROVED]`

Module:
`GaloisForLFunctions.HTGeometry.PrimitiveRecordPolaritySelector`.

Exact declarations:

- `recordPolarityMatrix`
- `recordPolarityMatrix_transpose`
- `odd_symmetric_record_eq_smul_pair`
- `odd_symmetric_nonzero_projectivelyCongruent_pair`

The proof is symbolic finite linear algebra. It uses no numerical experiment, `sorry`, `admit`,
axiom declaration, opaque proof, unsafe declaration, or computation-based decision procedure.
Final audit:

```text
lake build GaloisForLFunctions.HTGeometry.PrimitiveRecordPolaritySelector
✔ Built GaloisForLFunctions.HTGeometry.PrimitiveRecordPolaritySelector
```

`#print axioms` reports only Lean/mathlib's standard `propext`, `Classical.choice`, and
`Quot.sound`.

## Scientific meaning

This is the first finite source selector that survives the primitive nonuniqueness attack:

```text
primitive obstruction alone
  -> rank-one or rank-two higher law: nonunique;

primitive obstruction + retained/created polarity + source oddness
  -> paired cross-law only: unique projective orbit.
```

Existing involution event machinery already supplies the algebraic retained/created grading and
proves that every law splits into even self-sectors and odd reciprocal transfer sectors. Thus
`(P1)` is not invented solely to fit the matrix. What remains unproved is the physical statement
that the first successor-generating record must occupy the odd sector and be nonzero.

The theorem also exposes a possible reason gravity and gauge interaction cannot be self-laws of
independent sectors: the generating tensor is forced to pair what was retained with what was
created. Interaction is cross-polarity composition.

## Hostile audit

### Is the mathematics new?

No. Classification of a \(2\times2\) symmetric matrix under an involution is elementary
representation theory. Door grade: `[BRIDGE]`.

### Does it solve higher-record selection?

No. It selects only \(q_2\) in the smallest balanced two-channel truncation. In higher dimension,
odd tensors are off-diagonal pairings and still have rank strata. A perfect-pairing or
source-minimality theorem is needed to select the full-rank orbit. Ternary and higher tensors
\(q_3,q_4,\ldots\) remain completely open.

### Does it derive physics?

No. A supplied involution, a supplied oddness condition, and a nonzero tensor do not derive
quantum theory, time, spacetime, gravity, gauge symmetry, or a continuum action. The physical
claim begins only if source completeness forces these hypotheses and recursively forces every
higher tensor.

## Strongest positive survivor

The first higher record is not arbitrary once it is required to **change actuality polarity**.
In the minimal balanced case, source polarity converts nonuniqueness into a unique paired orbit.
This suggests a recursive selector:

> successor-generating \(n\)-records are precisely source-minimal tensors of the parity that
> transfers information between what an event retained and what it created.

That sentence is a conjecture beyond \(n=2\).

## Log

- 2026-07-29 — primitive nonselection exposed two inequivalent quadratic successor laws.
- 2026-07-29 — source involution reinterpreted as a retained/created polarity.
- 2026-07-29 — paper- and Lean-proved that symmetric polarity-odd tensors have one nonzero
  projective orbit in the minimal two-channel model.
- 2026-07-29 — final target build and axiom audit passed; moved to Stage 3 as
  `not_new_scientific_knowledge`.
