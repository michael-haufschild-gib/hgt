# Source colligation derives the minimal paired quadratic transfer

- **ID:** source-colligation-quadratic-transfer-selector
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Parent:** `primitive-record-polarity-selector.md`
- **Statement:** Symmetrizing the canonical odd sector of a symmetric source involution
  automatically produces a symmetric source-odd quadratic transfer; in the minimal nonzero
  two-channel case it lies in the unique paired projective orbit.
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/SourceQuadraticTransferSelector.lean`

## Goal

Remove one assumed hypothesis from the primitive-record polarity selector. The preceding theorem
assumed that the first symmetric successor tensor was odd under retained/created polarity. Here
oddness must follow from a supplied source event colligation before any successor composition law
is chosen.

## Gates

- [x] source-pure finite statement
- [x] complete paper proof `[PROVED HERE]`
- [x] unconditional Lean theorem
  `sourceQuadraticTransfer_nonzero_projectivelyCongruent_pair`
- [x] final target build and axiom audit
- [ ] physical theorem selecting a nonzero objective event transfer
- [ ] higher-rank and higher-arity source selector
- [x] generated declaration index
- [ ] project-wide lint (blocked by unrelated pre-existing unreachable modules)

## Setup

Let \(A,T\in M_n(\mathbb C)\), with

\[
A^2=I,\qquad A^{\mathsf T}=A.
\]

The source involution canonically projects \(T\) onto its odd transfer sector

\[
O_A(T)=\frac12(T-ATA).
\]

Define the symmetric source quadratic transfer

\[
Q_A(T)=\frac12\left(O_A(T)+O_A(T)^{\mathsf T}\right).          \tag{SQT1}
\]

This definition uses only the source grading and supplied event law. It does not inspect a desired
successor law.

## Source-derived quadratic transfer theorem

`[PROVED HERE]`

For every symmetric involution \(A\):

\[
Q_A(T)^{\mathsf T}=Q_A(T),\qquad
AQ_A(T)A=-Q_A(T).                                             \tag{SQT2}
\]

For the minimal retained/created polarity

\[
J=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\]

every nonzero \(Q_J(T)\) is projectively congruent to

\[
\begin{pmatrix}0&1\\1&0\end{pmatrix}.                         \tag{SQT3}
\]

### Proof

The first identity in `(SQT2)` is immediate from `(SQT1)`. Since \(A^2=I\),

\[
AO_A(T)A
=\frac12(ATA-A^2TA^2)
=-O_A(T).
\]

Transpose this identity and use \(A^{\mathsf T}=A\) to obtain

\[
AO_A(T)^{\mathsf T}A=-O_A(T)^{\mathsf T}.
\]

Adding both identities proves source oddness of \(Q_A(T)\).

For \(A=J\), write the symmetric matrix as

\[
Q_J(T)=\begin{pmatrix}a&b\\b&d\end{pmatrix}.
\]

Equation `(SQT2)` gives \(a=-a\) and \(d=-d\), hence \(a=d=0\). If the matrix is
nonzero, \(b\ne0\), and projective rescaling gives `(SQT3)`.

## Lean certificate

`[LEAN-PROVED]`

Exact declarations:

- `sourceQuadraticTransfer`
- `sourceQuadraticTransfer_transpose`
- `sourceQuadraticTransfer_conjugate`
- `recordPolarityMatrix_mul_self_complex`
- `sourceQuadraticTransfer_nonzero_projectivelyCongruent_pair`

Direct foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/SourceQuadraticTransferSelector.lean
lake build GaloisForLFunctions.HTGeometry.SourceOddPositivitySquareLaw
```

No `sorry`, `admit`, axiom declaration, opaque declaration, unsafe declaration, or
computation-based proof appears in the module.
The final target build completed all 3,182 jobs. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Hostile audit

### Is this new mathematics?

No. Projection to the odd component of a \(\mathbb Z/2\)-graded matrix and symmetrization are
elementary graded linear algebra. Door grade: `[BRIDGE]`.

### What assumption was removed?

Oddness is no longer independently inserted into the minimal quadratic selector. It follows from
the canonical odd projection of the source colligation.

### What assumptions remain?

The theorem still supplies \(A\), \(T\), the interpretation of the two eigenspaces, and
nonvanishing of \(Q_A(T)\). It does not show that objective physical events select these data or
that the extracted quadratic form generates anything.

### Circularity boundary

The construction is source-pure only if \(T\) is an independently defined complete event
colligation. If \(T\) is chosen from the desired successor law, `(SQT1)` becomes a circular
repackaging and must be rejected.

## Strongest positive survivor

At quadratic depth, source colligation now supplies both ingredients that eliminate primitive
nonselection:

```text
source involution
  -> retained/created polarity;

canonical odd projection of source event
  -> source oddness;

symmetrization + nonzero
  -> unique minimal paired projective orbit.
```

The first unresolved finite hypothesis is now **nonzero physical transfer**, not oddness.

## Log

- 2026-07-29 — derived source oddness by projecting the event law before symmetrization.
- 2026-07-29 — completed paper and unconditional Lean proofs.
- 2026-07-29 — classified result as standard bridge, not new scientific knowledge.
- 2026-07-29 — final target build and axiom audit passed; generated index refreshed. Global lint
  remains red only on unrelated pre-existing unreachable modules.
