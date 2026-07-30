# Three projective-source directions do not carry colour SU(3)

- **ID:** `projective-source-color-symmetry-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SYMMETRY NO-GO / NOT NEW MATHEMATICS
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [PARENT ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NO PHYSICS PROVED]`
- **Live parent:** `../../1-in-progress/projective-source-square-universal-law.md`
- **Retired identification:** `../../5-failed/projective-source-directions-are-color.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveSourceColorSymmetryNoGo.lean`
- **Statement:** The three Pauli/quaternion directions of a projective binary source square cannot
  themselves be a colour fundamental with full fixed-composition `SU(3)` symmetry.

## Question

A nontrivial projective completion of two binary source changes produces a two-dimensional
irreducible sector and three nonidentity directions. Assigning one sector vector to each direction
gives a vector-space census

\[
\operatorname{Map}(V_4\setminus\{1\},\mathbb C^2)\cong M_{3,2}(\mathbb C).
\tag{CN.1}
\]

The tempting jump was to call the three directions colour and the left `U(3)` frame ambiguity its
gauge symmetry. But the directions have more structure than a three-dimensional vector space:
Pauli/quaternion multiplication gives them a bracket. Does full `SU(3)` preserve it?

No.

## Exact no-go theorem

On \(\mathbb C^3\), write the source-composition bracket as

\[
[x,y]=
\begin{pmatrix}
x_1y_2-x_2y_1\\
x_2y_0-x_0y_2\\
x_0y_1-x_1y_0
\end{pmatrix}.
\tag{CN.2}
\]

Let

\[
U=\operatorname{diag}(i,-i,1).
\tag{CN.3}
\]

### Theorem

`[PROVED HERE]`

\[
U^\dagger U=I,\qquad \det U=1,
\tag{CN.4}
\]

but there exist \(x,y\in\mathbb C^3\) such that

\[
U[x,y]\ne[Ux,Uy].
\tag{CN.5}
\]

Therefore the determinant-one unitary group is not a symmetry group of the fixed three-source
composition law.

### Proof

Take \(x=e_1\) and \(y=e_2\). Then \([e_1,e_2]=e_0\), so

\[
U[e_1,e_2]=ie_0.
\tag{CN.6}
\]

But \(Ue_1=-ie_1\) and \(Ue_2=e_2\), hence bilinearity gives

\[
[Ue_1,Ue_2]=-i[e_1,e_2]=-ie_0.
\tag{CN.7}
\]

Since \(i\ne-i\), equations `(CN.6)` and `(CN.7)` differ. Direct diagonal multiplication proves
`(CN.4)`. \(\square\)

## Strongest positive survivor

The theorem does not destroy the \(3\times2\) vector-space census or the existing Gram-orbit
theorems. It separates three structures that had been silently identified:

1. **source directions:** three basis directions with a fixed composition tensor;
2. **consequence amplitudes:** a three-dimensional complex multiplicity space; and
3. **frame covariance:** basis changes acting on amplitudes and, if present, on their composition
   tensor.

Full `SU(3)` can survive only through one of two mathematically explicit repairs:

- **independent multiplicity:** colour acts on a consequence space not identified with the fixed
  source bracket; or
- **covariant composition:** the bracket tensor is part of the field and transforms with the
  frame, rather than remaining a fixed invariant tensor.

The second option suggests a sharper universal object. Gauge curvature would measure failure to
glue both consequence frames and their local composition tensors. A fixed Pauli bracket is then a
gauge choice or a special phase, not the universal colour law.

The exact proved survivor is deliberately narrower: the fixed-bracket automorphism group is a
proper subgroup of determinant-one unitaries.

Lean also closes the covariant-composition repair at the finite algebraic level. Define

\[
[a,b]_U=U[U^\dagger a,U^\dagger b].
\tag{CN.8}
\]

For every unitary \(U\),

\[
[Ux,Uy]_U=U[x,y].
\tag{CN.9}
\]

For the explicit witness `(CN.3)`, this transported bracket is genuinely different from the
original bracket. Thus the repair is substantive: arbitrary unitary frames act exactly when the
composition tensor moves with them. Identifying the fixed-bracket subgroup and proving whether
physics forces fixed or covariant composition remain open.

## Why this matters physically

Equal regular \(3\times2\) Gram records form one left `SU(3)` orbit. That is a true theorem about
the event carrier. It does not say `SU(3)` preserves the multiplication of the three labels used
to construct that carrier. Gram-frame equivalence and source-composition symmetry are different
claims.

This distinction blocks a common unification shortcut:

```text
three source directions
  -/-> colour SU(3) as fixed source automorphisms.
```

Any universal-law derivation of colour must now explain why physical transformations may change
the source-composition frame covariantly, or why colour is a distinct consequence multiplicity.

## Lean status

Lean proves:

- definition `(CN.2)`;
- unitarity and determinant one of `(CN.3)`;
- explicit bracket non-equivariance on \((e_1,e_2)\); and
- the packaged existential no-go;
- exact equivariance of the transported bracket `(CN.8)`; and
- nontriviality of that transported bracket for the no-go witness.

No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computation is used.

## Novelty and scope

This is standard finite-dimensional Lie/representation algebra. The bracket in `(CN.2)` is the
complex-bilinear cross-product bracket, and its automorphisms are much more rigid than arbitrary
unitary frame changes. No mathematical or physical novelty is claimed.

The research contribution is diagnostic: it falsifies one proposed bridge in the corpus before it
could be promoted into a physical claim, and exposes the composition tensor as missing dynamical
data in the candidate universal law.
