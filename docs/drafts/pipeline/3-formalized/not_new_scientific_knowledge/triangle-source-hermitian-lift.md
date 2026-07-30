# The unlabeled triangle forces a conjugate-complete Hermitian lift

- **ID:** `triangle-source-hermitian-lift`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE RECONSTRUCTION / COMPLEX-SCALAR AND HERMITIAN BRIDGE
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVEN] [CLASSICAL REPRESENTATION THEORY]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/triangle-fact-orientation-transmutation.md`
- **Formal dependencies:**
  `source-ordered-pair-complex-structure.md`,
  `no-outside-quadratic-witness-descent.md`,
  and `event-square-polarization-law.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/TriangleSourceHermitianLift.lean`
- **Statement:** The full source symmetry of the unlabeled triangle canonically generates a
  complex phase algebra with conjugation, forces both conjugate phase directions to remain, and
  gives the free complex exact sequence whose deformation carrier is
  \(M_{3,2}(\mathbb C)\) with its source-counting Hermitian Gram square.

## Goal

Close the finite sign-square to Hermitian-square gap without supplying complex scalars, a chosen
orientation, or an arbitrary metric. The theorem must explain why the two real account modes
become a complex doublet rather than one chosen complex line.

## Gates

- [x] 0 → 1: explicit source representation, no-orientation criterion, and hostile alternatives
- [x] 1 → 2: dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3: exact source matrices, phase algebra, conjugation, metric rigidity, and carrier
  formalized in Lean
- [ ] 3 → 4: supporting theorem only; no independent Nature claim

## Source representation

Let
\[
Q_{\mathbb R}
=\{(x_0,x_1,x_2)\in\mathbb R^3:x_0+x_1+x_2=0\}
\]
be the two-dimensional independent-account plane of the triangle. In coordinates
\[
(x,y)\longmapsto(x,y,-x-y),
\tag{HL1}
\]
the three-cycle and one transposition act by
\[
R=
\begin{pmatrix}
-1&-1\\
1&0
\end{pmatrix},
\qquad
T=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
\tag{HL2}
\]
They satisfy
\[
R^3=I,\qquad T^2=I,\qquad TRT=R^2=R^{-1}.
\tag{HL3}
\]

Thus \(R,T\) give the standard real representation of
\[
S_3=A_3\rtimes\mathbb Z_2.
\]

## Theorem A: source phase algebra and conjugation

`[PROVED HERE]`

Define the centered rotation
\[
K=2R+I
=
\begin{pmatrix}
-1&-2\\
2&1
\end{pmatrix}.
\tag{HL4}
\]
Then
\[
\boxed{K^2=-3I,\qquad TKT=-K.}
\tag{HL5}
\]

The centralizer of the orientation-preserving source subgroup is
\[
\operatorname{Cent}_{M_2(\mathbb R)}(R)
=
\{aI+bK:a,b\in\mathbb R\}.
\tag{HL6}
\]
Its multiplication law is
\[
(aI+bK)(cI+dK)
=(ac-3bd)I+(ad+bc)K.
\tag{HL7}
\]
Hence
\[
\operatorname{Cent}(A_3|Q_{\mathbb R})
\cong\mathbb C
\tag{HL8}
\]
as a real unital algebra, via
\[
aI+bK\longmapsto a+i\sqrt3\,b.
\]

The odd source relabeling acts by
\[
T(aI+bK)T=aI-bK,
\tag{HL9}
\]
which is exactly complex conjugation under `(HL8)`. Therefore the unlabeled source generates the
complex algebra together with its real structure but does not choose a sign of \(i\).

### Proof

Direct multiplication gives `(HL3)` and `(HL5)`. Write
\[
A=\begin{pmatrix}p&q\\r&s\end{pmatrix}.
\]
The equation \(AR=RA\) is equivalent to
\[
r=-q,\qquad s=p-q.
\]
Taking
\[
b=-q/2,\qquad a=p-q/2
\]
gives \(A=aI+bK\), uniquely. This proves `(HL6)`. Equation `(HL7)` follows from
\(K^2=-3I\), and `(HL9)` follows from \(TKT=-K\). \(\square\)

## Theorem B: source-counting metric and dagger are rigid

`[PROVED HERE]`

The counting inner product of the three unlabeled source atoms restricts through `(HL1)` to
\[
G=
\begin{pmatrix}
2&1\\
1&2
\end{pmatrix},
\qquad
(x,y)G(x,y)^{\mathsf T}
=x^2+y^2+(x+y)^2.
\tag{HL10}
\]
It is positive definite and source invariant:
\[
R^{\mathsf T}GR=G,\qquad T^{\mathsf T}GT=G.
\tag{HL11}
\]

Every real symmetric bilinear form \(H\) invariant under both \(R\) and \(T\) is a scalar
multiple of \(G\):
\[
R^{\mathsf T}HR=H,\quad T^{\mathsf T}HT=H
\quad\Longrightarrow\quad
H=cG
\tag{HL12}
\]
for a unique \(c\in\mathbb R\). It is positive definite exactly when \(c>0\).

Moreover
\[
K^{\mathsf T}G=-GK.
\tag{HL13}
\]
Therefore the adjoint induced by \(G\) restricts on the phase algebra to
\[
(aI+bK)^\dagger_G=aI-bK,
\tag{HL14}
\]
and
\[
(aI+bK)^\dagger_G(aI+bK)
=(a^2+3b^2)I.
\tag{HL15}
\]
Thus the same odd relabeling that reverses orientation supplies complex conjugation, the source
counting form supplies dagger, and the corresponding scalar norm is positive.

### Proof

Equation `(HL10)` is the squared Euclidean norm of \((x,y,-x-y)\). Direct multiplication proves
`(HL11)` and `(HL13)`.

Write a symmetric form as
\[
H=\begin{pmatrix}p&q\\q&s\end{pmatrix}.
\]
The \(T\)-invariance equation gives \(s=p\). Substitution into the \(R\)-invariance equation gives
\(p=2q\), hence \(H=qG\). This proves `(HL12)`. Equations `(HL14)`--`(HL15)` follow from
`(HL13)` and \(K^2=-3I\). \(\square\)

## Theorem C: full source symmetry forces the complex doublet

`[PROVED HERE]`

Complexify the account plane:
\[
Q_{\mathbb C}=\mathbb C\otimes_{\mathbb R}Q_{\mathbb R}.
\tag{HL16}
\]
The rotation \(R\) has the two distinct eigenvalues
\[
\omega=e^{2\pi i/3},\qquad\bar\omega=\omega^{-1}.
\]
Its two eigenlines are the two choices of complex orientation. Relation \(TRT=R^{-1}\) makes
\(T\) exchange those lines. Consequently:

1. neither eigenline is invariant under the full unlabeled-source group \(S_3\);
2. \(Q_{\mathbb C}\) has no nonzero proper \(S_3\)-invariant complex subspace; and
3. retaining only one complex line chooses an orientation not supplied by the source.

Therefore the least complex account carrier preserving every source automorphism is the full
complex doublet \(Q_{\mathbb C}\), not one phase eigenline.

### Proof

Since \(R^3=I\) and \(R\ne I\), its minimal polynomial on the account plane is
\[
z^2+z+1=(z-\omega)(z-\bar\omega),
\]
so the stated eigenspace decomposition holds. If \(Rv=\omega v\), then
\[
R(Tv)=TR^{-1}v=\bar\omega\,Tv.
\]
Thus \(T\) exchanges the two eigenspaces. Any nonzero invariant complex line would be one
\(R\)-eigenline and would fail \(T\)-invariance. \(\square\)

## Theorem D: free exact Hermitian lift

`[PROVED HERE]`

The real triangle sequence is
\[
0\longrightarrow O_{\mathbb R}
\longrightarrow E_{\mathbb R}
\longrightarrow Q_{\mathbb R}
\longrightarrow0
\tag{HL17}
\]
with real ranks \(1,3,2\). Extension of scalars along
\(\mathbb R\to\mathbb C\) is exact, so
\[
0\longrightarrow O_{\mathbb C}
\longrightarrow E_{\mathbb C}
\longrightarrow Q_{\mathbb C}
\longrightarrow0
\tag{HL18}
\]
has complex ranks
\[
1\longrightarrow3\longrightarrow2.
\tag{HL19}
\]

This is also the free complex-linear completion: for every complex vector space \(W\), every real
linear map \(V\to W\) extends uniquely to a complex-linear map
\[
\mathbb C\otimes_{\mathbb R}V\to W.
\tag{HL20}
\]
It therefore adds scalar closure but no source-independent quotient relation. The full-source
irreducibility in Theorem C forbids collapsing \(Q_{\mathbb C}\) to one conjugate phase line.

The complete linear deformation carrier of the source comparison map is consequently
\[
\boxed{
\operatorname{Hom}_{\mathbb C}(Q_{\mathbb C},E_{\mathbb C})
\cong M_{3,2}(\mathbb C).
}
\tag{HL21}
\]

Counting inner products on the vertex and edge atoms, extended sesquilinearly, give canonical
Hermitian forms. In source-orthonormal frames an event \(X\) has the positive public record
\[
\boxed{\Gamma(X)=X^\dagger X\in H_2(\mathbb C)_+.}
\tag{HL22}
\]
The existing continuous equivariant Gram-rigidity theorem proves that, up to nonnegative scale,
`(HL22)` is the unique nonzero continuous Hermitian-valued report invariant under target-unitary
frame changes, covariant under account-frame changes, and positive on every event.

### Proof

Field extension is flat, hence preserves exact sequences. The tensor--Hom adjunction proves
`(HL20)`. Finite-dimensional base change preserves ranks, proving `(HL18)`--`(HL21)`.
Sesquilinear extension of a positive real counting form is a positive Hermitian form. Finally,
\[
v^\dagger X^\dagger Xv=\lVert Xv\rVert^2\ge0,
\]
which proves `(HL22)`. The stated uniqueness is exactly the already paper- and Lean-proved
continuous equivariant Gram-rigidity theorem. \(\square\)

## What is now closed

The finite lift no longer has the earlier unexplained steps

```text
choose C;
choose one complex orientation;
choose a dagger;
choose positive Gram.
```

It now has one source dependency chain:

```text
unlabeled triangle
  -> orientation-preserving rotation algebra C
  -> odd relabeling acts as conjugation
  -> counting metric makes conjugation the adjoint
  -> full S3 symmetry retains both conjugate phase directions
  -> free exact complex ranks 1 -> 3 -> 2
  -> deformation carrier M₃,₂(C)
  -> positive Hermitian Gram public record.
```

## Hostile boundary

All mathematical ingredients are established:

- standard \(S_3\) representation theory;
- real two-dimensional phase/Clifford algebra;
- invariant inner-product classification;
- exact scalar extension;
- Hermitian Gram positivity; and
- equivariant Gram rigidity.

The theorem closes the **finite Hermitian lift**, not physical transfer to continuum reality. It
does not prove:

- that every physical primitive is the triangle self-witness source;
- that every linear deformation in `(HL21)` is physically realized;
- that the Gram report is causal spacetime rather than another positive record;
- Born normalization or event statistics;
- composition of neighboring event carriers;
- a source-generated connection, curvature, Einstein dynamics, or gauge forces; or
- any parameter-free observation.

Those are no longer allowed to be hidden inside “derive the Hermitian lift.” The next theorem must
start from the closed carrier `(HL21)`--`(HL22)` and derive its physical interpretation and
composition.

## Lean certificate

`[LEAN-PROVEN]`

The module formalizes:

- triangle cycle/reflection relations \(R^3=T^2=I\), \(TRT=R^2\);
- centered phase generator \(K\), \(K^2=-3I\), and \(TKT=-K\);
- exact phase-scalar multiplication and reflection conjugation;
- complete centralizer classifications for \(A_3\) and \(S_3\);
- absence of a nonzero common eigenvector and of a nontrivial invariant idempotent;
- source-counting Gram invariance, positive definiteness, and phase skew-adjointness;
- uniqueness of every invariant symmetric form up to scale;
- uniqueness of every invariant positive metric on one positive ray;
- positive phase norm \(a^2+3b^2\);
- complex triangle exactness at edge and account layers; and
- positive semidefiniteness of the \(3\times2\) Hermitian Gram report.

Capstone declarations:

- `triangleAccount_no_nonzero_common_eigenvector`
- `triangleAccount_sourceInvariant_idempotent_eq_zero_or_one`
- `triangleAccount_invariant_posDef_eq_pos_smul_countingGram`
- `triangleComplexEdgeBoundary_eq_zero_iff`
- `triangleComplexVertexAugmentation_eq_zero_iff`
- `triangleWitnessGram_posSemidef`

Foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/TriangleSourceHermitianLift.lean
lake build GaloisForLFunctions.HTGeometry.TriangleSourceHermitianLift
```

The final target build completed all 8,668 jobs. `#print axioms` for the irreducibility,
no-spectator, positive-metric-rigidity, and Hermitian-Gram capstones reports only project-baseline
`propext`, `Classical.choice`, and `Quot.sound`.

## Physical law exposed

`[CONJECTURE — NOT SCIENTIFIC KNOWLEDGE]`

> **The universe has no outside. Reality must witness itself. What it cannot choose, it must
> retain with its conjugate; what it can make public is their positive square.**

The source theorem now explains the conjugate pair and the positive square. The remaining
worldview jump is:

> **Quantum alternatives are the conjugate-complete square roots of public causal future.**

## Log

- 2026-07-30 — connected triangle source symmetry to the previously isolated ordered-pair complex
  phase algebra.
- 2026-07-30 — found the missing doublet selector: odd source relabeling exchanges the two phase
  eigenlines, so choosing either one imports an outside orientation.
- 2026-07-30 — proved source-counting metric rigidity, induced dagger, positive scalar norm, free
  exact complexification, and the \(M_{3,2}(\mathbb C)\) Hermitian carrier on paper.
- 2026-07-30 — formalized source phase/conjugation, full-source irreducibility, no-spectator
  projector rigidity, positive metric-ray uniqueness, complex exactness, and positive Hermitian
  Gram lift; direct check, final target build, and axiom audit passed.
