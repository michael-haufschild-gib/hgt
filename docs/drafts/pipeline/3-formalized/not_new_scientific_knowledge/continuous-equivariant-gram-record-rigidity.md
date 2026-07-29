# Continuous equivariant causal records are scalar Gram maps

- **ID:** `continuous-equivariant-gram-record-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper; exact `3 × 2` specialization in Lean)
- **Status:** `[PAPER-PROVED] [LEAN-PROVED 3x2] [REDISCOVERED] [BRIDGE]`
- **Parent conjecture:** `../../1-in-progress/actuality-creates-future-law.md`
- **Lean module:** `formal/GaloisForLFunctions/HTGeometry/ContinuousEquivariantGramRigidity.lean`
- **Statement:** For \(n\ge k\), every continuous Hermitian-valued map on
  \(M_{n,k}(\mathbb C)\) that is left-\(U(n)\)-invariant and right-\(GL(k,\mathbb C)\)-congruence
  covariant is a unique real scalar multiple of the Gram map \(X\mapsto X^\dagger X\).

## Theorem

Let \(n,k\ge1\) with \(n\ge k\), and write
\[
\operatorname{Herm}_k
=\{H\in M_k(\mathbb C):H^\dagger=H\}.
\]
Let
\[
F:M_{n,k}(\mathbb C)\longrightarrow\operatorname{Herm}_k
\]
be continuous. Assume:

1. **left-frame invariance:** for every \(U\in U(n)\) and \(X\in M_{n,k}(\mathbb C)\),
   \[
   F(UX)=F(X);
   \tag{1}
   \]
2. **right-frame congruence covariance:** for every \(A\in GL(k,\mathbb C)\) and
   \(X\in M_{n,k}(\mathbb C)\),
   \[
   F(XA)=A^\dagger F(X)A.
   \tag{2}
   \]

Then there is a unique \(c\in\mathbb R\) such that
\[
F(X)=cX^\dagger X
\qquad\text{for every }X\in M_{n,k}(\mathbb C).
\tag{3}
\]

Moreover:

- \(F(X)\) is positive semidefinite for every \(X\) if and only if \(c\ge0\);
- if \(F\) is positive-semidefinite-valued and nonzero, then \(c>0\).

The \(3\times2\) specialization says that, up to positive scale, the colour Gram record is the
unique continuous positive record with the full source-frame symmetries required by the active
causalization conjecture.

## Proof

### 1. Value at the standard frame

Let
\[
E=
\begin{pmatrix}
I_k\\
0
\end{pmatrix}\in M_{n,k}(\mathbb C)
\tag{4}
\]
be the standard isometric inclusion and set
\[
H=F(E)\in\operatorname{Herm}_k.
\tag{5}
\]

For \(V\in U(k)\), let
\[
\widetilde V=
\begin{pmatrix}
V&0\\
0&I_{n-k}
\end{pmatrix}\in U(n).
\tag{6}
\]
Then
\[
\widetilde V E=EV.
\tag{7}
\]
Using (1), (2), and \(V^{-1}=V^\dagger\),
\[
H
=F(E)
=F(\widetilde V E)
=F(EV)
=V^\dagger H V
\qquad(V\in U(k)).
\tag{8}
\]

Thus \(H\) is fixed by conjugation under every unitary matrix. We include the elementary
centralizer argument. Conjugation by arbitrary diagonal unitary matrices forces every
off-diagonal entry of \(H\) to vanish: for \(i\ne j\), choose diagonal phases whose \(i\)- and
\(j\)-entries have unequal quotient in (8). Conjugation by permutation matrices then forces all
diagonal entries to agree. Hence
\[
H=cI_k
\tag{9}
\]
for some \(c\in\mathbb C\). Since \(H\) is Hermitian, \(c=\overline c\), so \(c\in\mathbb R\).

### 2. Every full-rank frame has the Gram value

Let \(X\in M_{n,k}(\mathbb C)\) have full column rank \(k\). Then \(X^\dagger X\) is positive
definite. Let
\[
P=(X^\dagger X)^{1/2}.
\tag{10}
\]
The positive square root is Hermitian and invertible, and
\[
P^2=X^\dagger X.
\tag{11}
\]
Define
\[
Q=XP^{-1}.
\tag{12}
\]
Because \(P=P^\dagger\),
\[
Q^\dagger Q
=P^{-1}X^\dagger XP^{-1}
=P^{-1}P^2P^{-1}
=I_k.
\tag{13}
\]
Thus the columns of \(Q\) are an orthonormal \(k\)-frame in \(\mathbb C^n\). Extend them to an
orthonormal basis of \(\mathbb C^n\). The unitary matrix \(U\in U(n)\) having that basis as its
columns satisfies
\[
UE=Q.
\tag{14}
\]
Consequently
\[
X=QP=UEP.
\tag{15}
\]
Since \(P\in GL(k,\mathbb C)\), equations (1), (2), (9), and (11) give
\[
\begin{aligned}
F(X)
&=F(UEP)\\
&=F(EP)\\
&=P^\dagger F(E)P\\
&=cP^2\\
&=cX^\dagger X.
\end{aligned}
\tag{16}
\]
This proves (3) on the full-column-rank locus.

### 3. Continuity closes every rank stratum

Full-column-rank matrices are dense in \(M_{n,k}(\mathbb C)\). For completeness, take a singular
value decomposition
\[
X=U\Sigma V^\dagger.
\tag{17}
\]
Replace every zero singular value among the first \(k\) diagonal positions by
\(\varepsilon>0\), leaving the positive singular values unchanged. The resulting
\[
X_\varepsilon=U\Sigma_\varepsilon V^\dagger
\tag{18}
\]
has full column rank and satisfies \(X_\varepsilon\to X\) as \(\varepsilon\downarrow0\).

By Step 2,
\[
F(X_\varepsilon)=cX_\varepsilon^\dagger X_\varepsilon.
\tag{19}
\]
Both sides are continuous in \(X_\varepsilon\). Taking the limit proves
\[
F(X)=cX^\dagger X
\tag{20}
\]
for arbitrary \(X\), including every singular rank stratum.

### 4. Uniqueness and positivity

Since \(E^\dagger E=I_k\), equation (3) gives
\[
F(E)=cI_k.
\tag{21}
\]
Therefore \(c\) is unique.

If \(F\) is positive-semidefinite-valued, then (21) implies \(cI_k\ge0\), hence \(c\ge0\).
Conversely, if \(c\ge0\), then \(cX^\dagger X\ge0\) for every \(X\). Finally, if \(F\) is also
nonzero, uniqueness excludes \(c=0\), so \(c>0\). \(\square\)

## Sharpness

### Continuity cannot be deleted

Choose nonnegative constants \(c_0,\ldots,c_k\) and define
\[
F(X)=c_{\operatorname{rank}X}X^\dagger X.
\tag{22}
\]
Rank is unchanged by left unitary multiplication and right multiplication by an invertible matrix,
so (1) and (2) hold. The map is Hermitian- and positive-semidefinite-valued. If two adjacent
nonzero-rank constants differ, it is discontinuous at the lower-rank stratum and is not one scalar
Gram map. Thus symmetry alone does not identify records across rank-changing actualization.

### Compact right covariance is insufficient

For \(k\ge2\), if (2) is required only for \(A\in U(k)\), then
\[
F(X)=\operatorname{tr}(X^\dagger X)I_k
\tag{23}
\]
is continuous, positive, left-\(U(n)\)-invariant, and right-\(U(k)\)-conjugation covariant, but is
not a scalar multiple of \(X^\dagger X\). Full \(GL(k,\mathbb C)\) congruence covariance—or an
equivalent noncompact source principle—is essential.

### Positivity is not needed for algebraic uniqueness

The proof of (3) uses only continuity, Hermitian codomain, and the two transformation laws.
Positivity fixes the sign of the already unique scalar; it does not produce uniqueness.

## Hostile audit

### Internal frontier

`ColorGramMinkowskiCone.lean` already proves that \(X^\dagger X\):

- is positive semidefinite and Hermitian;
- preserves rank;
- is left-unitary invariant;
- is right-frame covariant;
- gives the exact \(1+3\) Lorentz determinant and future cone for \(3\times2\) events.

The Stage-2 card `color-gram-minkowski-orbit-theorem.md` paper-proves that equal Gram matrices are
exactly equal left-\(U(3)\) orbits and that the orbit space is the closed Hermitian positive cone.
The present theorem adds a classification of all continuous records respecting both frame actions.

### External frontier

This is classical invariant/homogeneous-space mathematics:

- the first fundamental theorem for unitary invariants says polynomial invariants are generated by
  Hermitian contractions; see Schrijver, *Tensor subalgebras and First Fundamental Theorems in
  invariant theory*, arXiv:math/0604240;
- the positive-definite Hermitian cone is homogeneous under \(GL(k,\mathbb C)\) congruence;
- polar decomposition and extension of an orthonormal frame to a unitary basis are standard.

The proof above is an elementary continuous-equivariant specialization. No scientific-priority
claim is made.

Verdict:

`[REDISCOVERED] [BRIDGE]`.

### What the theorem does and does not establish

It removes one arbitrary mathematical choice:

> once a physical record is required to forget the full left source frame, respect every right
> noncompact frame transformation, and vary continuously through rank change, the Gram record is
> forced up to units.

It does not prove:

- that exceptional quantum events physically generate \(X\);
- that left \(U(3)\) is exactly the unobservable frame for causalization;
- that right \(GL(2,\mathbb C)\) covariance is source-derived rather than inserted;
- that the Gram record is spacetime rather than a state/covariance matrix;
- Born probabilities, event incidence, gravity, continuum dynamics, or a prediction.

Those remain in the parent Stage-1 conjecture.

## Lean formalization

`ContinuousEquivariantGramRigidity.lean` proves the exact physical \(3\times2\) specialization
without a quadratic-map assumption:

1. a Hermitian \(2\times2\) matrix fixed by every unitary congruence is a real scalar identity;
2. every isometric \(3\times2\) frame extends to a \(3\times3\) unitary;
3. every full-rank \(3\times2\) matrix has the required \(UEP\) polar factorization;
4. full-rank \(3\times2\) matrices are dense, proved by a symbolic quadratic determinant
   perturbation and finite-root avoidance;
5. every continuous Hermitian record with left-\(U(3)\) invariance and right-\(GL(2,\mathbb C)\)
   congruence covariance equals \(cX^\dagger X\) for a real \(c\);
6. positivity for all events is equivalent to \(c\ge0\), and nonzero positivity forces \(c>0\).

The general \(n\ge k\) paper theorem is not claimed as Lean-formalized by this card.

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/ContinuousEquivariantGramRigidity.lean` — pass;
- `lake build GaloisForLFunctions.HTGeometry.ContinuousEquivariantGramRigidity` — pass;
- `scripts/formal_tools.py lint` — pass;
- axiom audit of all three capstone theorems — only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Gates

- [x] 0 → 1: exact conjecture and sharpness attacks stated
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: exact unconditional `3 × 2` Lean theorem, lint, axiom audit, focused final build
- [ ] 3 → 4: not eligible as standalone new knowledge; physical parent remains Stage 1

## Log

- 2026-07-29 — strengthened the active quadratic uniqueness target: no quadratic or polynomial
  hypothesis is needed.
- 2026-07-29 — closed the paper proof using the standard-frame centralizer, polar factorization,
  and density of full-rank matrices.
- 2026-07-29 — recorded discontinuous rank-stratum and compact-right-covariance counterfamilies,
  establishing sharp roles for continuity and noncompact covariance.
