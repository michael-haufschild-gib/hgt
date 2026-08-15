# The colour Gram orbit space is the closed four-dimensional Minkowski future cone

- **ID:** `color-gram-minkowski-orbit-theorem`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Formalized companion:** `color-gram-minkowski-orbit-theorem-formalized.md`
- **Status:** `[PAPER-PROVED] [FULLY-LEAN-PROVEN] [REDISCOVERED] [BRIDGE]`
- **Parent conjecture:** `../../1-in-progress/color-blind-event-gram-spacetime-law.md`
- **Statement:** The Gram map identifies
  \(M_{3,2}(\mathbb C)/U(3)\) with the positive-semidefinite Hermitian \(2\times2\) cone, hence with
  the closed future cone in \(\mathbb R^{1,3}\), carrying rank two to timelike vectors and rank one
  to nonzero null vectors.

## Theorem

Let \(V=M_{3,2}(\mathbb C)\), with \(U(3)\) acting by left multiplication, and define
\[
\Gamma:V\longrightarrow H_2(\mathbb C),\qquad
\Gamma(X)=X^\dagger X.
\tag{1}
\]
Then:

1. \(\Gamma(X)\) is positive semidefinite and
   \(\Gamma(UX)=\Gamma(X)\) for every \(U\in U(3)\).
2. \(\Gamma(X)=\Gamma(Y)\) if and only if \(Y=UX\) for some \(U\in U(3)\).
3. Every positive-semidefinite \(H\in H_2(\mathbb C)\) equals \(\Gamma(X)\) for some \(X\in V\).
4. The induced map
   \[
   \bar\Gamma:V/U(3)\xrightarrow{\ \cong\ }H_2(\mathbb C)_{\ge0}
   \tag{2}
   \]
   is a homeomorphism.
5. Under
   \[
   \Phi(t,x,y,z)=
   \begin{pmatrix}
   t+z&x-iy\\
   x+iy&t-z
   \end{pmatrix},
   \tag{3}
   \]
   \[
   \det\Phi(t,x,y,z)=t^2-x^2-y^2-z^2
   \tag{4}
   \]
   and
   \[
   \Phi^{-1}\!\left(H_2(\mathbb C)_{\ge0}\right)
   =\{(t,\mathbf x):t\ge0,\ t^2-\lVert\mathbf x\rVert^2\ge0\}.
   \tag{5}
   \]
6. \(X\) has complex rank two exactly when \(\Phi^{-1}(\Gamma(X))\) is future timelike.
   A nonzero \(X\) has rank one exactly when it is future null.
7. For the full left-right action
   \[
   X\longmapsto UXV^\dagger,\qquad (U,V)\in U(3)\times U(2),
   \tag{6}
   \]
   \[
   \Gamma(UXV^\dagger)=V\Gamma(X)V^\dagger.
   \tag{7}
   \]

## Proof

### Positivity and left invariance

For \(w\in\mathbb C^2\),
\[
w^\dagger\Gamma(X)w
=w^\dagger X^\dagger Xw
=\lVert Xw\rVert^2\ge0.
\tag{8}
\]
Thus \(\Gamma(X)\) is positive semidefinite. If \(U^\dagger U=I_3\), then
\[
\Gamma(UX)=X^\dagger U^\dagger UX=X^\dagger X=\Gamma(X).
\tag{9}
\]
This proves part 1.

### Exact orbit classification

Suppose \(\Gamma(X)=\Gamma(Y)\). Define
\[
T:\operatorname{im}X\longrightarrow\operatorname{im}Y,
\qquad T(Xw)=Yw.
\tag{10}
\]
This is well defined. Indeed, if \(Xw=0\), then
\[
0=\lVert Xw\rVert^2
=w^\dagger X^\dagger Xw
=w^\dagger Y^\dagger Yw
=\lVert Yw\rVert^2,
\]
so \(Yw=0\).

For \(w,z\in\mathbb C^2\),
\[
\langle T(Xw),T(Xz)\rangle
=\langle Yw,Yz\rangle
=w^\dagger Y^\dagger Yz
=w^\dagger X^\dagger Xz
=\langle Xw,Xz\rangle.
\tag{11}
\]
Therefore \(T\) is a complex-linear isometry from \(\operatorname{im}X\) onto
\(\operatorname{im}Y\). Choose orthonormal bases of these two subspaces related by \(T\), extend
both to orthonormal bases of \(\mathbb C^3\), and send the first completed basis to the second.
The resulting \(U\in U(3)\) extends \(T\), hence \(UX=Y\).

Conversely, equation (9) shows that \(Y=UX\) implies
\(\Gamma(Y)=\Gamma(X)\). This proves part 2.

### Surjectivity

Let \(H\in H_2(\mathbb C)_{\ge0}\). The finite-dimensional spectral theorem supplies its unique
positive-semidefinite square root \(R=H^{1/2}\), satisfying \(R^\dagger=R\) and \(R^2=H\). Embed
\(R\) as the first two rows of a \(3\times2\) matrix:
\[
X=
\begin{pmatrix}
&R&\\
0&0
\end{pmatrix}.
\tag{12}
\]
Then
\[
X^\dagger X=R^\dagger R=R^2=H.
\tag{13}
\]
This proves part 3.

### Quotient topology

By (9), \(\Gamma\) factors through a continuous map \(\bar\Gamma\) in (2). Parts 2 and 3 make
\(\bar\Gamma\) bijective. Define
\[
s:H_2(\mathbb C)_{\ge0}\longrightarrow V/U(3)
\]
by taking the orbit of the matrix (12). The positive-semidefinite square-root map is continuous,
so \(s\) is continuous. Equation (13) gives \(\bar\Gamma\circ s=\mathrm{id}\), while part 2 gives
\(s\circ\bar\Gamma=\mathrm{id}\). Hence \(\bar\Gamma\) is a homeomorphism. This proves part 4.

### Lorentz cone

Direct expansion gives
\[
\det\Phi(t,x,y,z)
=(t+z)(t-z)-(x-iy)(x+iy)
=t^2-x^2-y^2-z^2,
\]
proving (4).

The eigenvalues of \(\Phi(t,x,y,z)\) are
\[
t\pm r,\qquad r=\sqrt{x^2+y^2+z^2}.
\tag{14}
\]
Thus \(\Phi(t,x,y,z)\) is positive semidefinite exactly when
\(t-r\ge0\), equivalently \(t\ge0\) and \(t^2-r^2\ge0\). This is (5), proving part 5.

The kernels of \(X\) and \(X^\dagger X\) agree, because
\[
X^\dagger Xw=0
\quad\Longrightarrow\quad
0=w^\dagger X^\dagger Xw=\lVert Xw\rVert^2
\quad\Longrightarrow\quad Xw=0,
\tag{15}
\]
and the reverse implication is immediate. Hence
\[
\operatorname{rank}(X^\dagger X)=\operatorname{rank}X.
\tag{16}
\]
A positive-semidefinite Hermitian \(2\times2\) matrix is positive definite exactly at rank two,
which corresponds through (14) to \(t>r\), the future-timelike cone. Its nonzero rank-one boundary
has one zero eigenvalue, hence \(t=r>0\), the future-null cone. This proves part 6.

Finally,
\[
\begin{aligned}
\Gamma(UXV^\dagger)
&=(UXV^\dagger)^\dagger(UXV^\dagger)\\
&=VX^\dagger U^\dagger UXV^\dagger\\
&=V\Gamma(X)V^\dagger,
\end{aligned}
\]
proving part 7. \(\square\)

## Coordinate determinant identity

Writing \(X=(u\ v)\) with \(u,v\in\mathbb C^3\),
\[
\Gamma(X)=
\begin{pmatrix}
\lVert u\rVert^2&\langle u,v\rangle\\
\langle v,u\rangle&\lVert v\rVert^2
\end{pmatrix}
\tag{17}
\]
and
\[
\det\Gamma(X)
=\lVert u\rVert^2\lVert v\rVert^2-|\langle u,v\rangle|^2
=\sum_{1\le i<j\le3}|u_iv_j-u_jv_i|^2.
\tag{18}
\]
The second equality is the \(3\times2\) Cauchy--Binet identity. It makes the causal boundary
algebraic: \(\det\Gamma(X)=0\) exactly when every \(2\times2\) minor vanishes.

## Frontier and significance

The theorem combines standard results:

- Gram matrices and unitary orbit classification;
- polar decomposition and continuous positive square roots;
- the Pauli/Hermitian realization of Minkowski space;
- the Cauchy--Binet identity.

It is `[REDISCOVERED]`, not new mathematical or physical knowledge.

The source-specific bridge arises because Baez--Bokor--Boyle identify the common Peirce-half triple
of two compatible exceptional pure states with \(M_{3,2}(\mathbb C)\) and its real inner
automorphism group with the exact Standard Model gauge group. Their paper does not interpret the
left \(U(3)\) Gram quotient as causal spacetime.

The unproved physical statement that nature uses this quotient is isolated in
`../../1-in-progress/color-blind-event-gram-spacetime-law.md`.

## Formalization status

The exact algebraic and topological theorem is unconditionally Lean-proven in
`../../../../../formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiCone.lean` and
`../../../../../formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiOrbit.lean`, documented in
the two stage-3 cards:

1. the explicit \(3\times2\) Gram matrix;
2. positive semidefiniteness, Hermiticity, and exact rank preservation;
3. left-unitary invariance and right covariance;
4. determinant as the sum of the three squared Plücker minors;
5. exact Pauli-coordinate Lorentz determinant;
6. nonnegative future time and Lorentz mass-squared;
7. null iff all maximal minors vanish, timelike iff one is nonzero.

The orbit module additionally proves parts 2--4 of the paper theorem: exact \(U(3)\)-orbit
classification, surjectivity onto the full positive Hermitian cone, continuity of the Gram map
and square-root section, identification of kernel classes with unitary orbits, and the quotient
homeomorphism.

## Gates

- [x] 0 → 1: exact source-independent theorem and role identified
- [x] 1 → 2: dependency-closed proof written and hostile audit classifies it as a bridge
- [x] algebraic core extracted to stage 3; focused build and axiom audit green
- [x] 2 → 3 for this full card: orbit classification, surjectivity, and quotient homeomorphism
  formalized unconditionally in Lean
- [ ] 3 → 4: not eligible as a standalone publication claim; physical parent remains stage 1

## Log

- 2026-07-29 — proved the full Gram-orbit and Lorentz-cone theorem. Classified the mathematics as
  rediscovered and isolated the new physical content in the parent conjecture.
- 2026-07-29 — formalized the exact Gram/Lorentz/Cauchy--Binet core, causal rank strata, and
  covariance. Kept quotient classification and topology explicitly at paper-only status.
- 2026-07-29 — formalized equality of records iff left-unitary equivalence, positive-cone
  surjectivity, a continuous positive-square-root section, kernel-class/orbit identification, and
  the quotient homeomorphism.
- 2026-08-15 — re-audited both Gram-orbit and Gram-cone theorem surfaces by direct source and
  targeted orbit build before consolidating this full paper card into Stage 3. The audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
