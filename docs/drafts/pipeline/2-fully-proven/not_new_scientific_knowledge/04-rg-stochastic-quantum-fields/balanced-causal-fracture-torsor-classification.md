# Balanced causal fractures are gauge torsors over future cones

- **ID:** `balanced-causal-fracture-torsor-classification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [PROVED HERE] [CLASSICAL INGREDIENTS] [BRIDGE] [LEAN OPEN]`
- **Physics parent:**
  `../../1-in-progress/forbidden-transition-causalization-universal-law.md`
- **Statement:** For the AIII fracture
  \[
  \mathfrak{su}(p+q)
  =
  \mathfrak s(\mathfrak u(p)\oplus\mathfrak u(q))
  \oplus M_{p,q}(\mathbb C),
  \qquad p>q\ge2,
  \]
  equality of retained and forbidden real dimensions is equivalent to every full-rank Gram fibre
  being an \(SU(p)\)-torsor. Both hold exactly when \(p=q+1\). If the positive Gram future is
  strictly convex, then \(q=2\), hence \((p,q)=(3,2)\).

## Goal

Replace the unexplained arithmetic equality
\[
\dim_{\mathbb R}\mathfrak s(\mathfrak u(p)\oplus\mathfrak u(q))
=
\dim_{\mathbb R}M_{p,q}(\mathbb C)
\tag{1}
\]
by an exact recovery statement.

The result shows that balance means more than matching numbers: it is exactly the condition under
which a regular forbidden transition is one positive future together with one complete gauge
frame, with no residual stabilizer. Strict elementary future fusion then selects the
\(3\times2\) carrier.

This is a finite mathematical bridge. It does not prove that physical events satisfy any
antecedent, turn a broken GUT sector into spacetime, derive gravity, or establish new physics.

## Setup

Let
\[
\mathcal V_{p,q}^{\rm reg}
=
\{X\in M_{p,q}(\mathbb C):\operatorname{rank}_{\mathbb C}X=q\},
\qquad p>q\ge2,
\tag{2}
\]
and define the positive Gram map
\[
\Gamma(X)=X^\dagger X\in H_q(\mathbb C)_{++}.
\tag{3}
\]

The left action of \(SU(p)\) preserves \(\Gamma\). Call a regular Gram fibre **exact** when the
\(SU(p)\)-action on it is free and transitive: the fibre is then an \(SU(p)\)-torsor, not a
homogeneous space with unrecorded stabilizer.

Call the closed Gram future \(H_q(\mathbb C)_+\) **elementary** when any two nonzero,
nonproportional boundary points have interior sum:
\[
A,B\in\partial H_q(\mathbb C)_+,\quad
A\ne0,\quad B\ne0,\quad A\notin\mathbb R_{>0}B
\quad\Longrightarrow\quad
A+B\in H_q(\mathbb C)_{++}.
\tag{4}
\]
This is strict convexity in a form adapted to future cones. For the Lorentz cone it says that two
nonparallel future-null momenta add to a future-timelike momentum.

## Theorem

For \(p>q\ge2\), the following are equivalent:

1. the AIII retained and forbidden sectors have equal real dimension;
2. \(p=q+1\);
3. every fibre of `(3)` is an \(SU(p)\)-torsor;
4. some fibre of `(3)` is an \(SU(p)\)-torsor.

Under these conditions there is a smooth product decomposition
\[
\mathcal V_{q+1,q}^{\rm reg}
\cong
SU(q+1)\times H_q(\mathbb C)_{++},
\tag{5}
\]
whose second coordinate is \(\Gamma\).

Moreover, the elementary-future condition `(4)` holds exactly when \(q=2\). Therefore balance,
exact recovery, nonclassicality \(q\ge2\), and elementary future together force
\[
\boxed{(p,q)=(3,2)}
\tag{6}
\]
and
\[
\boxed{
M_{3,2}(\mathbb C)_{\rm reg}
\cong
SU(3)\times H_2(\mathbb C)_{++}.
}
\tag{7}
\]
The second factor is the open four-dimensional Lorentz future cone.

## Proof

### 1. Balance is consecutiveness

The retained algebra has real dimension
\[
\dim_{\mathbb R}\mathfrak s(\mathfrak u(p)\oplus\mathfrak u(q))
=p^2+q^2-1,
\tag{8}
\]
while the forbidden block has real dimension
\[
\dim_{\mathbb R}M_{p,q}(\mathbb C)=2pq.
\tag{9}
\]
Thus `(1)` is equivalent to
\[
p^2+q^2-1=2pq
\quad\Longleftrightarrow\quad
(p-q)^2=1.
\tag{10}
\]
Since \(p>q\), this is equivalent to \(p=q+1\).

### 2. Every regular Gram fibre is a Stiefel manifold

Fix \(H\in H_q(\mathbb C)_{++}\). Rectangular polar decomposition is unique on the full-rank
locus:
\[
X=QH^{1/2},
\qquad Q^\dagger Q=I_q.
\tag{11}
\]
Consequently
\[
\Gamma^{-1}(H)\cong V_q(\mathbb C^p),
\tag{12}
\]
the complex Stiefel manifold of orthonormal \(q\)-frames in \(\mathbb C^p\).

The \(SU(p)\)-action is transitive because \(q<p\): complete two \(q\)-frames to unitary bases,
map one completed basis to the other, and alter the transformation on the nonzero orthogonal
complement to make its determinant one. The stabilizer of the standard \(q\)-frame is
\[
SU(p-q).
\tag{13}
\]
Hence
\[
\Gamma^{-1}(H)\cong SU(p)/SU(p-q).
\tag{14}
\]
It is an \(SU(p)\)-torsor exactly when \(SU(p-q)\) is trivial, equivalently \(p-q=1\).
This proves the equivalence of assertions 1--4.

When \(p=q+1\), every orthonormal \(q\)-frame has a unique final unit vector that completes it to
an oriented unitary basis of determinant one. Thus
\[
V_q(\mathbb C^{q+1})\cong SU(q+1).
\tag{15}
\]
Combining `(11)` and `(15)` proves `(5)`. Smoothness follows because positive square root and
inverse square root are smooth on the positive-definite cone, and determinant-one frame
completion is smooth.

For the special case \((p,q)=(3,2)\), transitivity also has an explicit determinant-correction
proof suited to Lean. Given a regular event \(X\), define its complex normal from the maximal
minors:
\[
n_X=
\begin{pmatrix}
\overline{\Delta_{12}(X)}\\
-\overline{\Delta_{02}(X)}\\
\overline{\Delta_{01}(X)}
\end{pmatrix}.
\tag{15a}
\]
Then \(n_X^\dagger X=0\) and
\[
n_X^\dagger n_X
=|\Delta_{01}(X)|^2+|\Delta_{02}(X)|^2+|\Delta_{12}(X)|^2>0.
\tag{15b}
\]
Let
\[
P_X=\frac{n_Xn_X^\dagger}{n_X^\dagger n_X}.
\tag{15c}
\]
Thus \(P_X^\dagger=P_X\), \(P_X^2=P_X\), and \(P_XX=0\). For any unit phase \(t\), put
\[
D_X(t)=I+(t-1)P_X.
\tag{15d}
\]
Direct multiplication and the rank-one determinant lemma give
\[
D_X(t)^\dagger D_X(t)=I,\qquad
D_X(t)X=X,\qquad
\det D_X(t)=t.
\tag{15e}
\]
If \(U\in U(3)\) carries \(X\) to \(Y\), choose \(t=\overline{\det U}\). Then
\[
\widetilde U=U D_X(t)\in SU(3),
\qquad
\widetilde U X=Y.
\tag{15f}
\]
This proves regular-fibre \(SU(3)\) transitivity without choosing completed bases. For a
dependency-free freeness proof, complete \(X\) by its canonical normal:
\[
F_X=[\,X_0\;X_1\;n_X\,],\qquad
\det F_X=n_X^\dagger n_X>0.
\tag{15g}
\]
If \(W\in SU(3)\) fixes \(X\), then unitarity sends \(n_X\) to a vector orthogonal to both columns.
Since this orthogonal complement is one-dimensional, \(Wn_X=\lambda n_X\). But
\[
\det(WF_X)=\det F_X
\]
and the first two columns of \(WF_X\) equal those of \(F_X\), so \(\lambda=1\). Hence
\(WF_X=F_X\). Since \(F_X\) is invertible, \(W=I\). Thus the action is free, and any equal-Gram
pair is related by a unique \(SU(3)\) transporter.

### 3. Elementary future is rank two

Assume \(q=2\). A nonzero boundary point of \(H_2(\mathbb C)_+\) has rank one. If \(A\) and \(B\)
are nonproportional nonzero boundary points, their one-dimensional ranges are distinct and span
\(\mathbb C^2\). Therefore \(A+B\) has rank two and is positive definite. Condition `(4)` holds.

Assume \(q\ge3\). Let
\[
A=\operatorname{diag}(1,0,0,\ldots,0),
\qquad
B=\operatorname{diag}(0,1,0,\ldots,0).
\tag{16}
\]
They are nonzero, nonproportional boundary points, but \(A+B\) has rank two, hence remains on the
boundary because \(2<q\). Condition `(4)` fails.

Since \(q\ge2\), `(4)` is therefore equivalent to \(q=2\). Balance gives \(p=q+1=3\), proving
`(6)`. The standard Pauli-coordinate identification
\[
H_2(\mathbb C)_{++}
\cong
\{(t,\mathbf x)\in\mathbb R^{1,3}:t>\|\mathbf x\|\}
\tag{17}
\]
turns `(5)` into `(7)`. \(\square\)

### 4. Primitive-pair formulation

For \(u\in\mathbb C^q\), write
\[
R_q(u)_{ij}=\overline{u_i}u_j.
\tag{18}
\]
This is the Gram record of one primitive row and is a positive-semidefinite rank-one boundary
record when \(u\ne0\).

For every \(q\ge2\), the following root-level property is equivalent to \(q=2\):
\[
\forall u,v\in\mathbb C^q,\qquad
\operatorname{LinearIndependent}_{\mathbb C}(u,v)
\Longrightarrow
R_q(u)+R_q(v)\in H_q(\mathbb C)_{++}.
\tag{19}
\]
For \(q=2\), independence makes \(u,v\) a basis, so the quadratic form
\[
x^\dagger(R_2(u)+R_2(v))x
=|\langle u,x\rangle|^2+|\langle v,x\rangle|^2
\tag{20}
\]
is positive for every \(x\ne0\). For \(q\ge3\), take the first two coordinate roots. They are
independent, while their Gram sum annihilates the third coordinate vector and is not positive
definite. Thus `(19)` gives an exact dimension test using only primitive records. It is weaker than
the arbitrary-boundary condition `(4)` but has the same unique nonclassical solution.

This root-level theorem is the exact next Lean target. Its physical use still requires deriving
`(19)` from a source law; treating it as an unexplained spacetime axiom would be circular.

## Full irreducible compact-Hermitian audit

The rank-two conclusion is not an artefact of considering only AIII after balance. Cartan's list
of irreducible compact Hermitian symmetric spaces with simple transvection group gives:

| Type | \(G/K\) | \(\dim K\) | \(\dim(G/K)\) | rank |
|---|---|---:|---:|---:|
| AIII | \(SU(p+q)/S(U(p)\times U(q))\) | \(p^2+q^2-1\) | \(2pq\) | \(\min(p,q)\) |
| BDI | \(SO(n+2)/(SO(n)\times SO(2))\) | \(n(n-1)/2+1\) | \(2n\) | \(2\) for \(n\ge2\) |
| CI | \(Sp(n)/U(n)\) | \(n^2\) | \(n(n+1)\) | \(n\) |
| DIII | \(SO(2n)/U(n)\) | \(n^2\) | \(n(n-1)\) | \(\lfloor n/2\rfloor\) |
| EIII | \(E_6/(\operatorname{Spin}(10)\cdot U(1))\) | \(46\) | \(32\) | \(2\) |
| EVII | \(E_7/(E_6\cdot U(1))\) | \(79\) | \(54\) | \(3\) |

For BDI, balance would require
\[
n(n-1)/2+1=2n
\quad\Longleftrightarrow\quad
n^2-5n+2=0,
\tag{21}
\]
which has no integer solution. CI and DIII have unequal displayed dimensions for every positive
\(n\); EIII and EVII are visibly unequal. Therefore the balanced members of the full list are
exactly
\[
SU(2q+1)/S(U(q+1)\times U(q)).
\tag{22}
\]
Rank two then uniquely gives \(q=2\), hence the \(SU(5)\) pair.

This audit depends on the classical Cartan classification. It is not yet represented by genuine
Lie-group and symmetric-space definitions in Lean and must not be replaced by an encoded finite
table.

## What is new and what is occupied

Occupied mathematics:

- Cartan classification of irreducible compact Hermitian symmetric spaces;
- rectangular polar decomposition;
- \(V_q(\mathbb C^p)\cong SU(p)/SU(p-q)\);
- \(V_{n-1}(\mathbb C^n)\cong SU(n)\);
- strict convexity of rank-two positive cones and the Lorentz realization of
  \(H_2(\mathbb C)_+\).

The proved-here bridge is the equivalence
\[
\text{AIII sector balance}
\quad\Longleftrightarrow\quad
\text{Gram fibre has no residual stabilizer},
\tag{23}
\]
followed by the strict-future selection `(6)`. It is an elementary synthesis, not a claim of
major new mathematics.

Potentially new physics remains wholly in the parent conjecture:

> Nature conserves a forbidden internal transition by retyping its positive quotient as future
> and its exact Gram fibre as gauge frame.

No source located in the audit was found to make that physical identification. Absence of a hit
is not a priority proof.

Useful boundaries:

- M. Ito and B. F. Lourenço,
  [*The \(p\)-cones in dimension \(n\ge3\) are not homogeneous when \(p\ne2\)*](https://arxiv.org/abs/1701.05801),
  which proves that nontrivial strictly convex homogeneous cones are Lorentz cones.
- R. Hauser and O. Güler,
  [*Self-scaled barrier functions on symmetric cones and their classification*](https://arxiv.org/abs/math/0103196),
  for symmetric-cone classification and irreducible decomposition.
- A. Fauntleroy,
  [*Projective Ranks of Compact Hermitian Symmetric Spaces*](https://arxiv.org/abs/math/0104112),
  for the compact irreducible Hermitian symmetric-space setting.

## Physical interpretation boundary

Equation `(7)` supports three exact finite statements:

1. quotienting a regular \(3\times2\) transition by its complete left colour frame leaves one
   four-dimensional timelike future record;
2. the eight missing real dimensions form an \(SU(3)\)-torsor rather than arbitrary padding;
3. the transition is exactly recoverable from future record plus colour frame.

It does **not** establish:

- that physical colour is the torsor action;
- that the positive quotient is physical spacetime;
- that null-boundary strata have the required particle interpretation;
- that \(SU(2)\) weak isospin and Lorentz spin separate across an event;
- event composition, locality, dynamics, chirality, generations, couplings, or gravity.

## Formalization status

Existing unconditional Lean already proves:

- the \(3\times2\) Gram map and its Lorentz-cone coordinates;
- equality of Gram records exactly when matrices differ by a left unitary;
- quotient homeomorphism by the left-unitary orbit relation;
- continuous positive-square-root section; and
- rank-one/null and rank-two/timelike correspondence; and
- two independent one-root null records have positive-definite, timelike sum; and
- for every \(q\ge2\), universal primitive-pair interior fusion holds iff \(q=2\); and
- equal regular \(3\times2\) Gram records are related by a unique left \(SU(3)\) transporter.

Modules:

- `ColorGramMinkowskiCone.lean`;
- `ColorGramMinkowskiOrbit.lean`;
- `ColorGramNullFusion.lean`;
- `PrimitivePairInteriorDimension.lean`;
- `ColorGramSpecialUnitaryOrbit.lean`;
- `BalancedActualityCapacity.lean`.

Still Lean-open:

1. the smooth global product equivalence on the regular \(3\times2\) locus;
2. the arbitrary-boundary strict-convexity iff \(q=2\) theorem for complex positive matrix cones;
3. the AIII balance/torsor equivalence for general \(p>q\);
4. the full Cartan-list corollary using actual formal Lie/symmetric-space definitions.

Formalizing only the integer table while claiming the Cartan classification would be Lean theatre.

The formalized null-fusion subtheorem is documented in
`../../3-formalized/not_new_scientific_knowledge/color-gram-null-fusion.md`. It proves the
rank-two positive direction with genuine complex matrices; it is not presented as the full
strict-cone classification.

The arbitrary-dimension primitive-pair iff theorem is documented in
`../../3-formalized/not_new_scientific_knowledge/primitive-pair-interior-dimension.md`.

The exact regular-fibre \(SU(3)\)-torsor theorem is documented in
`../../3-formalized/not_new_scientific_knowledge/color-gram-special-unitary-orbit.md`.

## Gates

- [x] 0 → 1: exact source-independent theorem and physical role isolated
- [x] 1 → 2: complete paper proof with all parent dependencies stated
- [x] alternative compact-Hermitian families audited
- [x] strongest positive survivor extracted from the non-uniqueness attack
- [ ] 2 → 3: full theorem formalized without table encoding or target smuggling
- [ ] 3 → 4: ineligible alone; physical parent remains open

## Log

- 2026-07-30 — proved balance iff no-stabilizer Gram recovery for the AIII family.
- 2026-07-30 — proved strict elementary future selects \(q=2\), hence the \(3\times2\) fracture.
- 2026-07-30 — audited all irreducible compact Hermitian families and recorded that balance plus
  rank two uniquely leaves \(SU(5)/S(U(3)\times U(2))\).
