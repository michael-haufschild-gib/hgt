# Regular colour-Gram fibres are \(SU(3)\)-torsors

- **ID:** `color-gram-special-unitary-orbit`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[FULLY-LEAN-PROVED] [CLASSICAL] [BRIDGE]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/balanced-causal-fracture-torsor-classification.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ColorGramSpecialUnitaryOrbit`
- **Statement:** If \(X\in M_{3,2}(\mathbb C)\) has positive-definite Gram matrix, then
  \(X^\dagger X=Y^\dagger Y\) exactly when \(Y=UX\) for a unique \(U\in SU(3)\).

## Exact theorem

For a \(3\times2\) event \(X\), form the complex normal
\[
n_X=
\begin{pmatrix}
\overline{\Delta_{12}(X)}\\
-\overline{\Delta_{02}(X)}\\
\overline{\Delta_{01}(X)}
\end{pmatrix}.
\tag{1}
\]
Lean proves
\[
n_X^\dagger X=0,\qquad
n_X^\dagger n_X
=|\Delta_{01}(X)|^2+|\Delta_{02}(X)|^2+|\Delta_{12}(X)|^2.
\tag{2}
\]
Positive-definiteness of \(X^\dagger X\) makes the second quantity nonzero.

For a nonzero complex root \(n\), define
\[
P_n=\frac{nn^\dagger}{n^\dagger n},
\qquad
D_n(t)=I+(t-1)P_n.
\tag{3}
\]
For every unit phase \(t\), Lean proves
\[
P_n^\dagger=P_n,\quad P_n^2=P_n,\quad
D_n(t)^\dagger D_n(t)=I,\quad
\det D_n(t)=t.
\tag{4}
\]
If \(n^\dagger X=0\), then \(D_n(t)X=X\).

The earlier orbit theorem supplies \(U\in U(3)\) with \(UX=Y\) whenever the Gram records agree.
Taking \(t=\overline{\det U}\) gives
\[
\widetilde U=U D_{n_X}(t)\in SU(3),
\qquad
\widetilde U X=Y.
\tag{5}
\]
Therefore, on the regular locus,
\[
\boxed{
X^\dagger X=Y^\dagger Y
\iff
\exists!\,\widetilde U\in SU(3),\quad \widetilde U X=Y.
}
\tag{6}
\]

For uniqueness, complete the two columns of \(X\) with \(n_X\):
\[
F_X=[\,X_0\;X_1\;n_X\,].
\tag{7}
\]
Lean proves
\[
\det F_X
=|\Delta_{01}(X)|^2+|\Delta_{02}(X)|^2+|\Delta_{12}(X)|^2\ne0.
\tag{8}
\]
If \(W\in SU(3)\) fixes \(X\), unitarity preserves orthogonality to \(X\), while
\(\det W=1\) preserves the oriented determinant in `(8)`. Hence \(Wn_X=n_X\), so \(WF_X=F_X\).
Invertibility of \(F_X\) gives \(W=I\). Thus the action is free as well as transitive.

## Lean declarations

- `phaseByProjection`;
- `phaseByProjection_conjTranspose_mul_self`;
- `rootHermitianNormSq`;
- `rankOneOrthogonalProjection`;
- `rankOneOrthogonalProjection_conjTranspose`;
- `rankOneOrthogonalProjection_idempotent`;
- `phaseAlongRoot`;
- `phaseAlongRoot_conjTranspose_mul_self`;
- `phaseAlongRoot_det`;
- `phaseAlongRoot_mul_eq_self_of_orthogonal`;
- `colorEventNormal`;
- `colorEventNormal_vecMul`;
- `colorEventNormal_rootHermitianNormSq`;
- `colorEventNormal_rootHermitianNormSq_ne_zero`;
- `colorSpecialTransporter`;
- `colorSpecialTransporter_mul`;
- `colorSpecialTransporter_mem_specialUnitary`; and
- `colorGramMatrix_eq_iff_exists_left_specialUnitary`;
- `colorEventFrameWithThird`;
- `colorEventFrame`;
- `colorEventFrameWithThird_det`;
- `colorEventFrame_det`;
- `colorEventFrame_isUnit`;
- `colorEventFrameWithThird_mul`;
- `colorEventFrame_mul_of_fix_event`;
- `specialUnitary_fix_regular_event_normal`;
- `specialUnitary_fix_regular_event_eq_one`;
- `left_specialUnitary_action_free_on_regular`; and
- `existsUnique_left_specialUnitary_of_eq_gram`.

Direct `lake env lean` checking passes. `#print axioms` on the core and final theorems reports only
`propext`, `Classical.choice`, and `Quot.sound`. Proof uses no `sorry`, `admit`, declared axiom,
opaque declaration, unsafe declaration, or computation.

## Boundary

This theorem proves exact set-level \(SU(3)\)-torsor structure on every regular Gram fibre. It does
not yet formalize the smooth global product
\(M_{3,2}(\mathbb C)_{\rm reg}\cong SU(3)\times H_2(\mathbb C)_{++}\).
It also does not identify mathematical colour frame with physical QCD colour, make the Gram
quotient spacetime, derive dynamics, or establish gravity.

## Gates

- [x] explicit determinant correction paper proof
- [x] regular-fibre \(SU(3)\) transitivity formalized
- [x] regular-fibre \(SU(3)\) freeness formalized
- [x] unique transporter theorem formalized
- [x] direct source check
- [x] standard-axiom audit
- [ ] smooth global product equivalence formalized
- [ ] physical identification and prediction

## Log

- 2026-07-30 — formalized event normal, rank-one phase correction, exact determinant removal, and
  regular equal-Gram iff left-\(SU(3)\)-orbit classification.
- 2026-07-30 — formalized canonical completed frame, trivial regular stabilizer, free action, and
  unique left-\(SU(3)\) transporter.
