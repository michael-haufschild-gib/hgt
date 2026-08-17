# Kernel fidelity selects the Gram causalizer

- **ID:** `equivariant-causal-hessian-kernel-fidelity-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE] [LEAN CLOSED]`
- **Parent:** `../../1-in-progress/self-noncontainment-minimal-repair-law.md`
- **Statement:** Every sesquilinearly polarized \(U(r)\)-invariant and \(U(n)\)-covariant positive
  quadratic causalizer on \(M_{r,n}(\mathbb C)\), \(n\ge2\), is
  \[
  q_{a,b}(X)=aX^\dagger X+b\,\operatorname{tr}(X^\dagger X)I_n.
  \]
  Positivity is equivalent to \(b\ge0\) and \(a+b\ge0\).  Exact kernel fidelity
  \(\ker q(X)=\ker X\) for every \(X\) holds exactly when \(b=0\) and \(a>0\).

## Goal

Close the local ambiguity identified by the causal-Hessian programme.  Positivity and unitary
equivariance permit both a direct Gram record and an isotropic trace record.  Determine whether the
operational requirement
\[
Xv=0\quad\Longleftrightarrow\quad q(X)v=0
\tag{1}
\]
selects \(X^\dagger X\).

The theorem is only a finite local bridge.  It does not derive kernel fidelity from source-level
physics, select a scale, construct spacetime, identify a gauge group, produce gravity, or prove the
future-square conjecture.

## Exact setup

Fix integers \(r\ge1\) and \(n\ge2\).  Let
\[
\Phi:
M_{r,n}(\mathbb C)\times M_{r,n}(\mathbb C)
\longrightarrow M_n(\mathbb C)
\]
be conjugate-linear in its first argument and complex-linear in its second.  Assume:

1. **left-unitary invariance**
   \[
   \Phi(UX,UY)=\Phi(X,Y)
   \qquad(U\in U(r));
   \tag{2}
   \]
2. **right-unitary covariance**
   \[
   \Phi(XV,YV)=V^\dagger\Phi(X,Y)V
   \qquad(V\in U(n)).
   \tag{3}
   \]

Define the diagonal quadratic map
\[
q(X)=\Phi(X,X).
\tag{4}
\]

## Theorem

### Part I: equivariant classification

There are unique \(a,b\in\mathbb C\) such that
\[
\Phi(X,Y)
=aX^\dagger Y
+b\,\operatorname{tr}(X^\dagger Y)I_n
\tag{5}
\]
for all \(X,Y\).

If \(q(X)\) is Hermitian for every \(X\), then \(a,b\in\mathbb R\).

### Part II: positive cone

The condition
\[
q(X)\succeq0
\qquad\text{for every }X
\tag{6}
\]
is equivalent to
\[
b\ge0,\qquad a+b\ge0.
\tag{7}
\]

### Part III: kernel-fidelity rigidity

Under positivity, the following are equivalent:

1. for every \(X\in M_{r,n}(\mathbb C)\) and \(v\in\mathbb C^n\),
   \[
   Xv=0\quad\Longleftrightarrow\quad q(X)v=0;
   \tag{8}
   \]
2. \(b=0\) and \(a>0\);
3. there is \(c>0\) such that
   \[
   q(X)=cX^\dagger X
   \tag{9}
   \]
   for every \(X\).

Thus kernel fidelity removes the isotropic trace causalizer and every mixed causalizer, but it
does not fix the positive scale \(c\).

## Proof of Part I

### Lemma 1: left invariance leaves only the Gram contraction

View \(M_{r,n}(\mathbb C)\) as
\(\mathbb C^r\otimes(\mathbb C^n)^*\).  For each output matrix coefficient, the corresponding
scalar component of \(\Phi\) is a sesquilinear form on this tensor product.  Condition (2) says its
coefficient operator commutes with the defining \(U(r)\)-action on \(\mathbb C^r\).

The defining complex representation of \(U(r)\) is irreducible, so its commutant consists of
scalars.  Hence the row indices can occur only through the standard contraction.  Equivalently,
there is a unique complex-linear map
\[
L:M_n(\mathbb C)\longrightarrow M_n(\mathbb C)
\tag{10}
\]
such that
\[
\Phi(X,Y)=L(X^\dagger Y).
\tag{11}
\]

This statement can also be checked in coordinates.  Independent diagonal phases in \(U(r)\) kill
terms pairing different row indices, and permutation unitaries force the surviving same-row
coefficients to agree.

### Lemma 2: conjugation-equivariant linear maps have two parameters

Substituting (11) into (3) gives
\[
L(V^\dagger AV)=V^\dagger L(A)V
\qquad
(V\in U(n),\ A\in M_n(\mathbb C)).
\tag{12}
\]

First, \(L(I_n)\) commutes with every unitary, hence
\[
L(I_n)=\lambda I_n.
\tag{13}
\]

Second, \(A\mapsto\operatorname{tr}(L(A))\) is a conjugation-invariant linear functional.
Every such functional is a scalar multiple of trace.  Indeed, permutation unitaries give the same
value on all diagonal matrix units, while diagonal phase unitaries force the value on every
off-diagonal matrix unit to vanish.  Therefore \(L\) preserves the traceless subspace
\[
\mathfrak{sl}_n(\mathbb C)=\{A:\operatorname{tr}A=0\}.
\tag{14}
\]

The conjugation representation of \(U(n)\) on \(\mathfrak{sl}_n(\mathbb C)\) is irreducible for
\(n\ge2\).  One concise proof differentiates the unitary action: an invariant complex subspace is
stable under commutators with \(\mathfrak{su}(n)\), hence with its complexification
\(\mathfrak{sl}_n(\mathbb C)\); it is therefore an ideal of the simple Lie algebra
\(\mathfrak{sl}_n(\mathbb C)\).  Schur's lemma now gives
\[
L(A)=aA
\qquad
(\operatorname{tr}A=0)
\tag{15}
\]
for one \(a\in\mathbb C\).

Splitting
\[
A=\left(A-\frac{\operatorname{tr}A}{n}I_n\right)
  +\frac{\operatorname{tr}A}{n}I_n
\tag{16}
\]
and using (13)--(15) yields
\[
L(A)=aA+b\,\operatorname{tr}(A)I_n
\tag{17}
\]
for a unique \(b\in\mathbb C\).  Equations (11) and (17) prove (5).

If every \(q(X)\) is Hermitian, take a nonzero rank-one \(X=u v^\dagger\) with
\(\lVert u\rVert=\lVert v\rVert=1\).  Then
\[
q(X)=avv^\dagger+bI_n.
\tag{18}
\]
On \(v^\perp\) the eigenvalue is \(b\), and on \(\mathbb Cv\) it is \(a+b\).  Hermiticity gives
\(b\in\mathbb R\) and \(a+b\in\mathbb R\), hence \(a\in\mathbb R\).

This proves Part I. \(\square\)

## Proof of Part II

Assume (6).  Apply it to the rank-one matrix in (18).  Since \(n\ge2\), there is a nonzero vector
in \(v^\perp\).  Positivity on \(v^\perp\) and on \(\mathbb Cv\) gives
\[
b\ge0,\qquad a+b\ge0.
\]
Thus (7) is necessary.

Conversely, let
\[
A=X^\dagger X\succeq0,\qquad s=\operatorname{tr}A.
\]
Choose an eigenvalue \(\lambda\) of \(A\).  Then \(0\le\lambda\le s\), and the corresponding
eigenvalue of \(q(X)=aA+bsI_n\) is
\[
a\lambda+bs.
\tag{19}
\]

If \(a\ge0\), (19) is nonnegative because \(b\ge0\).  If \(a<0\), the inequality
\(\lambda\le s\) reverses after multiplication by \(a\), so
\[
a\lambda+bs\ge as+bs=(a+b)s\ge0.
\]
Every eigenvalue of \(q(X)\) is therefore nonnegative.  This proves (6).
\(\square\)

## Proof of Part III

Assume positivity and kernel fidelity.  Again take
\[
X=u v^\dagger
\]
with \(u\ne0\) and \(v\ne0\).  Its kernel is \(v^\perp\).  For every \(w\in v^\perp\),
\[
q(X)w
=b\,\lVert u\rVert^2\lVert v\rVert^2w.
\tag{20}
\]
Kernel fidelity requires (20) to vanish for every such nonzero \(w\), hence \(b=0\).

With \(b=0\),
\[
q(X)v
=a\,\lVert u\rVert^2\lVert v\rVert^2v.
\tag{21}
\]
Because \(Xv\ne0\), kernel fidelity makes (21) nonzero, so \(a\ne0\).  Positivity and (7) now give
\(a>0\).  This proves \(1\Rightarrow2\), and \(2\Rightarrow3\) is immediate.

Finally, if \(q(X)=cX^\dagger X\) with \(c>0\), then
\[
q(X)v=0
\quad\Longleftrightarrow\quad
\langle v,q(X)v\rangle=0
\quad\Longleftrightarrow\quad
c\lVert Xv\rVert^2=0
\quad\Longleftrightarrow\quad
Xv=0.
\tag{22}
\]
Thus \(3\Rightarrow1\), completing the proof.
\(\square\)

## Sharp boundaries

1. The hypothesis \(n\ge2\) is necessary for separating the direct and trace contractions.  For
   \(n=1\), they are the same scalar quadratic form.
2. Positivity alone leaves the full wedge \(b\ge0,\ a+b\ge0\).
3. Rank, support, phase invariance, unitary equivariance, and one total weight do not replace
   kernel fidelity.
4. Kernel fidelity fixes the direction of every rank-one causal ray but not the global positive
   scale.
5. This is a same-level classification after complex Hilbert carriers and unitary actions are
   supplied.  The corpus's isoradical theorem still shows that kernel data do not select a
   physical metric or its weights across histories.
6. Nothing here makes the source matrix a physical event or the Gram cone physical spacetime.

## Hostile novelty audit

`[NOT NEW MATHEMATICS]`

The proof is a direct application of the commutant of the defining unitary representation, the
decomposition
\[
M_n(\mathbb C)=\mathbb CI_n\oplus\mathfrak{sl}_n(\mathbb C),
\]
Schur's lemma, and elementary positive-matrix spectral bounds.  It belongs to classical unitary
invariant theory.

Candidate physical novelty remains upstream: derive kernel fidelity, complex carriers, the unitary
actions, positive calibration, and the source-to-successor role change without inserting a Hilbert
space or causal cone.  The theorem only says that if those local hypotheses are independently
forced, the direct Gram causalizer is rigid up to scale.

## Positive consequence for the active conjecture

Within the complete polarized unitary-equivariant family, “no unaffected alternative receives
future weight” is exactly strong enough to eliminate:

- the isotropic spectator causalizer
  \(\operatorname{tr}(X^\dagger X)I_n\);
- every positive mixture of direct and isotropic causalization; and
- the complementary/opposite-ray causalizer in the two-channel rank-one shadow.

It is not strong enough to generate the ruler.  The remaining factor \(c>0\) confirms the later
complete-history conclusion: local source support may select causal orientation while global
history must select calibration.

## Planned Lean surface

Target module:
`GaloisForLFunctions.HTGeometry.EquivariantCausalHessianKernelFidelity`.

Exact theorem families:

1. define the two-parameter causalizer
   \[
   q_{a,b}(X)=aX^\dagger X+b\,\operatorname{tr}(X^\dagger X)I;
   \]
2. prove its unitary invariance/covariance and Hermiticity for real \(a,b\);
3. prove positivity from \(b\ge0,\ a+b\ge0\);
4. prove positivity forces the two inequalities by a symbolic rank-one witness;
5. prove kernel fidelity forces \(b=0\);
6. prove kernel fidelity plus positivity forces \(a>0\);
7. prove positive Gram scaling has exact kernel fidelity;
8. formalize the full equivariant classification (5), rather than silently assuming the
   two-parameter family, before promotion to Stage 3; and
9. audit all declarations with `#print axioms`.

No numerical computation, finite enumeration, `native_decide`, `sorry`, `admit`, `axiom`,
`opaque`, `unsafe`, or classical-choice shortcut may replace the symbolic proof.

## Gates

- [x] 0 → 1: exact source question and counterfamilies identified
- [x] 1 → 2: dependency-closed paper theorem and proof
- [x] hostile novelty audit: classical invariant-theory bridge
- [x] physical interpretation bounded
- [x] 2 → 3: full classification and rigidity formalized unconditionally in Lean —
      `HTGeometry/EquivariantCausalizerClassification.lean`,
      `HTGeometry/EquivariantCausalizerPositivity.lean` (+ three supporting modules);
      axioms `[propext, Classical.choice, Quot.sound]`
- [ ] source-level physics derives kernel fidelity and calibration

## Log

- 2026-07-30 — classified all polarized left-invariant/right-covariant quadratic causalizers by
  the direct Gram and isotropic trace contractions.
- 2026-07-30 — proved exact positivity wedge \(b\ge0,\ a+b\ge0\).
- 2026-07-30 — proved kernel fidelity selects \(cX^\dagger X\), \(c>0\), and isolated the
  remaining calibration ambiguity.
- 2026-07-30 — classified result as standard unitary invariant theory and retained it only as a
  local bridge for source-complete causalization descent.

## Lean formalization — 2026-08-17

Five new modules, all unconditional
(`#print axioms` = `[propext, Classical.choice, Quot.sound]` for every declaration cited here):

- `formal/GaloisForLFunctions/HTGeometry/UnitaryConjugationMatrixUnits.lean`
- `formal/GaloisForLFunctions/HTGeometry/TwoBlockUnitaryAlgebra.lean`
- `formal/GaloisForLFunctions/HTGeometry/ConjugationEquivariantClassification.lean`
- `formal/GaloisForLFunctions/HTGeometry/EquivariantCausalizerClassification.lean`
- `formal/GaloisForLFunctions/HTGeometry/EquivariantCausalizerPositivity.lean`

| Paper step | Lean name |
|---|---|
| (2) left invariance kills different rows | `phi_diff_row_eq_zero` |
| (2) left invariance makes the same-row pairing row-independent | `phi_row_indep` |
| Lemma 1, (10)-(11): `Φ(X,Y) = L(XᴴY)` | `inducedMap`, `phi_eq_inducedMap` |
| (3)/(12): right covariance makes `L` conjugation equivariant | `inducedMap_equivariant` |
| Lemma 2 support step: `L(E_ij)` is a multiple of `E_ij` for `i≠j` | `exists_offDiag_coeff` |
| Lemma 2: `L(E_ii)` is diagonal | `diag_image_offDiag_eq_zero` |
| Lemma 2: the constants are index-independent | `offDiag_coeff_eq`, `diag_offCoeff_eq`, `diag_sameCoeff_eq`, `exists_perm_map_pair` |
| (13)-(15): the one non-monomial unitary tying the constants | `blockUnitary`, `blockUnitary_mem_unitaryGroup`, `blockUnitary_conj_blockZ`, `coeffA_eq_sub` |
| (16)-(17): `L(A) = aA + b tr(A) I` | `classification` |
| (5) Part I existence | `exists_causalizer_coeffs` |
| Part I uniqueness of `a, b` | `causalizer_coeffs_unique` |
| (18) Hermiticity forces `a, b` real | `coeffs_real_of_isHermitian` |
| the family is `U(r)`-invariant and `U(n)`-covariant | `causalizerForm_left_invariant`, `causalizerForm_right_covariant` |
| (6)-(7)/(19) Part II, the positive wedge | `posSemidef_causalizerForm_iff` |
| (8)-(9)/(20)-(22) Part III, kernel fidelity | `kernel_fidelity_iff` |

Two substitutions of proof mechanism, both avoiding imported machinery:

1. **No Schur's lemma or `sl_n` irreducibility.**  The classification of conjugation-equivariant
   linear maps is proved in coordinates: two diagonal phase unitaries (with entries `I` at one
   index) confine `L(E_ij)` to `E_ij`, permutation matrices make the three constants
   index-independent, and the single non-monomial unitary
   `V = 1 + ((1+I)/2 - 1)(E_ii + E_jj) + ((1-I)/2)(E_ij + E_ji)` — for which
   `Vᴴ (E_ii - E_jj) V = -I (E_ij - E_ji)` — supplies the relation `α = a + b`.
2. **No spectral theorem in Part II.**  Instead of eigenvalues of `A = XᴴX`, the Lean proof uses
   the explicit quadratic form `a ‖Xv‖² + b ‖X‖_F² ‖v‖²` together with the componentwise
   Cauchy–Schwarz bound `‖Xv‖² ≤ ‖X‖_F² ‖v‖²` (`sum_norm_mulVec_sq_le`), which reproduces the
   card's eigenvalue argument `0 ≤ λ ≤ s` without any spectral input.

The planned Lean surface of this card (items 1–9) is complete, including item 8: the full
equivariant classification is proved rather than assumed.

Not formalized, and not an obligation of this card: the "sharp boundaries", "hostile novelty
audit", and "positive consequence" sections, which interpret the theorem rather than assert new
mathematics, and the second open gate (source-level physics deriving kernel fidelity), which the
card marks as upstream research.

## Log

- 2026-08-17 Formalized Parts I, II and III unconditionally in Lean 4 and promoted to stage 3.
