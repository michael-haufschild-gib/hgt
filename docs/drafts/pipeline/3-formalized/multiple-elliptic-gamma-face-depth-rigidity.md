# Multiple elliptic gamma face-depth rigidity

- **ID:** MEG-FACE-DEPTH-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Internal multiple-elliptic-gamma face hierarchy; Kato's irrational-period differential-algebraicity question
- **Statement:** For an integrally independent period tuple, external-lattice translates of two distinct deletion faces with at least two surviving periods are never equal.

## Goal

Close the cross-depth collision gap in the structural differential-matroid program.  Existing Lean
theorems separate translates within one face and across distinct bottom faces, but do not exclude
equality between packets belonging to faces of different depths.  The present theorem reduces every
such hypothetical collision to a nonzero linear relation among bottom-face coordinates.

The statement is source-pure: it concerns actual logarithmic derivatives of multiple elliptic gamma
functions and their actual additive translates.  Its analytic input is exactly the already
formalized joint differential independence of bottom-face packets.

## Exact statement

Let \(I\) be finite, let \(\tau_i\in\mathbb H\), and assume

\[
 m+\sum_{i\in I}n_i\tau_i=0,\qquad m,n_i\in\mathbb Z
 \quad\Longrightarrow\quad
 m=0,\quad n_i=0\ \ (i\in I).
\tag{Q}
\]

For a deletion face \(J\subseteq I\), write

\[
 S_J=I\setminus J,\qquad
 \Psi_J(z)=\frac{d}{dz}\log
 G_{|S_J|}\bigl(z;(\tau_i)_{i\in S_J}\bigr),
\]

using the repository's normalized multiple elliptic gamma hierarchy.  Its external lattice is

\[
 \Lambda_J=\sum_{j\in J}\mathbb Z\tau_j.
\]

**Face-depth rigidity theorem `[PAPER-PROVED]`.**  If \(J\ne L\),
\(|S_J|\ge2\), and \(|S_L|\ge2\), then for every
\(\lambda\in\Lambda_J\) and \(\mu\in\Lambda_L\),

\[
 \Psi_J(z+\lambda)\ne\Psi_L(z+\mu)
\]

as global meromorphic functions.

Equivalently, all external-lattice packets belonging to distinct faces with at least two survivors
are pairwise disjoint.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, direct elaboration, `lake build` green, formal lint PASS, axiom audit clean
- [ ] 3 → 4 publication-ready: incorporated into standalone paper with Lean certificate and external novelty audit

## Proof `[PROVED HERE]`

Put \(S=I\setminus J\), \(T=I\setminus L\).  Suppose, for contradiction,

\[
 T_\lambda\Psi_J=T_\mu\Psi_L, \qquad T_a f(z)=f(z+a).
\tag{1}
\]

For \(i\in I\), set \(\Delta_i=T_{\tau_i}-1\).  The intrinsic coface equation already proved for
the genuine meromorphic hierarchy is

\[
 \Delta_i\Psi_K=\Psi_{K\cup\{i\}}\qquad(i\notin K).
\tag{2}
\]

All \(\Delta_i\) commute with one another and with every \(T_a\).

### 1. Choose compatible bottom faces

There are two-element subsets \(A\subseteq S\), \(B\subseteq T\) satisfying

\[
 A\cap T=B\cap S.
\tag{3}
\]

Indeed, let \(C=S\cap T\), \(u=|S\setminus T|\), and \(v=|T\setminus S|\).  Choose

\[
 k=\max(0,2-u,2-v).
\]

Since \(|S|,|T|\ge2\), one has \(0\le k\le\min(2,|C|)\).  Choose \(k\) common elements, then
\(2-k\) elements from each corresponding difference.  These form \(A,B\).  In a nested case the
construction chooses \(k=2\), hence \(A=B\); otherwise \(A\ne B\) may be arranged.

Set

\[
 W=(S\setminus A)\cup(T\setminus B),\qquad
 \Delta_W=\prod_{i\in W}\Delta_i.
\tag{4}
\]

Condition (3) gives

\[
 W\cap S=S\setminus A,\qquad W\cap T=T\setminus B.
\tag{5}
\]

### 2. Descend both sides to bottom packets

Apply \(\Delta_W\) to (1).  On the left, directions in \(S\setminus A\) use (2) and delete all but
the two survivors \(A\).  Directions in \(W\setminus S\) are already deleted directions; expanding
their factors \(T_{\tau_i}-1\) produces a finite alternating sum of external-lattice translates of
\(\Psi_{I\setminus A}\).  Thus

\[
 \Delta_WT_\lambda\Psi_J
   =\sum_{E\subseteq W\setminus S}(-1)^{|W\setminus S|-|E|}
     T_{\lambda+\sum_{i\in E}\tau_i}\Psi_{I\setminus A}.
\tag{6}
\]

Similarly,

\[
 \Delta_WT_\mu\Psi_L
   =\sum_{F\subseteq W\setminus T}(-1)^{|W\setminus T|-|F|}
     T_{\mu+\sum_{i\in F}\tau_i}\Psi_{I\setminus B}.
\tag{7}
\]

Each translation label in (6) belongs to the external lattice of the bottom face \(I\setminus A\);
each label in (7) belongs to that of \(I\setminus B\).

Hypothesis (Q) makes each Boolean-cube labelling in (6) and (7) injective: equality of two labels
would give an integral period relation with coefficients in \(\{-1,0,1\}\).  Hence neither
alternating sum vanishes internally.

### 3. Rule out cancellation

If \(A\ne B\), existing bottom-face cross-separation says the two packets are disjoint, and existing
bottom-star freeness says their union is differentially independent over \(\mathbb C\).  Equations
(6) and (7) would therefore give a nonzero linear relation among a differentially independent
family, impossible.

If \(A=B\), write

\[
 U=S\setminus T,\qquad V=T\setminus S.
\]

The left cube in (6) varies only in the \(V\)-coordinates; the right cube in (7) varies only in the
\(U\)-coordinates.  Two distinct common labels would yield, after subtraction, an integral relation
supported on the disjoint sets \(U,V\), contrary to (Q).  Thus the cubes intersect in at most one
label.  Since \(S\ne T\), at least one of \(U,V\) is nonempty, so at least one cube has more than one
term.  After the possible single cross-cancellation, a nonzero coefficient remains.  The resulting
nonzero linear relation lies in one differentially independent bottom packet, again impossible.

Both cases contradict (1).  This proves face-depth rigidity. \(\square\)

## Dependency audit

1. Intrinsic coface equation (2): Lean theorem
   `multipleEllipticGammaLogDerivFaceMero_addTranslation_sub`.
2. Translation commutation and finite alternating expansion: algebraic identities for the existing
   meromorphic translation automorphisms; no analytic assumption.
3. Injectivity of lattice labels under (Q): Lean theorem family
   `faceShiftLattice_translate_injective` / `facePalette_injective`; the Boolean-cube instance also
   follows directly from (Q).
4. Bottom-face packet disjointness: Lean theorem
   `multipleEllipticGammaFace_translate_ne_bottom`.
5. Joint bottom-face differential independence: Lean theorem
   `multipleEllipticGammaFaceStar_diffIndepOn_bottom`.

No unproved mathematical dependency remains in the paper proof.  The finite-difference descent and
same-bottom Boolean-cube cancellation lemma still require Lean formalization.

## Antagonist attacks

### Attack A: applying all differences might over-delete a side

Resolved by (3): it is exactly the condition making (5) hold.  No direction surviving in \(A\) or
\(B\) is differentiated.

### Attack B: repeated translation labels could annihilate an alternating cube

Resolved by (Q).  Distinct subsets give coefficient vectors differing in
\(\{-1,0,1\}^{I}\), hence distinct complex shifts.

### Attack C: different-depth packets might overlap, making the final linear relation zero

This is the original gap.  Descent replaces it by either already formalized cross-bottom
separation (\(A\ne B\)) or the disjoint-coordinate cube argument (\(A=B\)).  The latter permits at
most one cross-cancellation and cannot cancel a nontrivial cube completely.

### Attack D: differential independence is stronger than needed and might be invoked circularly

Bottom-star freeness was proved independently from two-period elliptic-gamma divisor obstructions.
It does not use face-depth separation or the all-order gluing theorem.  The present proof uses only
its linear-independence consequence.

### Attack E: nested survivor sets force identical chosen bottom faces

Handled by the \(A=B\) case.  Nesting is precisely where one Boolean cube is a singleton and the
other is nontrivial, so complete cancellation is impossible.

## External frontier

- Kato proves differential algebraicity when all periods are rational and explicitly records the
  non-rational-period case as unknown.
- Narukawa and Nishizawa establish modular/functional identities for the hierarchy, not
  differential-algebraic separation of deletion faces.
- Recent geometric-family work studies cocycles and rational Bernoulli corrections, not equality
  or differential independence of the meromorphic face packets.
- Arreche–Babbitt and related parametrized-difference-Galois work provide obstruction mechanisms for
  elliptic difference equations, but no all-face multiple-elliptic-gamma rigidity theorem was found.

The external search found no equivalent face-depth packet-separation law.  This is negative
evidence, not a proof of novelty; exact priority claims remain forbidden.

## Lean target

Add one focused module proving:

1. finite commuting face-difference descent to an alternating bottom-packet sum;
2. injectivity and at-most-one-intersection for the two Boolean cubes;
3. `multipleEllipticGammaFacePacket_disjoint_of_ne`, or an equivalent pointwise translate theorem.

Use `lake env lean <file>` during development.  Run `lake build <module>` only once at final audit;
then run formal lint and an isolated `#print axioms` scratch check.

## Log

- 2026-07-27 — created in 1-in-progress after corpus audit exposed the cross-depth overlap gap.
- 2026-07-27 — paper proof completed and attacked; moved to 2-fully-proven for Lean formalization.
