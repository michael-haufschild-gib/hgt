# Same-qubit weak–Lorentz overlap no-go

- **ID:** `same-qubit-weak-lorentz-overlap-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / HOSTILE BOUNDARY
- **Novelty:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`; explicit corollary of the standard
  \(SU(2)\)-on-\(H_2(\mathbb C)\) conjugation action
- **Parent:** `../1-in-progress/exceptional-locality-curvature-theory-of-everything.md`
- **Statement:** The electroweak \(SU(2)\) selected by the canonical nested
  \(H_2(\mathbb C)\subset H_3(\mathbb C)\subset H_3(\mathbb O)\) construction acts nontrivially
  on that same \(H_2(\mathbb C)\) by the ordinary spatial-rotation representation; it cannot be an
  internal kernel of a Lorentz action obtained from the same copy.

## Exact finite theorem

Let

\[
  U=\begin{pmatrix}i&0\\0&-i\end{pmatrix},
  \qquad
  X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

Then:

1. \(U^\dagger U=I\);
2. \(\det U=1\), so \(U\in SU(2)\);
3. \(X^\dagger=X\), so \(X\in H_2(\mathbb C)\);
4. \(UXU^\dagger=-X\neq X\).

Consequently, the conjugation representation

\[
  \rho:SU(2)\longrightarrow GL(H_2(\mathbb C)),\qquad
  \rho(u)(x)=uxu^\dagger
\]

is nontrivial. In particular \(SU(2)\not\subseteq\ker\rho\).

## Proof

Complex conjugation sends \(i\) to \(-i\), so

\[
  U^\dagger=\begin{pmatrix}-i&0\\0&i\end{pmatrix}.
\]

Diagonal multiplication and \(i^2=-1\) give

\[
  U^\dagger U
  =\begin{pmatrix}(-i)i&0\\0&i(-i)\end{pmatrix}
  =I.
\]

Also

\[
  \det U=i(-i)=1.
\]

The matrix \(X\) is real symmetric, hence Hermitian. Direct multiplication gives

\[
  UXU^\dagger
  =
  \begin{pmatrix}i&0\\0&-i\end{pmatrix}
  \begin{pmatrix}0&1\\1&0\end{pmatrix}
  \begin{pmatrix}-i&0\\0&i\end{pmatrix}
  =
  \begin{pmatrix}0&-1\\-1&0\end{pmatrix}
  =-X.
\]

Since \(X_{01}=1\), \(X\neq0\), hence \(-X\neq X\). Thus \(U\notin\ker\rho\), proving the
claim.

## Lorentz identification

Every \(x\in H_2(\mathbb C)\) has a unique Pauli decomposition

\[
  x=x^0I+x^1\sigma_1+x^2\sigma_2+x^3\sigma_3,
\]

and

\[
  \det x=(x^0)^2-(x^1)^2-(x^2)^2-(x^3)^2.
\]

The action \(x\mapsto gxg^\dagger\) for \(g\in SL(2,\mathbb C)\) is the spin double cover of
the proper orthochronous Lorentz action. Its \(SU(2)\) subgroup fixes \(x^0\) and acts on
\((x^1,x^2,x^3)\) by ordinary spatial rotations. The witness above is a half-turn sending the
\(\sigma_1\) direction to its negative.

This paragraph is `[LITERATURE]`; the finite nontriviality witness is all that is needed for the
kernel no-go.

## Application boundary

Baez--Schwahn's canonical nested-pair formulas make the first \(SU(3)\) factor act on
\(H_3(\mathbb C)\) by \(Y\mapsto gYg^\dagger\). Its subgroup preserving the upper
\(H_2(\mathbb C)\) corner contains the electroweak \(SU(2)\), acting by the same conjugation
representation used above.

Therefore a proposed exact sequence

\[
  1\to G_{\rm SM}\to K\to SO^+(1,3)\to1
\]

cannot use restriction to that same \(H_2(\mathbb C)\) as its last map while placing the full
electroweak \(SU(2)\) in the kernel.

The theorem does **not** exclude:

1. an independent Lorentz action on a distinct, canonically related Peirce corner;
2. a non-product group in which weak \(SU(2)\) is literally identified with a chiral spacetime
   rotation, provided the resulting dynamics matches experiment;
3. exceptional-Jordan algebra as an internal algebra without identifying this qubit corner with
   spacetime.

## Strongest positive survivor

Any exceptional-Jordan unification must construct two physically distinct actions:

- an external Lorentz action defining causal geometry;
- an internal weak action on particle multiplets.

Their relationship must be derived from Jordan-frame, Peirce, triality, or structure-group data.
Merely observing that \(H_2(\mathbb C)\) is both a qubit algebra and a Minkowski vector space
identifies the two \(SU(2)\) actions instead of unifying independent forces.

## Lean formalization

Module:

`GaloisForLFunctions.HTGeometry.WeakLorentzOverlap`

Unconditional certificates:

- explicit \(U\), \(X\), and conjugation action;
- \(U^\dagger U=1\);
- \(\det U=1\);
- \(X^\dagger=X\);
- \(UXU^\dagger=-X\);
- \(UXU^\dagger\neq X\);
- the full conjugation action is not pointwise trivial on the same corner.

Foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/WeakLorentzOverlap.lean
```

passed. A separate `/tmp` audit reports exactly
`[propext, Classical.choice, Quot.sound]` for every theorem and no project axiom.

## Primary source

- J. C. Baez and P. Schwahn, *The Standard Model Gauge Group from the Exceptional Jordan
  Algebra*, especially the explicit
  \((g,h):(Y,M)\mapsto(gYg^\dagger,hMg^\dagger)\) action,
  <https://arxiv.org/abs/2606.15235>.

## Gates

- [x] source formula identified
- [x] exact finite theorem and proof dependency-closed
- [x] physical application boundary stated
- [x] strongest positive survivor extracted
- [x] Lean theorem suite
- [x] axiom audit
- [x] repository-wide formal lint

## Log

- 2026-07-28 — extracted while hostile-testing the same-\(H_2(\mathbb C)\) spacetime/gauge
  identification.
- 2026-07-28 — formalized as
  `GaloisForLFunctions.HTGeometry.WeakLorentzOverlap`; direct foreground Lean check and separate
  axiom audit passed; repository-wide formal lint passed.
