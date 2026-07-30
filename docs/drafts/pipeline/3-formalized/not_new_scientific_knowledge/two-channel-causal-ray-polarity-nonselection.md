# Two-channel causal-ray polarity is not selected by positivity

- **ID:** `two-channel-causal-ray-polarity-nonselection`
- **Stage:** 3-formalized
- **Type:** exact no-go / positive polarity survivor
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE]`
- **Parent:** `../../1-in-progress/self-noncontainment-minimal-repair-law.md`
- **Lean target:** `GaloisForLFunctions.HTGeometry.CausalRayPolarityNonselection`

## Exact theorem

For a complex doublet \(H=(a,b)\in\mathbb C^2\), define its spin flip
\[
JH=(-\overline b,\overline a)
\tag{1}
\]
and its Hermitian outer square
\[
q(H)=HH^\dagger.
\tag{2}
\]
Then:

1. \(J^2H=-H\);
2. \(q(JH)=\operatorname{adj}(q(H))\);
3. \(q(H)q(JH)=0\);
4. both \(q(H)\) and \(q(JH)\) are positive semidefinite and Lorentz-null;
5. their time/Born-weight coordinate agrees:
   \[
   \tfrac12\operatorname{tr}q(JH)
   =
   \tfrac12\operatorname{tr}q(H);
   \tag{3}
   \]
6. the two rays need not agree. For \(H=(1,0)\),
   \[
   q(H)=
   \begin{pmatrix}1&0\\0&0\end{pmatrix},
   \qquad
   q(JH)=
   \begin{pmatrix}0&0\\0&1\end{pmatrix}.
   \tag{4}
   \]

Thus positivity, nullness, total squared amplitude, and phase blindness do not select the
orientation of an elementary two-channel causal ray.

## Paper proof

Applying `(1)` twice gives
\[
J^2(a,b)
=J(-\overline b,\overline a)
=(-a,-b).
\]
Direct multiplication gives
\[
q(JH)
=
\begin{pmatrix}
|b|^2&-a\overline b\\
-b\overline a&|a|^2
\end{pmatrix}
=\operatorname{adj}
\begin{pmatrix}
|a|^2&a\overline b\\
b\overline a&|b|^2
\end{pmatrix}.
\]
The adjugate identity
\[
q(H)\operatorname{adj}(q(H))
=\det(q(H))I
\]
and the rank-one identity \(\det q(H)=0\) prove item 3. Both matrices are outer squares, so they are
positive semidefinite and have determinant zero. Spin flip swaps \(|a|^2\) and \(|b|^2\), hence
preserves their sum and proves `(3)`. Substitution of \(H=(1,0)\) proves `(4)`. Every dependency is
closed.

## Hostile interpretation

This is standard two-spinor/adjugate mathematics. It is not a new causal law and does not prove
that either ray is physical spacetime.

Its exact use is negative:

> a local positive-null event square does not choose which of two complementary null directions
> is future.

The existing full \(GL(2,\mathbb C)\)-congruence theorem uniquely forces the direct Gram record up
to scale. This card shows why that stronger noncompact covariance cannot be replaced by unitary
symmetry, positivity, nullness, or scalar Born weight. A background-free event law must generate
causal orientation or source polarity before it can claim to derive spacetime.

## Gates

- [x] exact theorem frozen
- [x] dependency-closed paper proof
- [x] hostile status `REDISCOVERED / BRIDGE`
- [x] exact Lean formalization
- [x] axiom audit; only `propext`, `Classical.choice`, and `Quot.sound`
- [x] targeted final build:
  `lake build GaloisForLFunctions.HTGeometry.CausalRayPolarityNonselection`
- [ ] repository-wide lint clean; blocked by pre-existing unreachable modules outside this card

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.CausalRayPolarityNonselection`
- **Direct check:** `lake env lean
  GaloisForLFunctions/HTGeometry/CausalRayPolarityNonselection.lean`
- **Target build:** passed, `3007/3007`
- **Formal scope:** spin-flip square, adjugate outer-square identity, mutual annihilation,
  positivity, nullness, equal time coordinate, and explicit distinct-ray witness
- **Excluded:** physical future orientation, source polarity, and causal-germ rigidity

## Log

- 2026-07-30 — extracted while attacking uniqueness of the source-positive causal Hessian.
  Positive direct and spin-flipped outer squares expose a two-valued causal-orientation boundary.
