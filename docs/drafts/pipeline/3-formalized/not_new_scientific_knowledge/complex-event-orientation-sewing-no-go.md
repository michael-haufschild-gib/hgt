# A nonzero complex event passage synchronizes endpoint orientations

- **ID:** `complex-event-orientation-sewing-no-go`
- **Stage:** 3-formalized
- **Type:** EXACT ORIENTATION-SEWING RIGIDITY / UNIVERSAL-LAW NO-GO
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL LEAN] [STANDARD ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/actuality-creates-future-law.md`
- **Failed route:** `../../5-failed/complex-orientation-sign-defect-as-force.md`
- **Lean target:**
  `GaloisForLFunctions.HTGeometry.ComplexEventOrientationSewingNoGo`

## Statement

Let
\[
\rho(X)=
\begin{pmatrix}
\operatorname{Re}X&-\operatorname{Im}X\\
\operatorname{Im}X&\operatorname{Re}X
\end{pmatrix},
\qquad
J_k=
\begin{pmatrix}0&-I_k\\I_k&0\end{pmatrix}.
\]
For every finite complex matrix \(X\in M_{m,n}(\mathbb C)\),
\[
J_m\rho(X)=\rho(X)J_n.
\tag{1}
\]

Joint orientation reversal preserves `(1)`:
\[
\boxed{
(-J_m)\rho(X)=\rho(X)(-J_n).
}
\tag{2}
\]

One-sided orientation reversal is rigid:
\[
\boxed{
J_m\rho(X)=\rho(X)(-J_n)
\iff X=0,
}
\tag{3}
\]
\[
\boxed{
(-J_m)\rho(X)=\rho(X)J_n
\iff X=0.
}
\tag{4}
\]

Thus every nonzero realified complex passage requires the same orientation sign at its two
endpoints.

## Dependency-closed proof

Negating both sides of `(1)` and using
\[
(-J_m)\rho(X)=-(J_m\rho(X)),
\qquad
\rho(X)(-J_n)=-(\rho(X)J_n)
\]
proves `(2)`.

Assume the left side of `(3)`. Matrix multiplication by a negative matrix gives
\[
J_m\rho(X)=-\rho(X)J_n.
\tag{5}
\]
Combining `(5)` with `(1)` yields
\[
\rho(X)J_n=-\rho(X)J_n.
\tag{6}
\]
The realification theorem identifies both sides with
\[
\rho(iX)=-\rho(iX).
\tag{7}
\]
Equality of the upper-right blocks in `(7)` gives
\[
-\operatorname{Re}X=\operatorname{Re}X,
\]
and equality of upper-left blocks gives
\[
-\operatorname{Im}X=\operatorname{Im}X.
\]
Over \(\mathbb R\), both parts vanish, so \(X=0\). The converse is immediate. Negating a
one-sided source-reversal equation converts it into `(3)`, proving `(4)`.

## Exact no-go

The first orientation-descent proposal tried to make the sign of local complex structure carry a
nontrivial force-producing sewing defect.

Equations `(2)`--`(4)` kill that proposal for ordinary complex-linear event passages:

```text
joint sign reversal -> exact symmetry;
one-sided sign reversal + nonzero passage -> impossible.
```

A sign mismatch is not a small curvature. It annihilates the passage.

This does not rule out topology of a separate orientation bundle, anti-linear transitions,
singular event interfaces, or higher noninvertible sewing. It proves that those structures cannot
be replaced by ordinary nonzero complex-linear intertwiners with independently chosen endpoint
signs.

## Strongest positive survivor

The exact survivor is **orientation synchronization by nonzero passage**. It identifies the
minimum additional structure required for any richer defect:

```text
ordinary J-intertwiner
  -> synchronized Z₂ orientation;

nontrivial actuality defect
  -> must involve semilinearity, noninvertibility, quadratic target creation,
     higher interchange, or a source boundary not reducible to endpoint signs.
```

Combined with earlier no-go theorems:

1. static event square does not select \(\mathbb C\);
2. a generated \(J\) does not select connection; and
3. a one-sided \(J\)-sign mismatch kills every nonzero complex-linear passage.

Therefore the universal-law target must live in the complete causalization cell and its
composition, not in the scalar field or orientation line alone.

## Hostile audit

This is elementary block linear algebra. It proves no physical synchronization, force, spacetime,
or gravity. It assumes finite complex matrices, their doubled-real representation, and canonical
complex structures.

It does **not** prove:

- that physical events are complex-linear passages;
- that a source generates endpoint \(J\)'s;
- that orientation has only two physical values;
- that anti-linear or singular passages occur;
- a connection, holonomy, or curvature;
- the master loss--future identity; or
- a new observable.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/ComplexEventOrientationSewingNoGo.lean`.

Declarations:

- `complexMatrixRealification_zero`;
- `complexMatrixRealification_joint_orientation_reversal`;
- `complexMatrixRealification_target_orientation_reversal_iff_zero`; and
- `complexMatrixRealification_source_orientation_reversal_iff_zero`.

Direct foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ComplexEventOrientationSewingNoGo.lean
```

completed with exit code zero and no warnings.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.ComplexEventOrientationSewingNoGo
✔ [1273/1273] Built GaloisForLFunctions.HTGeometry.ComplexEventOrientationSewingNoGo
Build completed successfully (1273 jobs).
```

`#print axioms` for all four declarations reports only `propext`, `Classical.choice`, and
`Quot.sound`. The module has no forbidden declaration and is reachable from the
`GaloisForLFunctions.HTGeometry` umbrella. Repository formal lint passed with only pre-existing
large-file warnings.

## Gates

- [x] exact statement
- [x] dependency-closed proof
- [x] exact killed route
- [x] strongest nontrivial positive survivor
- [x] hostile novelty classification
- [x] unconditional Lean formalization
- [x] direct foreground source check
- [x] focused final build
- [x] axiom audit
- [x] repository formal lint

## Log

- 2026-07-30 — proved joint reversal symmetry and one-sided reversal rigidity.
- 2026-07-30 — retired local orientation-sign mismatch as a force-producing defect.
- 2026-07-30 — extracted noninvertible/semilinear/higher causalization sewing as the surviving
  open location.
- 2026-07-30 — focused `1273/1273` build, axiom audit, and repository formal lint passed.
