# Colour-Gram weak--Lorentz lock no-go

- **ID:** `color-gram-weak-lorentz-lock-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / HOSTILE BOUNDARY
- **Status:** `[LEAN-PROVEN] [REDISCOVERED] [NO-GO]`
- **Parent conjecture:** `../1-in-progress/color-blind-event-gram-spacetime-law.md`
- **Earlier boundary:** `same-qubit-weak-lorentz-overlap-no-go.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ColorGramWeakLorentzLock.lean`

## Exact theorem

Let
\[
U=\begin{pmatrix}i&0\\0&-i\end{pmatrix}.
\]
Then
\[
U^\dagger U=I,\qquad \det U=1,
\]
so \(U\) is an explicit \(SU(2)\) element.

Let \(X\in M_{3,2}(\mathbb C)\) be the one-row event
\[
X=\begin{pmatrix}1&1\\0&0\\0&0\end{pmatrix}.
\]
Its colour Gram matrix is
\[
G_X=X^\dagger X=
\begin{pmatrix}1&1\\1&1\end{pmatrix},
\]
which is the future-null vector \((t,x,y,z)=(1,1,0,0)\).

Right multiplication of the event by \(U^\dagger\) gives
\[
G_{XU^\dagger}
=UG_XU^\dagger
=\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
\]
the distinct future-null vector \((1,-1,0,0)\). Therefore
\[
G_{XU^\dagger}\ne G_X.
\]
In particular,
\[
\neg\left[\forall Y\in M_{3,2}(\mathbb C),\;
G_{YU^\dagger}=G_Y\right].
\]

More generally, the full right orbit of every event supported on one colour row remains
Lorentz-null. The witness therefore rotates **inside the actual positive Gram future cone**; it is
not an artifact of extending the action to indefinite Hermitian matrices.

## Physical no-go

Suppose the right \(SU(2)\) of the exceptional
\(M_{3,2}(\mathbb C)\) carrier is interpreted simultaneously as:

1. weak isospin, required to be internal; and
2. the compact spatial-frame subgroup acting on the derived Gram spacetime.

The explicit element \(U\) changes a physical future-null direction. Hence this same action is not
pointwise internal on the derived causal carrier. The single-factor construction cannot keep weak
gauge transformations internal while using the same right doublet as spacetime spin frame.

Quotienting by the full right \(U(2)\) does not repair the construction: it erases the spatial
orientation of \(G_X\) and leaves only its two eigenvalues. A four-dimensional causal carrier then
does not survive.

## Strongest positive survivor

A viable colour-blind event theory must contain structure beyond one
\(M_{3,2}(\mathbb C)\) representation:

- a second, canonically selected two-spinor action for Lorentz frame transport; or
- a noninvertible event interface whose kernel carries weak transport while its cokernel carries
  Lorentz transport; or
- an experimentally viable identification of weak and spatial rotations, which is presently
  incompatible with their observed roles.

The first two actions cannot be inserted as an unrelated product. Exceptional incidence,
Peirce/triality data, or event descent must derive both from one source.

## Lean realization

`ColorGramWeakLorentzLock.lean` proves:

- `colorGramWeakHalfTurn_conjTranspose_mul_self`;
- `colorGramWeakHalfTurn_det`;
- `singleColorEvent_mul`;
- `singleColorEvent_right_orbit_lorentz_null`;
- `weakLockedColorEvent_gram`;
- `weakLockedColorEvent_lorentz_null`;
- `colorGramWeakHalfTurn_conjugates_futureNullPlus`;
- `colorGramFutureNullMinus_ne_plus`;
- `colorGramWeakHalfTurn_moves_futureGram`;
- `colorGramWeakHalfTurn_moves_futureGram_via_event`;
- `colorGramWeakHalfTurn_not_in_pointwiseKernel`;
- `colorGramWeakHalfTurn_moved_event_lorentz_null`.

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ColorGramWeakLorentzLock.lean
lake build GaloisForLFunctions.HTGeometry.ColorGramWeakLorentzLock
```

Both pass. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Novelty boundary

The underlying statement that \(SU(2)\) acts as spatial rotations on
\(H_2(\mathbb C)\) is standard. The positive-Gram light-ray witness sharpens the corpus boundary
but is not claimed as new scientific knowledge.

## Gates

- [x] actual positive Gram-cone witness, not an indefinite extension
- [x] both original and moved events proved Lorentz-null
- [x] exact pointwise-kernel no-go
- [x] strongest positive survivor extracted
- [x] unconditional Lean formalization
- [x] focused source check, focused build, and axiom audit
- [ ] source-selected doubled action or noninvertible descent constructed

## Log

- 2026-07-29 — strengthened the prior same-corner witness to an explicit future-null event in the
  colour Gram image. Formalized the entire right-orbit null law and pointwise-kernel obstruction.
