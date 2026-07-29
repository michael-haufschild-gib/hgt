# A unitary source-event reciprocal square is only transported polarity

- **ID:** source-event-reciprocal-square-flatness
- **Stage:** 3-formalized
- **Type:** THEOREM + NO-GO (paper + Lean)
- **Parent:** `source-odd-positivity-square-law.md`
- **Statement:** In the complete finite unitary event model, the canonical transmuting map has
  source record and unitarily transported target record as its reciprocal squares. Both squares
  are sharp projections, so this construction carries no dynamical spectrum or curvature.
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/SourceEventReciprocalSquareFlatness.lean`

## Goal

Test whether the existing source involution plus complete event colligation already produces the
differential required by the reciprocal-square conjecture, rather than merely allowing an
arbitrary \(D\).

## Gates

- [x] exact source-derived finite model
- [x] dependency-closed paper proof `[PROVED HERE]`
- [x] unconditional Lean theorem `sourceEvent_reciprocalSquareLaw`
- [x] final target build and axiom audit
- [ ] generated index and project-wide lint
- [ ] physical non-flat replacement

## Setup

Let

\[
A^2=I,\qquad A^\dagger=A,\qquad
U^\dagger U=UU^\dagger=I.
\]

Define source record projection and canonical transmuting map

\[
P=\frac{I-A}{2},\qquad D=UP.                                  \tag{ES1}
\]

Transport the source involution to the target:

\[
A_{\rm out}=UAU^\dagger.                                      \tag{ES2}
\]

Then \(A_{\rm out}\) is again a self-adjoint involution.

## Finite source-event reciprocal-square theorem

`[PROVED HERE]`

The reciprocal squares of the canonical event transfer are

\[
\boxed{
D^\dagger D=P,\qquad
DD^\dagger=\frac{I-A_{\rm out}}2=UPU^\dagger.
}                                                             \tag{ES3}
\]

Consequently, source and target record projections have equal rank.

### Proof

Using unitarity, self-adjointness, and idempotence of \(P\),

\[
D^\dagger D
=PU^\dagger UP
=P^2
=P,
\]

and

\[
DD^\dagger
=UPP U^\dagger
=UPU^\dagger.
\]

Finally,

\[
\frac{I-UAU^\dagger}{2}
=U\frac{I-A}{2}U^\dagger
=UPU^\dagger,
\]

where \(UU^\dagger=I\). This proves `(ES3)`.

## Exact killing mechanism

The finite unitary source event realizes the algebraic shape of the reciprocal-square law, but
only trivially:

```text
source record projector P
        -- unitary relabelling U -->
target record projector UPU†.
```

Both squares have spectrum contained in \(\{0,1\}\). Their equality of rank is kinematic. A
single complete unitary colligation supplies no variable spectral weights, no curvature, no
relative coupling, and no gravitational dynamics.

This is the one-event counterpart of the existing result that globally supplied fixed-carrier
unitary completion memories form a strict coboundary with trivial triangular holonomy.

## Strongest positive survivor

The source does canonically generate a transfer:

\[
D=UP.
\]

It exactly identifies lost source record with created target record. Therefore arbitrary-\(D\)
freedom is not the first obstruction. The first missing datum is a **non-flat weight/composition
law beyond sharp unitary transport**.

Possible escape routes, each still open:

1. source-derived non-isometric weights on the transmuting map;
2. open/CP event dynamics whose minimal dilation is not treated as physical fixed carrier;
3. unbounded or higher differential with nontrivial singular spectrum;
4. composition across event-generated categories, where no global \(U\) identifies source and
   target; or
5. higher incompatibility tensors whose reciprocal square is not determined by \(P\) alone.

## Lean certificate

`[LEAN-PROVED]`

Declarations:

- `transportedSourceInvolution`
- `transportedSourceInvolution_conjTranspose`
- `transportedSourceInvolution_mul_self`
- `transportedSourceInvolution_recordProjection`
- `sourceEvent_reciprocalSquareLaw`
- `sourceEvent_reciprocalSquare_rank_eq_record`

No `sorry`, `admit`, axiom declaration, opaque declaration, unsafe declaration, or
computation-based proof appears in the module.
Final audit:

```text
lake build GaloisForLFunctions.HTGeometry.SourceEventReciprocalSquareFlatness
✔ Built GaloisForLFunctions.HTGeometry.SourceEventReciprocalSquareFlatness
Build completed successfully (3184 jobs).
```

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile novelty audit

This is standard partial-isometry and unitary-conjugation algebra. Door grade: `[BRIDGE]`.

It does not prove that record is spacetime, that target projection is gravity, or that a physical
event is described by \(U\). Calling `(ES3)` unification would be false.

## New insight for the universal law

The universal differential cannot be only the sharp transmuting partial isometry of a
fixed-carrier unitary completion. That object already exists and is flat. The discovery must
explain where nontrivial singular values and non-coboundary composition come from while retaining
the exact source/target record pairing.

In concise form:

> **Actuality supplies the arrow; higher incompatibility must supply its weight.**

## Log

- 2026-07-29 — identified canonical finite transfer \(D=UP\).
- 2026-07-29 — proved its reciprocal squares are exactly source and transported target record
  projections.
- 2026-07-29 — isolated sharp-projector flatness as the next no-go boundary.
- 2026-07-29 — final target build and axiom audit passed.
