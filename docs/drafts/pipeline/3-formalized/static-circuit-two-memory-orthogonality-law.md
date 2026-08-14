# Static--circuit two-memory orthogonality law

- **ID:** `static-circuit-two-memory-orthogonality-law-formalized`
- **Stage:** 3 -- formalized
- **Type:** universal Hilbert-space theorem / shortcut threshold / recurrence realignment
- **Status:** `[LEAN-FORMALIZED] [NO FINITE-DIMENSIONALITY] [BROWN RATE STILL OPEN]`
- **Source:** `formal/GaloisForLFunctions/HTGeometry/StaticCircuitTwoMemoryOrthogonalityLaw.lean`
- **Parent paper proof:** `../2-fully-proven/static-circuit-two-memory-orthogonality-law.md`

## Exact formal result

Let `PiOp` and `P` be nested orthogonal projections on a real or complex Hilbert space, let `U` be
a linear isometric equivalence that fixes the `P` sector, let `x` be a seed, and let `y` have the
same `PiOp` projection as `x`.  Define

\[
u=\Pi x,\qquad c=Px-\Pi x,\qquad r=Ux-Px,\qquad q=y-\Pi x.
\]

Lean proves

\[
\langle Ux,y\rangle
=\langle u,u\rangle+\langle c,q\rangle+\langle r,q\rangle,
\]

with `u` orthogonal to `c`, `r`, and `q`, and `c` orthogonal to `r`.  It also proves

\[
\langle Px,y\rangle=\langle u,u\rangle+\langle c,q\rangle,
\qquad
\langle(U-P)x,y\rangle=\langle r,q\rangle,
\]

and, when `U` fixes `P` pointwise,

\[
\|c\|^2+\|r\|^2=\|x-\Pi x\|^2.
\]

For a finite real-Hilbert target dictionary, every nonnegative target collision of size at least
`a` forces dynamic/preparation alignment by at least

\[
|I|^{-1}a-(\langle u,u\rangle+\langle c,q\rangle).
\]

At exact recurrence, if the normalized seed is one dictionary target, `a=1`; hence recurrence
forces realignment by one inverse dictionary size minus the completed baseline.

## Formal declarations

- `universal_static_inner_eq_zero`
- `universal_dynamic_inner_eq_zero`
- `universal_preparation_inner_eq_zero`
- `static_dynamic_inner_eq_zero`
- `twoMemory_collision`
- `twoMemory_completedBaseline`
- `twoMemory_dynamicCorrection`
- `twoMemory_norm_conservation`
- `projection_preparation_pow_invariant`
- `one_target_forces_memory_realign`
- `recurrence_forces_memory_realign`

The exact bounded-dependence local-circuit composition is formalized separately in
`local-circuit-two-memory-capacity-law.md`.

## Boundary

This is an exact universal mechanism, not a Brown--Susskind rate theorem.  It proves that retained
non-Haar norm and circuit hardness are compatible, and identifies the only time-dependent scalar
that a growth proof must control.  It does not yet prove quenched decay of that alignment for an
ordinary local-Hamiltonian ensemble, instantiate the abstract target vectors as tensor-power
Hermitian circuit moments, prove the ensemble Bochner identity, or formalize the all-replica
zero-temperature limit.

## Verification

- foreground check: `lake env lean GaloisForLFunctions/HTGeometry/StaticCircuitTwoMemoryOrthogonalityLaw.lean`;
- umbrella import: `GaloisForLFunctions.HTGeometry`;
- final build: `lake build GaloisForLFunctions.HTGeometry.StaticCircuitTwoMemoryOrthogonalityLaw`
  (`2623/2623`);
- axiom audit of collision, norm conservation, target forcing, and recurrence realignment: only
  `propext`, `Classical.choice`, and `Quot.sound`.
