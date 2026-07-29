# The primitive Albert Hessian is not the rank-six event

- **ID:** `albert-hessian-as-rank-six-event`
- **Stage:** 5-failed
- **Type:** FAILED SOURCE-NATURAL EVENT REALIZATION / POSITIVE SURVIVOR
- **Parent:** `../1-in-progress/actuality-creates-future-law.md`
- **Scientific status:** `[FALSIFIED] [BRIDGE]`

## Failed claim

`[FALSIFIED]`

The Hessian of the Albert cubic norm at the primitive actualization idempotent is the desired
rank-six ten-to-ten event map, so its kernel and cokernel directly supply the `4/6/4` event.

## Exact killing mechanism

For the standard primitive idempotent

\[
p=\operatorname{diag}(1,0,0)
\]

and Peirce-zero corner \(A=H_2(\mathbb O)\), the cubic norm obeys

\[
N(p+X)=\det_2(X),\qquad X\in A.
\]

Consequently,

\[
\frac12D^2N_p(X,X)=\det_2(X).
\]

The determinant quadratic on \(H_2(\mathbb O)\) is the ten-dimensional Lorentz spin-factor form
of signature \((1,9)\). It is nondegenerate. Therefore its polar map

\[
A\longrightarrow A^*
\]

has rank ten and zero kernel and cokernel. It cannot be the rank-six event.

The same fact is visible on the complex nested corner in
`formal/GaloisForLFunctions/HTGeometry/ExceptionalCubicLorentzSlice.lean`: the Hessian restricts
to the nondegenerate \(1+3\) Minkowski form, not a rank-deficient conversion.

## Representation lesson

Two exact structures had been conflated:

1. the Albert Hessian supplies the quadratic metric on an outgoing Jordan corner;
2. the compatible pure-pair product involution supplies the `6+4` fracture.

One object need not perform both jobs through the same linear map. A viable event law must derive
both from one source while preserving their distinct mathematical roles.

## Strongest positive survivor

Krasnov's compatible pure pair determines two commuting orthogonal complex structures on
\(\mathbb R^{10}\). Their product is an orthogonal involution \(A\) with six-dimensional
\(+1\)-eigenspace and four-dimensional \(-1\)-eigenspace. Hence

\[
C_A=\frac{1+A}{2},\qquad R_A=\frac{1-A}{2}
\]

are source-derived complementary projections of ranks six and four. They satisfy

\[
C_A+R_A=1,\qquad C_AR_A=R_AC_A=0.
\]

The record \(R_A\) is not an arbitrary dilation: it is the unique complementary spectral
projection selected by \(A\). Its range equals \(\ker C_A\), and it canonically represents
\(\operatorname{coker}C_A\).

This is ordinary spectral-projector algebra and Krasnov's `6+4` product structure, not new
mathematics. Its new research role is to replace the arbitrary maximal-rank event map in the
physical conjecture by a source-selected candidate.

## Why the survivor does not prove physics

- the projections only decompose a parent carrier; they do not prove creation of spacetime;
- the four-record initially inherits no Lorentzian metric or time orientation;
- the pure pair has not been derived as an actual quantum event;
- no completely positive channel, probability law, causal composition, connection, or dynamics
  follows;
- fixed-carrier and same-qubit weak--Lorentz no-goes still apply unless the record is transported
  into a distinct outgoing physical role.

## Survivor status

- paper theorem: dependency-closed;
- novelty: `[REDISCOVERED] [BRIDGE]`;
- Lean status: `[LEAN-PROVED]` in
  `formal/GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean`;
- physical selector: open.

## Primary source

- K. Krasnov, *Geometry of Spin(10) Symmetry Breaking*, J. Math. Phys. **65** (2024),
  arXiv:2209.05088. Compatible pure spinors determine commuting complex structures whose product
  gives \(\mathbb R^{10}=\mathbb R^6\oplus\mathbb R^4\).

## Log

- 2026-07-29 — killed the tempting identification of the primitive Albert Hessian with the
  rank-six event by its nondegenerate \((1,9)\) restriction.
- 2026-07-29 — extracted the compatible-pair spectral projections as the source-natural positive
  survivor.
- 2026-07-29 — formalized the positive survivor, including canonical cokernel realization and
  trace-two `4/6/4` index, unconditionally in Lean.
