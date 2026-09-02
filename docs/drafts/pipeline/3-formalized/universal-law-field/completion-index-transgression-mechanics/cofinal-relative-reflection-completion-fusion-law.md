# Cofinal relative-reflection completion fusion law

- **ID:** `ULF-CRRCF-1`
- **Stage:** 3-formalized
- **Type:** unconditional source/reflection/Gamma/cofinal-completion fusion law
- **Status:** dependency-closed paper proof; Lean-certified in
  `GaloisForLFunctions.RHTower.CofinalRelativeReflectionCompletionFusion`

## Statement

At Tate stage `m`, write `F_m` for finite forward shift, `i_m` for zero-extension, and

`beta_m=F_(m+1)i_m-i_mF_m`

for the rank-one new top boundary. Scaling both finite arrows by `u` gives naturality defect
`u beta_m`; hence flat-minus-scaled defect is

`A_m(u)=(1-u) beta_m`.

The canonical top-coordinate reader sends `beta_m` to one. Assemble the negatives of its readouts
at reciprocal Gamma clocks `u=exp(a), exp(-a)` as an odd two-by-two matrix. At every `m` this matrix
is exactly

`C_a=[[0,exp(a)-1],[exp(-a)-1,0]]=R_a-R`.

Therefore:

1. the paired completion anomaly squares to `-K(a) I`;
2. its determinant is positive curvature `K(a)=2(cosh a-1)`;
3. this determinant equals physical evaluation of the universal integral Laurent determinant
   `det C_T`, where `C_T=[[0,T-1],[T^-1-1,0]]`.

## Proof

Finite-shift naturality gives `delta_m(u)=u beta_m`; subtraction gives
`A_m(u)=(1-u)beta_m`. Since top readout of `beta_m` is one, negative readout is `u-1`. Reciprocal
clocks therefore give the two off-diagonal entries of `C_a`. The square and determinant follow
from the already proved curved-suspension laws. `ULF-IRRCF-1` identifies the same determinant with
evaluation of the integral Laurent source matrix.

## Meaning

The quadratic ghost is not merely compatible with completion. It is exactly the determinant of
failure of reciprocal formation clocks to commute with cofinal zero-extension. Curvature is born
only in the new top coordinate and is retained coefficient-faithfully at every stage.

## Boundary

This theorem constructs no integral physical top-coordinate lattice and proves no RH statement.
It shows exactly where a global strictness theorem must act: on assembled cofinal naturality
defects before divisor specialization, not on a fitted Xi fibre.

## Dependency audit

- Literal finite Tate shift/inclusion naturality defect and top-boundary basis theorem.
- Exact Gamma boundary legs and curved-suspension square/determinant.
- Integral Laurent relative-reflection determinant evaluation.
- No Xi zero, RH premise, positivity assumption, numerical computation, added axiom, or integral
  landing premise.
