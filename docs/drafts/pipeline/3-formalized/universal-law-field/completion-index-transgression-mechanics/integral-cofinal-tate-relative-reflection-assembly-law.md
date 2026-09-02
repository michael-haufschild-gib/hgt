# Integral cofinal Tate relative-reflection assembly law

- **ID:** `ULF-ICTRRA-1`
- **Stage:** 3-formalized
- **Type:** unconditional global source/completion assembly law
- **Status:** dependency-closed paper proof; Lean-certified in
  `GaloisForLFunctions.RHTower.IntegralCofinalTateRelativeReflectionAssembly`

## Statement

Over `R=Z[T,T^-1]`, finite Tate interval shift, zero-extension, and outgoing top boundary are
defined without field coefficients. Their naturality law is

`F_(m+1)i_m-i_mF_m=beta_m`.

For clock gain `u`, flat-minus-scaled defect is `(1-u)beta_m`. Canonical top readout of the
negated defects at `u=T` and `u=T^-1` gives exactly

`C_T=[[0,T-1],[T^-1-1,0]]`

at every stage.

Let `P=directSum_m R^2`. Acting by `C_T` on every stage defines one global `R`-linear operator
`D_T:P->P`. Then

`D_T^2=kappa id_P`, where `kappa=(T-1)(T^-1-1)`.

## Proof

Coordinate inspection proves the integral finite-shift naturality law. Scaling is central, so the
defect is `u beta_m`; subtracting from flat clock yields `(1-u)beta_m`. The top reader sends
`beta_m` to one, hence negated readouts at `T` and `T^-1` are the two Laurent arrows. The direct-sum
operator is stagewise matrix multiplication. Its square follows pointwise from
`C_T^2=kappa I`.

## Meaning

The higher object is now global and source-native. Completion curvature is not attached after
choosing a divisor: one integral curved Tate operator exists over every cofinal stage before any
physical character is evaluated.

## Boundary

No physical Xi completion or lattice landing is asserted. Remaining theorem must show that actual
Xi completion preserves the canonical integral top-coordinate module of this assembled operator.
That comparison cannot be defined by inserting a spectral grade or by asking for copywise compact
reduction.

## Dependency audit

- Integral Laurent source and inversion.
- Elementary finite vectors, shifts, zero-extension, Finsupp direct sums, and two-by-two matrices.
- `ULF-IRRCF-1` source Clifford law.
- No Xi zero, RH premise, physical evaluation, positivity, computation, added axiom, or landing
  assumption.
