# Exact finite dyadic coordinates of complete cell sources

## Statement

For actual W=logCellShift 2 and the normalized balanced details d_a,

e_(2a)=alpha_a W e_a+beta_a d_a,
e_(2a+1)=beta_a W e_a-alpha_a d_a.

Every finite linear combination of standard complete cells is an exact finite
linear combination of W^j e_1 and W^j d_a. These generators form an orthonormal
Hilbert basis of l2(N+;C). The resulting coordinate map is an isometric
isomorphism onto l2(N x Option(N+);C), with coordinates given by the literal
generator inner products.

## Proof

The unit identity alpha_a^2+beta_a^2=1 inverts the cell-pair rotation. The algebraic
span of all translated generators is W-invariant by linearity. Strong induction
in the integer label places each e_m in this span: m=1 is the root generator;
otherwise its parent floor(m/2) is positive and smaller, and the inverse rotation
supplies the required child. Finite summation gives a finitely supported
coefficient representation for every finite source.

Same-level orthonormality comes from the explicit wandering basis; different
levels are orthogonal by the actual cell-clock theorem. The standard cell basis
has dense span and lies in the algebraic dyadic span. This proves completeness
and constructs the coordinate isometry without a quotient or an assumed
exhaustion statement.

## Lean

Module:
formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/EveryFiniteCellSourceHasFiniteDyadicCoordinates.lean

Capstones:

- exists_finite_logCellDyadic_expansion
- orthonormal_logCellDyadicOrbit
- logCellDyadicFiniteSpan_dense
- logCellDyadicCoordinates

Final individual no-olean audit passes. All capstones use only propext,
Classical.choice and Quot.sound. The module is wired into its umbrella.

## Scope

Finite compact cell sources require no infinite expansion to obtain these
coordinates. The completed statement concerns the actual logarithmic-cell
Hilbert space. Passing Gamma or the Weil form through a general infinite
expansion still requires its own domain and convergence theorem. Physical
balanced-Haar normalization, one-reserve Gamma payment and selective full-form
sign remain separate obligations.
