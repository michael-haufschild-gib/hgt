# Reflection grades the complete pair-face signature by a twisted fixed submodule

- **ID:** `reflection-graded-pair-face-signature`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[BRIDGE]` -- finite-group averaging and affine principal-part transport
  are standard; Lean audit corrected the orbital-orientation sign and completed the exact
  reflection-fixed classification against the proved all-depth parent theorem.
- **Parent:** `all-depth-pair-face-signature-completeness`
- **Statement:** For a reflection-symmetric meromorphic function with constant full mixed
  difference, the complete pair-face signature lies in a canonically twisted reflection-fixed
  submodule. Every compatible signature in that fixed submodule is realized by a
  reflection-symmetric constrained function, and the kernel is exactly the reflection-symmetric
  differentially algebraic class.

## Setup

Let `d >= 2`, let `1,tau_1,...,tau_d` be linearly independent over `Q`, and let `Q_d` be the
additive mixed-constraint class from the parent card:

```text
F(z+1)=F(z),
Delta_1 ... Delta_d F in C,
Delta_i F(z)=F(z+tau_i)-F(z).
```

Write

```text
R F(z)=F(1-z)
```

and let `Q_d^R` be the fixed class `R F=F`. For a pair `{i,j}`, put

```text
C_ij={1,...,d}\{i,j},
sigma_ij=sum_(k in C_ij) tau_k,
W_ij(F)=product_(k in C_ij) Delta_k F.
```

The parent complete invariant is

```text
PairFace_d(F)=(R_2^(ij)(W_ij(F)))_(i<j) in Comp_d.
```

## Unconditional reflection--difference identity `[PROVED HERE + Lean]`

For a finite ordered direction list `tau=(tau_1,...,tau_n)`, write

```text
D_tau=Delta_(tau_1)...Delta_(tau_n),
Sigma_tau=sum tau_k.
```

If `F(2c-z)=epsilon F(z)`, then

```text
D_tau F(2(c-Sigma_tau/2)-z)
  =(-1)^n epsilon D_tau F(z).                         (1)
```

One difference is the identity

```text
Delta_tau F(2(c-tau/2)-z)
 =F(2c-z)-F(2c-(z+tau))
 =-epsilon Delta_tau F(z).
```

Induction proves (1). No commensurability, convergence, continuation, or limiting hypothesis is
used.

If `F` is entire and symmetric, differentiation of (1) gives the all-order face-jet selection law

```text
(d/dz)^m D_tau F(c-Sigma_tau/2)=0
whenever m+n is odd.                                   (2)
```

If the face is not identically zero, its vanishing order at the shifted centre is even for even
`n` and odd for odd `n`.

Lean module:

```text
formal/GaloisForLFunctions/RHTower/ReflectionDifferenceFaces.lean
```

Capstones:

- `iteratedForwardDifference_signed_reflection`;
- `iteratedDeriv_iteratedForwardDifference_center_eq_zero_of_odd`;
- `analyticOrderAt_iteratedForwardDifference_even_of_symmetric`;
- `analyticOrderAt_iteratedForwardDifference_odd_of_symmetric`.

The exact module builds successfully. All four capstones have axiom footprint
`[propext, Classical.choice, Quot.sound]`.

## The component reflection involution

For the pair `{i,j}`, define the affine involution

```text
r_ij(z)=1-sigma_ij-z.                                   (3)
```

It preserves the pair lattice modulo sign. Affine pullback by `r_ij` preserves the depth-two DA
kernel, so depth-two completeness induces an involution

```text
J_ij : A_ij -> A_ij,
J_ij R_2(U)=R_2(U o r_ij).                              (4)
```

This definition is independent of the representative: if two depth-two functions have the same
residue, their difference is DA; affine reflection preserves DA, so their reflected residues also
agree. Since `r_ij^2=id`, `J_ij^2=id`.

The pair-face signature is the orbital sum of the boundary
`U(z+tau_i)-U(z)`. Reflection both sends a principal part of order `k` to its affine reflected
principal part with coefficient `(-1)^k` **and reverses this oriented boundary**. Consequently the
actual component action on the order `ell=-k<0` signature is

```text
(J_ij D)(ell,p)=-(-1)^k D(ell,r_ij(p)).                (4')
```

The extra minus sign is forced by

```text
(U o r_ij)(z+tau_i)-(U o r_ij)(z)
  =-[U(y+tau_i)-U(y)],  y=r_ij(z)-tau_i,
```

followed by reindexing the bilateral orbit sum. The earlier draft omitted this orientation sign;
the independent Lean audit detected and corrected it. Formula (4') is involutive.

Put

```text
K_ij=(-1)^(d-2) J_ij.                                  (5)
```

The family `K=(K_ij)` preserves triple compatibility, because it is induced by the single
reflection `R` on `Q_d`. Hence it defines an involution of `Comp_d`.

## Equivariance `[PROVED HERE]`

The operator identity underlying (1), without assuming `R F=F`, is

```text
W_ij(R F)(z)=(-1)^(d-2) W_ij(F)(1-sigma_ij-z).          (6)
```

Applying `R_2^(ij)` gives

```text
PairFace_d(R F)=K PairFace_d(F).                        (7)
```

Reflection preserves `Q_d`: periodicity follows from period one, and the full `d`-fold difference
is sent to its constant value multiplied by `(-1)^d`. Reflection also preserves the DA subfield.

## Fixed-submodule classification `[PROVED + Lean]`

Define

```text
Comp_d^K={D in Comp_d:K D=D}.
```

Then the pair-face map induces an isomorphism

```text
Q_d^R/(Q_d^R intersect Mer_DA)  ~=  Comp_d^K.           (8)
```

### Necessity

If `R F=F`, equation (7) gives

```text
K PairFace_d(F)=PairFace_d(F).
```

### Kernel

Inside `Q_d^R`, zero pair signature is equivalent to DA by the parent completeness theorem. The
kernel is therefore exactly `Q_d^R intersect Mer_DA`.

### Surjectivity

Let `D in Comp_d^K`. Parent realization supplies `F_0 in Q_d` with

```text
PairFace_d(F_0)=D.
```

Since the coefficient field has characteristic zero, form the reflection average

```text
F=(F_0+R F_0)/2.
```

Then `R F=F`, and by (7),

```text
PairFace_d(F)
 =(D+K D)/2
 =D.
```

This proves (8).

## Scientific consequence

`[PROVED, CONDITIONAL ON PAIR-FACE COMPLETENESS]` Functional-equation reflection does not force the
complete pair-face obstruction to vanish. It grades the obstruction by the twisted involution `K`
and retains exactly its fixed submodule. The correct completed constraint object is therefore not
an ordinary differential matroid and not an ungraded pair-divisor module; it is the
reflection-graded pair-face module `(Comp_d,K)`.

At depth two, nonzero fixed signatures exist. In the corrected convention, an order-one class
divisor supported on the reflection-fixed class of `1/2` is fixed: principal-part parity and orbital
orientation contribute two minus signs. Depth-two realization and reflection averaging produce a
reflection-symmetric constrained meromorphic function with signature value `1` on that class. Thus
FE symmetry alone permits hypertranscendental pair-face charge.

For the RH program this is a route-sharpening theorem, not an RH implication. It proves that the
missing Euler input must do more than supply the FE involution: the exact Euler multiplicativity
constraint must force the particular completed Euler--Gamma class to be zero inside `Comp_d^K`.
That is now the source-completeness target. No operator, positivity cone, cutoff, or carrier limit
appears.

## Parent-theory and novelty attack

- Finite-difference parity of symmetric functions is standard and is graded `[BRIDGE]`.
- Exactness of fixed points for a finite group in characteristic zero is standard and is graded
  `[BRIDGE]`.
- Principal-part transport under an affine reflection is standard and is graded `[BRIDGE]`.
- The potentially new content is their combination with the complete all-depth triptic pair-face
  invariant: the explicit twisted involution, the exact fixed-submodule image, and realization of
  every reflection-compatible obstruction.

No scientific-novelty promotion is made. Equivalent, stronger, mechanism-level, and older-parent
literature searches remain required, together with independent audit of the parent depth-two
atomicity and all-depth completeness proofs.

## Gates

- [x] exact finite-difference reflection identity proved;
- [x] all-order face-jet parity proved;
- [x] analytic-order parity proved;
- [x] unconditional core formalized and axiom-audited in Lean;
- [x] component reflection involution defined and orbital-orientation sign independently audited;
- [x] pair-face equivariance proved on paper;
- [x] fixed-submodule kernel and realization proved on paper;
- [x] independent audit of the reflection action on the differential principal-part convention;
- [x] parent depth-two atomicity, all-depth completeness, and exact image reused as proved Lean
  theorems rather than exposed assumptions;
- [x] meromorphic pair-face residues and exact fixed-submodule theorem formalized;
- [x] explicit nonzero fixed signature and symmetric realization formalized;
- [x] classified `[BRIDGE]`; no scientific-priority claim is made.

## 2026-08-23 Stage 2 -> 3 formalization audit

- [x] `HTGeometry/ReflectionGradedPairFaceSignature.lean` proves affine Laurent-coefficient
  reflection, orbital-divisor transport, finite-difference reflection, and pair-signature
  equivariance.
- [x] `pairSigReflection` includes both principal-part parity and the independently audited orbital
  orientation sign; `pairSigReflection_involutive` proves it is an involution.
- [x] `reflectionSymmetricPairSigRealizable_iff` proves exact image equals admissible signatures
  fixed by this involution. Surjectivity uses the literal characteristic-zero reflection average
  and the existing unconditional all-depth exact-image theorem.
- [x] `differentialAlgebraicOver_iff_pairSig_zero_of_reflectionSymmetric` identifies the kernel with
  the reflection-symmetric differentially algebraic class using proved all-depth completeness.
- [x] `exists_reflectionSymmetric_depthTwo_nonzero_pairSig` gives a closed concrete realization at
  the distinct prime-log periods for `2` and `3`, with signature value `1` at order `-1` on the
  class of `1/2`.
- [x] Direct `lake env lean` and targeted
  `lake build GaloisForLFunctions.HTGeometry.ReflectionGradedPairFaceSignature` passed. No umbrella
  build was run.
- [x] `#print axioms` for all 24 new theorem declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- [x] Leaf module is wired into `GaloisForLFunctions.HTGeometry`.

No Lean proof obligation remains for the theorems claimed by this card.
