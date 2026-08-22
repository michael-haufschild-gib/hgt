# Reflection grades the complete pair-face signature by a twisted fixed submodule

- **ID:** `reflection-graded-pair-face-signature`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper), conditional on pair-face completeness
- **Scientific status:** `[NOVELTY UNVERIFIED]` -- the fixed-point algebra is standard in
  characteristic zero, but no parent theorem has yet been checked for the reflection-equivariant
  classification of the complete triptic pair-face invariant.
- **Parent:** `all-depth-pair-face-signature-completeness`
- **Statement:** For a reflection-symmetric meromorphic function with constant full mixed
  difference, the complete pair-face signature lies in a canonically twisted reflection-fixed
  submodule. Conditional on the parent pair-face completeness theorem, every compatible signature
  in that fixed submodule is realized by a reflection-symmetric constrained function, and the
  kernel is exactly the reflection-symmetric differentially algebraic class.

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

For an explicit principal part `a_(u,k)(z-u)^(-k)`, the affine reflection sends the label `u` to
`r_ij(u)` and multiplies the order-`k` coefficient by `(-1)^k`. Thus (4) is the ordinary reflected
principal-part involution, not a newly imposed quotient.

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

## Fixed-submodule classification `[PROVED HERE, CONDITIONAL ON THE PARENT]`

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

At depth two, nonzero fixed signatures exist: start with a finite principal-part divisor supported
away from its reflected orbit and add its `J`-image. Depth-two realization produces a constrained
meromorphic function, and reflection averaging produces a reflection-symmetric realization with
that nonzero signature. Thus FE symmetry alone permits hypertranscendental pair-face charge.

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
- [x] component reflection involution defined;
- [x] pair-face equivariance proved on paper;
- [x] fixed-submodule kernel and realization proved on paper;
- [ ] independent audit of the reflection action on the differential principal-part convention;
- [ ] independent audit of parent depth-two atomicity and all-depth completeness;
- [ ] formalization of meromorphic pair-face residues and the exact fixed-submodule theorem;
- [ ] scientific literature and priority audit.
