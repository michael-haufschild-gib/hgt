# Pointed variational data reconstruct finite nonlinear polynomial sources

- **ID:** `pointed-variational-polynomial-source-reconstruction`
- **Stage:** 3-formalized / not-new
- **Type:** BRIDGE THEOREM / FIRST NONABELIAN EFFECTIVITY MODEL
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [PARENT MATHEMATICS] [NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/MvPolynomialJacobianFDeriv.lean`
- **Statement:** A finite complex polynomial source map is determined by its full Jacobian field
  and one calibrated value.  The Jacobian alone is nonfaithful.  The polynomial Hénon map and a
  translation give a concrete nonlinear noncommuting source action to which the reconstruction
  applies.

## Exact no-go

For a polynomial family

```text
P:C^n -> C^m,
```

let `J_P(x)` be its Jacobian matrix.  The assignment `P |-> J_P` is not injective.  Already in one
variable,

```text
P(x)=x,                  Q(x)=x+1                         (1)
```

have identical Jacobian fields.

> **[NO-GO]** An unpointed variational realization cannot classify source morphisms.  Affine
> calibration is not recoverable from the Kähler differential, Fréchet cocycle, Cartan projection,
> or variational building.

## Positive reconstruction theorem

Fix one source point `x_0`.  Define the pointed variational fingerprint

```text
PV(P)=(x |-> J_P(x), P(x_0)).                             (2)
```

> **[THEOREM]** The map `PV` is injective on every finite complex polynomial family.

### Proof

If `PV(P)=PV(Q)`, the evaluation maps of `P` and `Q` have equal Fréchet derivatives everywhere and
agree at `x_0`.  The derivative-plus-one-value theorem on the connected vector space `C^n` gives
equality of the evaluation maps.  Polynomial function extensionality over the infinite field `C`
then gives `P=Q`. `QED`

This proves joint conservativity of two individually different realizations:

```text
variational realization: P |-> J_P,
affine realization:      P |-> P(x_0).                    (3)
```

The second component removes exactly the constant-translation kernel witnessed by `(1)`.

## Concrete nonlinear noncommuting model

On `C^2`, put

```text
H(x,y)=(y,y^2-x),                 H^(-1)(u,v)=(u^2-v,u),
T(x,y)=(x+1,y).                                           (4)
```

Thus `H` is a polynomial automorphism.  The maps do not commute: at the origin,

```text
(H composed T)(0,0)=(0,-1),
(T composed H)(0,0)=(1,0).                                (5)
```

If `x,y` are a free differential pair, prolongation of `(4)` gives a nonlinear nonabelian source
action on the rank-two free HT field `C<x,y>`.  The pointed variational fingerprint reconstructs
each finite polynomial source generator without inserting the unknown HT germ into the data.

This is the first explicit nonabelian model of the source-effectivity fibre, but it carries only
the source-morphism and calibration faces.  It does not yet supply analytic bornology,
polarization, integral ramification, or a distinguished spectral section.

## Boundary of the model

The theorem is finite-dimensional and polynomial.  It does not solve the infinite-jet HT problem.
At infinite depth, the missing conditions are:

1. compatibility of the pointed Fréchet cocycles under jet prolongation;
2. invariance under differential-birational source changes;
3. descent across source restrictions and correspondences;
4. critical bornological control of the resulting infinite tower;
5. coupling to polarization, integral realization, and the distinguished effective section.

The first four cannot be replaced by the affine building.  The building retains only relative
lattice position and Cartan growth, while `(1)` proves that source pointing is already invisible
before completion.

## Map-versus-correspondence constraint

The scalar rational tail theorem supplies a second exact boundary.  For one-sided
degree-expanding maps on a fixed projective line, every nonconstant persistent HT tail eventually
reduces to a finite-holonomy parabolic current; genuinely projective/nonabelian tail structure
collapses.  Two-sided correspondences can preserve minimal projective structure only by paying
topological capacity

```text
degree * hyperbolic excess <= 2 genus + puncture budget - 2.   (6)
```

The Hurwitz `(2,3,7)` phase and modular `(2,3,infinity)` phase attain the sharp bounds.

> **Positive consequence.** Finite-level nonlinear source actions may be reconstructed by `(2)`,
> but persistent nonabelian effectivity cannot in general live in a one-sided category of maps.
> The full HT source theory must admit calibrated correspondences and retain their topological
> capacity.

## Novelty and anti-theatre gate

The derivative-plus-one-value theorem, polynomial function extensionality, Hénon automorphisms,
and noncommuting polynomial maps are established mathematics.  The theorem on this card is a
formalized bridge and model, not new scientific knowledge.

The candidate-new residue is not `(2)`.  It is an essential-image theorem for compatible pointed
Fréchet towers over source correspondences, proving differential-birational invariance and
reconstructing a natural analytic HT germ from boundary data without storing that germ.  That
residue remains open.

- `[ANTI-THEATRE -- PASS]` The standard finite theorem is explicitly downgraded.
- `[POSITIVE VALUE]` The model proves why affine pointing is necessary and sufficient at finite
  polynomial level, and supplies a genuine noncommuting test action.
- `[FIELDS BOUNDARY]` The medal-scale theorem begins exactly where finite pointed reconstruction
  stops: infinite-jet descent, source correspondence effectivity, and joint analytic realization.

## Lean certificate

New declarations:

- `complexMvPolynomialFamily_eq_of_jacobian_eq_of_value_eq`;
- `pointedPolynomialSourceFingerprint`;
- `pointedPolynomialSourceFingerprint_injective`;
- `unpointedPolynomialSourceJacobian_not_injective`;
- `henonPlaneSource_bijective`;
- `henonPlaneSource_firstPlaneTranslation_noncommute`.

## Gates

- [x] unpointed Jacobian nonfaithfulness formalized
- [x] pointed variational reconstruction formalized
- [x] nonlinear polynomial automorphism formalized
- [x] explicit noncommutation formalized
- [x] every no-go paired with a positive theorem
- [x] standard parent status stated explicitly
- [ ] extend reconstruction to finite differential-rational substitutions
- [ ] define compatible pointed Fréchet towers over source correspondences
- [ ] prove differential-birational invariance
- [ ] reconstruct one natural analytic HT source from the tower
