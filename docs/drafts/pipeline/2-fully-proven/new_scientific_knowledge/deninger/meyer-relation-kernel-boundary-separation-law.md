# Meyer--relation-kernel boundary separation law

- **ID:** `meyer-relation-kernel-boundary-separation-law`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL LAW / ROUTE CORRECTION / POSITIVE NO-GO SURVIVOR
- **Status:** `[PAPER PROOF CLOSED] [LEAN-PROVED] [NOT RH]`

## Question

Can completed Green provenance be compared to the Calderon--Witt relation-kernel character by
placing both inside the literal Meyer--Poisson boundary kernel and proving

```text
Trans(g_G(rho)) = D_rho tau_p?
```

## Shared coefficient space

At a prime `p`, let

```text
Q_p = C^2 / G_p,
P_p = affine-gauge rational-Witt Haar L2,
S_p = affine-gauge first-suspension Haar L2.
```

Here `G_p` is the reflected Meyer--Poisson Calderon graph.  The actual Calderon--Witt cross-effect
is a bilinear map

```text
B_p : Q_p x P_p -> S_p.
```

The Calderon--Witt cup and its relation-kernel transgression both take values in `S_p`.  For every
fixed affine packet `a in P_p`, the map

```text
T_{p,a}(u) = B_p([u],a),       u in C^2,
```

therefore gives a type-correct, source-native comparison from the literal Meyer collar to the
same coefficient space.  It does not choose an origin in the affine packet torsor.

## The universal law

Let `pi : R -> A` be a group quotient, let `c` be an `M`-valued normalized two-cocycle, and let
`b` be a primitive of `pi*c`.  For a scalar `z`, the cochain `z b` is a primitive of `pi*(z c)` and

```text
Trans_pi(z c; z b) = z Trans_pi(c; b).                 (1)
```

If `Trans_pi(c;b)` is nonzero and the scalar ring is a field, then

```text
Trans_pi(z c; z b) = 0  <->  z = 0.                    (2)
```

This is the **homogeneous relation-kernel faithfulness law**.  It constructs the coefficient
identity requested by the route: scaling the actual Calderon--Witt cup by the Green fracture
scales its relation-kernel character by exactly the same unsquared coefficient.

## Literal-boundary separation theorem

For every Meyer cap `f`, Poisson reflection gives

```text
[collar_p(f)] = 0 in Q_p.
```

Consequently

```text
T_{p,a}(collar_p(f)) = 0                                (3)
```

for every affine packet `a`.  Let `tau_p` be any nonzero value of the actual Calderon--Witt
relation-kernel character.  Combining `(1)`--`(3)` gives

```text
T_{p,a}(collar_p(f)) = D_rho tau_p  <->  D_rho = 0.     (4)
```

Thus no unconditional comparison can both:

1. factor the Green class as `D_rho tau_p` with `tau_p != 0`; and
2. place that class in the literal Meyer--Poisson boundary image,

unless it has already proved the critical-line assertion at `rho`.

## Why the existing source does not evade the theorem

The fixed reflected log-Gaussian is an honest nonzero Meyer middle-cohomology class.  Its zeroth
Xi evaluation is nonzero at every divisor support.  Every literal Meyer boundary has zero Xi jets.
Therefore the reflected Gaussian source is not in the literal Meyer boundary range.  The
prime--Gamma Cauchy representation is an analytic Cauchy boundary representation of that nonzero
class; it is not a Meyer--Poisson coboundary.

Likewise, the singular Poisson--Gaussian lift has a pole of order `m+1` at a Xi zero of
multiplicity `m`.  It is precisely outside the regular Meyer cap on which literal boundary
annihilation is proved.  Enlarging the source domain to admit this lift requires a new singular
relative complex; declaring it a boundary would merely restate the missing theorem.

## Route verdict

The proposed identity has two parts with different status.

- **Closed:** relation-kernel transgression is homogeneous, so the source-scaled cup has
  transgression exactly `D_rho tau_p`.
- **Impossible unconditionally in the current complex:** literal Meyer boundary membership of
  that class is equivalent to `D_rho=0` because `tau_p` is coefficient-faithful.

The relation-kernel route therefore does not supply an independent annihilator.  It faithfully
re-encodes the existing horizontal defect.  The correct next object, if this lane is continued,
is a singular relative/mapping-cone boundary law whose vanishing comes from arithmetic before
divisor specialization.  Its vanishing may not be defined as regular Meyer boundary membership.

## Strongest positive survivor

Exactifying covers and literal boundary quotients obey complementary laws:

```text
exactification lowers nonzero cohomology to a faithful relation character;
literal boundary passage kills only the zero cohomology class.
```

No coefficient-faithful natural comparison can identify the lowered nonzero character with a
literal boundary.  A valid comparison must live in relative cohomology and retain the boundary
anomaly rather than annihilate it.

## Gates

- [x] identify a choice-free shared coefficient target
- [x] prove transgression homogeneity on paper
- [x] prove literal Meyer boundary annihilation in the shared target on paper
- [x] prove simultaneous factorization-and-boundary condition is equivalent to scalar vanishing
- [x] separate Cauchy boundary from Meyer--Poisson coboundary
- [x] formalize exact laws in Lean
- [ ] construct an independent singular relative arithmetic vanishing law

## Formalization

Lean module:

```text
formal/GaloisForLFunctions/RHTower/DeningerMeyerRelationKernelBoundarySeparation.lean
```

Load-bearing declarations:

```text
DeningerNormalizedCocycle.kernelTransgression_csmul_apply
exists_deningerCalderonWitt_greenFracture_relationKernelTransgression
deningerMeyerCalderonWittGaugeBoundaryComparison_literalBoundary_zero
deningerMeyer_literalBoundary_eq_greenFracture_smul_iff
deningerMeyerReflectedLogGaussianSource_not_mem_literalBoundaryRange
```

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/DeningerMeyerRelationKernelBoundarySeparation.lean
lake build GaloisForLFunctions.RHTower.DeningerMeyerRelationKernelBoundarySeparation
../scripts/formal_tools.py lint
```

The theorem audit reports only Lean's standard logical foundations:
`propext`, `Classical.choice`, and `Quot.sound`.
