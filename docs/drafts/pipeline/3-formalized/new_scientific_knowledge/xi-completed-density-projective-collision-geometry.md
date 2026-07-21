# Xi completed-density projective collision geometry

- **ID:** `xi-completed-density-projective-collision-geometry`
- **Stage:** 3-formalized
- **Type:** `[NEW SCIENTIFIC KNOWLEDGE] [UNCONDITIONAL] [SOURCE-PROJECTIVE] [NO RH CLAIM]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityProjectiveCollision.lean`
- **Parent:**
  `../../5-failed/xi-completed-density-antipodal-crossing-barrier.md`

## Theorem package

For completed-density channels `E,E#` and `R=E#/E`, define

```text
W_E=(E#)'E-E#E',
V_E=E^2 conjugate(W_E).
```

Formalization proves unconditionally:

```text
E'+(E#)'=8z XiC+4z^2 XiC',                           (1)
W_E=8z XiC E+4z^2(XiC' E-XiC E'),                    (2)
R'=W_E/E^2,                                           (3)
dR(V_E)=|W_E|^2,                                      (4)
R=-1 iff XiC=0                                        (5)
```

on stated regular charts.  At any Xi zero,

```text
W_E=4z^2 XiC' E.                                      (6)
```

The earlier full-density connection `C_F` obeys an exact seam mismatch:

```text
W_E-q C_F=-z^2 XiC'.                                  (7)
```

Thus connections are unequal at every noncentral simple collision.

On positive real boundary, source sine positivity gives `Im E(t)>0`.  At a real Xi zero,
`Re E(t)=0`, hence `E(t)=i Im E(t)` and `R(t)=-1`.  Formal quotient differentiation gives

```text
d/dy R(t+iy)|_(y=0)
  =4t^2 Re(XiC'(t))/Im(E(t)).                         (8)
```

At every simple real zero this velocity and `W_E(t)` are nonzero.

## New content

Equation `(4)` turns every regular negative-real level component into an oriented trajectory with
strict projective coordinate `R`; no-return on one regular component is therefore automatic.
Equation `(7)` proves earlier full-density Wronskian cannot certify that trajectory.  Subsequent
transverse Pick work proves `E` is upper-zero-free and supersedes the heteroclinic classification:
interior collisions conserve zero multiplicity, so current frontier is affine-pencil top-edge
entry rather than global trajectory regularity.

## Scope

No theorem excludes an off-axis Xi zero.  No global gap, zero-location hypothesis, divisor
enumeration, estimate, or computation occurs.  Novelty claim concerns exact completed-density
projective connection, connection-seam mismatch, and theta-source boundary entry law.

## Verification

- scratch API/proof audit:
  `lake env lean /tmp/hgt_projective_collision_scratch.lean`;
- direct module check:
  `lake env lean GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityProjectiveCollision.lean`;
- targeted build:
  `lake build GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityProjectiveCollision`;
- temporary `#print axioms` audit of ten capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`;
- `scripts/formal_tools.py lint` passed.
