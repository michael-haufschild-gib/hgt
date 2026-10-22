# Quadratic reflection anomaly to RH

- **ID:** `quadratic-reflection-anomaly-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Consumer:** `../../../3-formalized/not_new_scientific_knowledge/quadratic-circle-free-orbit-charge.md`
- **Local source square:** `../../../3-formalized/not_new_scientific_knowledge/completed-flux-incidence-square.md`
- **Integral source square:** `../../../3-formalized/not_new_scientific_knowledge/integral-jet-quadratic-incidence.md`
- **Linear predecessor:** `irrational-circle-sem-holonomy-collapse.md`

## Claim

Construct from the completed Euler--Gamma constraint an equivariant quadratic refinement of the
prime-log circle character.  Its finite-window localization must satisfy:

```text
fixed critical-line orbit of multiplicity m  ->  0,
free reflected orbit of multiplicity m       ->  [2m^2 log p] in R/Z.  (1)
```

The completed source should force the total equivariant anomaly to vanish.  Since the total free
contribution is

```text
[2 sum_(free orbits i) m_i^2 log p],                       (2)
```

and `log p` has infinite order modulo `Z`, `(2)=0` implies that every free-orbit multiplicity is
zero.  All Xi zeros are then fixed by critical-line reflection, which is RH.

The local symmetric incidence object is no longer hypothetical.  The completed flux square is an
analytic reflection-invariant germ with center value `m^2` and an exact prime--prime / prime--Gamma /
Gamma--Gamma decomposition.  The unresolved construction begins at equivariant fixed-point
subtraction and finite-window assembly.

The actual completed-SEM contour boundary now also carries a canonical integral quadratic index:
constant-coefficient evaluation on the integral divisor-jet quotient, followed by squaring.  It is
proved equal to the squared contour winding, split count, and Xi order.  Thus neither the integral
lattice nor the local source-to-square transgression is missing.  The first unresolved operation is
the nonlocal equivariant subtraction that kills fixed orbits without reading their location from
the target divisor.

## Two-ended chain

```text
completed Euler--Gamma / FE--Schwarz constraint
  -> symmetric arithmetic incidence pairing in an unbounded-exponent circle class
  -> canonical quadratic refinement q_p of the signed local order character
       [OPEN CORE A: source-defined quadratic class]
  -> equivariant fixed-point localization
       fixed orbit contribution = 0
       free pair contribution = [2m^2 log p]
       [OPEN CORE B: localization formula]
  -> excisive finite-window sum with no cross-orbit terms
       [OPEN CORE C: orthogonal additivity]
  -> completed source trivializes the global quadratic anomaly
       [OPEN CORE D: source annihilation]
  -> [2 sum m_i^2 log p] = 0
  -> every free-orbit multiplicity m_i = 0
       [PROVED LEAN: freeOrbitQuadraticCircleCharge_eq_zero_iff]
  -> every Xi zero is fixed by line reflection
  -> RH.
```

Unlike the linear circle route, this route does not need to discard the reflected half.  It tries
to make reflection pairing positive through a quadratic refinement and to remove only genuine fixed
points by equivariant localization.

## Candidate mathematical homes

The required object could appear as one of the following, but the route is not committed to a
vocabulary before the identities are proved:

- a quadratic refinement of a new symmetric incidence form on a determinant gerbe;
- an eta/Chern--Simons phase whose polarization is the linear prime-log character;
- an equivariant Pfaffian line with a fixed-point correction;
- a secondary index pairing on the FE--Schwarz action groupoid.

The defining constraint is `(1)`, not the name of the carrier.

## Firewalls

### Arbitrary squaring is not a source construction

The formal consumer squares a known integer multiplicity.  That alone is target-side.  The source
must produce a canonical quadratic refinement before the unknown divisor is expanded and prove that
its local index is the square in `(1)`.

### Fixed-point correction cannot encode the answer

The fixed locus `Re(s)=1/2` is known geometrically, so an equivariant localization correction may
depend on stabilizer type.  It may not be defined by first asking which Xi zeros are on that locus.
It must arise functorially from the FE--Schwarz action on the source object.

`FESchwarzGermGluingTrivialization.lean` sharpens this firewall: every germ-local scalar detector
invariant under the natural basis gauges factors through the Boolean fixed/free orbit shape.  A
local scalar rule that subtracts the fixed `m^2` term and keeps the free one would therefore be the
orbit classification itself.  The correction must be nonlocal and arithmetic—built from the
all-place incidence/window system with a source-derived reduction of gauge—not from scalar germ
gluing.

### Cross terms are dangerous

A quadratic function satisfies

```text
q(x+y)-q(x)-q(y)=b(x,y).
```

A global quadratic determinant can therefore contain cross-orbit terms `2m_i m_j`.  These can have
signs and cancellations, destroying the positive sum of squares.  Excision, block orthogonality, or
a localization theorem must prove that the relevant global anomaly is the direct sum of local
quadratic terms, not the square of the total order.

### Linear completed-ratio closure proves nothing

The ordinary FE-paired linear phase cancels for every multiplicity.  The source trivialization must
act on the genuinely quadratic secondary class; reusing the scalar identity
`Lambda(s)/Lambda(1-s)=1` without the quadratic localization only recovers `m-m=0`.

### The existing Arf seam is already dead

`SeamArfCollapse.lean` proves that the reflection-equivariant `ZMod 2` Arf density satisfies
`x^2=x` and therefore collapses pointwise to the linear deck parity.  It also records that the
two-lane reflection matching carries no `ZMod 4` symplectic lift.  The present circle-valued square
cannot be installed on that same seam by relabeling it.

The required enlargement is structural: an unbounded-exponent coefficient circle plus an
arithmetic incidence/polarization whose quadratic refinement has polarization

```text
b(m,n) = [2mn log p].
```

It must use completed Euler--Gamma data beyond the FE--Schwarz matching.  A functional-equation-only
quadratic invariant is excluded by the same soft counterexamples that kill the Arf route.

There is also a general algebraic firewall.  Polarization of a quadratic function on an abelian
group is symmetric, whereas the weld commutator pairing is alternating.  The formal theorem
`no_primeCircle_antisymmetric_quadraticPolarization` proves that a non-two-torsion prime-log phase
cannot be both.  Thus the new symmetric incidence form cannot be the old weld `H^2` cocycle under a
change of vocabulary.

### Infinite divisor requires finite-window coherence

The formal sum-of-squares theorem is finite.  The source anomaly must be defined first on compact
windows, be invariant under admissible boundary changes, and be compatible under window inclusion.
No divergent global sum is permitted.

### No de Bruijn or Maslov flow substitution

The backlog already contains a spectral-flow/Maslov encoding of the off-line inertia.  That object
uses a deformation family and its identification with the off-line count is itself the RH-bearing
endpoint.  Replacing the static quadratic anomaly by de Bruijn flow, PT spectral flow, or a
divisor-fed Maslov index would leave the constraint register and merely rename the target count.
The required class is a static source constraint on the FE--Schwarz action groupoid.

## First falsifiable subclaims

1. `[CONJECTURE]` The completed weld/determinant data admits a canonical `R/Z`-valued quadratic
   transgression of the proved completed-flux incidence square to the one-prime circle character.
2. `[CONJECTURE]` Equivariant localization assigns zero to a fixed reflection germ and
   `[2m^2 log p]` to a free multiplicity-`m` pair.
3. `[PROVED FINITE BRIDGE]` Once the source supplies finite component labels, the marked-support
   incidence character eliminates every cross-component term and retains the sum of local squares.
4. `[CONJECTURE]` The finite-window quadratic class is computed from the prime--Gamma source without
   selecting the Xi zeros.
5. `[CONJECTURE]` The completed source constraint trivializes this class on every window.

Failure of 1 kills the route.  Failure of 2 makes it position-blind.  Using target-selected labels
in 3 would make the diagonalization circular.  Failure of 4 makes it a target encoding.  Failure of
5 leaves a faithful detector with no proof.

The finite combinatorial part of item 3 is now discharged without assuming geometric
orthogonality.  `MarkedSupportQuadraticDiagonalization.lean` applies the marked Koszul character to
the support of each ordered orbit-label pair and proves

```text
sum_(i,j) m_i m_j chi({i,j}) = sum_i m_i^2.
```

Thus every mixed-orbit term is deleted and every local square survives with coefficient one.  The
remaining source clause is narrower: construct the component-labelled incidence decomposition
functorially from the finite-window FE--Schwarz action groupoid before expanding the Xi divisor.
Applying the selector only after target-side orbit enumeration is forbidden.

There is also a strictly weaker finite-ring successor.  At each integer height, compare the marked
quadratic census `sum m_i^2` with the linear SEM contour census `sum m_i` modulo one power of two
larger than the squared unconditional zero-count envelope.  This forces all enclosed right-half
zeros to be simple.  Combined with an independently sourced `RHLadder 1`, which forces their
multiplicities to be even, it proves RH.  The implication is formalized in
`XiHeightAdaptiveLinearQuadraticCensusCollision.lean`; the source comparison and first rung remain
separate open cores.

## Status

- `[PROVED]` linear reflection-pair circle phase cancels automatically;
- `[PROVED]` quadratic reflection-pair phase is zero exactly at zero multiplicity;
- `[PROVED]` finite free-orbit phase closure forces every multiplicity to vanish;
- `[PROVED]` the local completed source square reads `m^2` and splits into exact all-place incidence
  terms;
- `[PROVED]` the integral completed-SEM divisor-jet boundary has canonical quadratic index equal to
  the squared winding, split count, and Xi order;
- `[PROVED]` marked-support incidence diagonalizes every finite labelled quadratic sum, eliminating
  all cross-orbit terms without a geometric orthogonality assumption;
- `[OPEN]` prime-log circle transgression of the integral source square;
- `[OPEN]` source-defined component labels and fixed/free equivariant localization;
- `[OPEN]` source-only finite-window trivialization.
- `[CLOSED SHORTCUT]` the existing `ZMod 2` Arf/two-lane seam collapses to linear parity.
- `[CLOSED SHORTCUT]` scalar germ-local fixed-point subtraction factors through orbit shape.
