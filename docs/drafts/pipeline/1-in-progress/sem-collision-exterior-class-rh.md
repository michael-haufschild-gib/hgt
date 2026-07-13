# SEM collision exterior class to RH

- **ID:** `sem-collision-exterior-class-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Source audit:** `CarrierCountConstraint.lean`, `FiniteMemberSteering.lean`
- **Consumers:** `XiHeightAdaptiveLinearQuadraticCensusCollision.lean`,
  `RHLadderHedenmalmSimplicityCollision.lean`

## Exact collision quantity

For a finite zero window with multiplicities `m_i`, the fine labelled diagonal contraction is

```text
M = sum_i m_i,
```

while the coarse quadratic contraction is

```text
Q = sum_i m_i^2.
```

Their difference is the ordered collision-pair count

```text
Q-M = sum_i m_i(m_i-1) = 2 sum_i choose(m_i,2).
```

It vanishes exactly when every zero in the window is simple.  This identity is already formalized
for Xi boxes by `boxSquareOrderSum_eq_order_add_excess` and
`boxSquareOrderSum_eq_boxOrderSum_iff_all_simple`.

The natural source object is therefore not another scalar winding number.  It is a label-stable
second exterior or discriminant class whose local rank is `choose(m,2)`.  A source annihilation
theorem for this class would prove simplicity; an independent first ladder rung would force every
hypothetical right-half order to be even, and the two constraints would prove RH.

## Proved no-go: ordinary SEM domination forgets collisions

`xi_dominating_configuration_iff` proves that every hole-confined list satisfying the smallness
margin occurs as the zero list of some member dominating Xi if and only if its length is the central
Xi order.  Its indexed form is sharper:

```text
an indexed configuration dominates
  <-> sum_i multiplicity_i = central Xi order.
```

The positions, partition into labels, repeated centers, and collision pattern are otherwise free.
Hence annulus domination determines `M` and cannot determine `Q-M`.  No argument using only the
existing domination relation can prove simplicity or identify a fine/coarse quadratic comparison.

`sem_hole_zeros_localize` does not repair this: uniform compact convergence forces all finite-member
zeros into a shrinking hole but supplies no derivative floor or pair-separation margin.  Simple
approximant zeros may merge into an allowed multiple limiting zero.

## Positive successor

The missing datum must refine the count constraint before scalarization.  Equivalent candidate
forms are:

1. a source-defined `Lambda^2` class of the SEM hole projection or local divisor complex;
2. the nilpotent/cotangent part of `C[X]/(X^m)`, whose nontriviality records `m>1`;
3. a discriminant line with a source-derived nonvanishing trivialization;
4. a label-stable collision measure surviving the SEM limit with a quantitative separation floor.

The class must be constructed from the completed Euler--Gamma object before enumerating Xi zeros.
Applying an exterior power after the target multiplicities are known merely repackages the
quadratic census.

## Two-ended chain

```text
completed Euler--Gamma / SEM source
  -> finite-window labelled local complex, compatible under refinement
       [OPEN CORE A: source labels]
  -> second exterior collision class C_window
  -> local trace(C_window) = sum_i choose(m_i,2)
       [OPEN CORE B: source-to-divisor comparison]
  -> source reducedness, discriminant, or contracting homotopy annihilates C_window
       [OPEN CORE C: annihilation]
  -> every right-half finite window is simple
  + independently sourced RHLadder 1
  -> no right-half Xi zero
  -> RH.
```

The retired prime-Frobenius ramification route is not a provider: the actual Euler/Adams operation
dilates rather than contracts the cotangent filtration.  Its positive successor could provide Open
Core C only after an additional source theorem: pure-weight Adams localization or a relative
Lefschetz comparison forces the positive cotangent weights, hence the collision class, to vanish.

## Kill conditions

Retire a proposed realization if its class depends only on total winding, if its labels are obtained
by enumerating the Xi divisor, if uniform convergence is used without a derivative/separation
floor, if the exterior class is merely `choose(m,2)` defined from the target order, or if the
annihilation hypothesis is equivalent to global Xi simplicity.

## Status

- `[PROVED]` quadratic minus linear census equals collision-pair excess;
- `[PROVED]` vanishing excess is equivalent to simplicity in every finite Xi box;
- `[PROVED NO-GO]` existing SEM domination is exactly total-count data and is collision-partition
  blind;
- `[PROVED NO-GO]` compact uniform convergence/localization alone does not preserve simplicity;
- `[POSITIVE TARGET]` construct a source-defined second-exterior/discriminant class beyond the
  domination relation;
- `[OPEN]` source comparison and annihilation;
- `[OPEN]` independent first ladder rung.
