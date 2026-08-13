# P-G155: Fixed-center exterior reflection energy

- **Stage:** `1-in-progress`
- **Route:** Hedenmalm critical features / prime--Gamma reflection projector
- **Status:** paper proof written; Lean verification pending

## Problem removed

The previous adjacent exterior carrier chose `round(height rho)` after exposing a divisor point.
That gives a valid zero-side quantum but is not a fixed prime--Gamma test.  A source estimate cannot
legitimately use that zero-dependent reporter choice.

## New construction

Fix a real center `t` before divisor expansion and use the two critical features centered at
`t,t+1`.  Give determinant rows contragredient prime clocks and covariant horizontal Cayley clocks.
The three-clock Cesaro projector keeps exactly `sigma=1-conj rho`.  At the Abel boundary, the
Cayley multiplier is the inverse transverse coordinate and changes sign under reflection.

The fixed adjacent Pluecker coordinate also changes sign and is purely imaginary.  Consequently
each surviving oriented projector term is exactly

```text
normSq[(Im z)^(-1) * adjacentDet(t,z)].
```

For a reflection-closed finite packet, the triple Cesaro determinant therefore converges to half
the sum of these positive norm squares.  Adding centers `t` and `t-1` gives the complete
two-orientation energy.  Every off-line divisor point with `|height-t|<=1/2` carries the existing
uniform quantum

```text
4 * (96/145)^2,
```

while an on-line point contributes zero exactly.

## Novelty and limitation

This is the first exact divisor-side composition in the corpus that simultaneously has fixed
feature centers, mixed prime/Cayley reflection dephasing, removable Cayley--Abel Green
normalization, positive reflected exterior squares, and the quantitative adjacent-feature
quantum.  It removes the zero-dependent reporter defect from the proposed four-leg producer.

It does not yet identify every clocked finite determinant with a pre-divisor arithmetic trace and
does not prove the arithmetic upper bound.  Remaining gate is a source identity plus an
infinite/dyadic version whose fixed-center determinant is bounded on the prime--Gamma side strongly
enough to charge at most one eighth of the local zero census.

## Lean

- `HedenmalmFixedCenterExteriorReflectionEnergy.lean`
- [ ] direct `lake env lean` check
- [ ] targeted leaf build
- [ ] standard-axiom audit
- [ ] umbrella import
