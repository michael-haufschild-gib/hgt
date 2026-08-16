# Countable Window Basis for `D_2`

- **ID:** d2-countable-window-basis
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/revision01/proof-route.md`
- **Statement:** For a discrete zero divisor, `D_2(R)=0` for every admissible window is equivalent to `D_2(R)=0` on a countable basis of rational rectangles whose boundaries avoid zeros.

## Goal
Reduce the all-window `D_2` wall to a countable local detection problem. This does not prove RH; it removes an avoidable quantifier burden from the local-source formulation.

## Proof
Let the zero divisor be discrete and define the positive atomic off-seam-width measure

```text
nu = sum_rho m_rho (Re rho - 1/2)^2 delta_rho.
```

Then `D_2(R)=nu(R)`.

If `nu(R)=0` for every admissible window, then it is zero on every rational rectangle whose boundary avoids the divisor.

Conversely, assume `nu` is zero on every such rational rectangle. If an off-seam zero `rho_0` existed, then

```text
m_{rho_0} (Re rho_0 - 1/2)^2 > 0.
```

Since the divisor is discrete, choose a small open rectangle around `rho_0` containing no other zeros and with rational sides avoiding `rho_0`. Its boundary avoids the divisor after shrinking if necessary. On that rectangle, `D_2` is exactly the positive atomic mass of `rho_0`, contradiction.

Therefore no off-seam zero exists, and `D_2(R)=0` for every admissible window.

## Boundary Note
Open/closed boundary conventions matter only when a zero lies on the boundary. Discreteness lets one shrink to a rational isolating rectangle with boundary disjoint from the divisor.

## Computation
Artifacts:

- `computations/2026-06-21-penrose-proof-r03-d2-countable-window-basis.py`
- `computations/2026-06-21-penrose-proof-r03-d2-countable-window-basis.txt`

## Log
- 2026-06-21 -- Penrose: created from proof-route node 8 and NODE "critical behavior depends on network topology". This is a quantifier reduction for all-window `D_2`, not a proof of `D_2=0`.

## Gates
- [x] 0 -> 1 in-progress: quantifier reduction isolated.
- [x] 1 -> 2 fully-proven: discreteness/isolating-rectangle proof written.
- [x] 2 -> 3 formalized: `RHTower/CountableWindowBasis.lean`.

## 2026-08-16 Lean closure

`RHTower/CountableWindowBasis.lean` proves the card unconditionally.

`ratRectangle a b c d` is the open window with rational corners, and `offSeamMass m F` is
`D_2` over a finite family of divisor atoms, with `offSeamMass_eq_zero_iff` reducing vanishing of
the mass to vanishing of every atom (the sum has nonnegative terms).

- `exists_ratRectangle_subset_ball`: every point has arbitrarily small rational windows around it.
- `exists_isolating_ratRectangle`: around every point of a discrete set there is a rational window
  whose closure meets the set only in that point, so its boundary avoids the divisor.  This is the
  card's "shrink to a rational isolating rectangle with boundary disjoint from the divisor".
- `offSeam_vanishes_iff_ratRectangles`: the equivalence of the card — off-seam width vanishing on
  every window is equivalent to vanishing on the countable rational-window family whose boundary
  avoids the divisor.
- `re_eq_half_of_ratRectangles`: with strictly positive multiplicities the rational-window
  condition puts every divisor point on the critical line, which is the card's contradiction
  argument in positive form.

Discreteness is rendered exactly as the card uses it: every divisor point has a ball meeting the
divisor only in itself.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
