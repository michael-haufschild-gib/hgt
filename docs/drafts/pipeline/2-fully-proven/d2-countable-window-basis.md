# Countable Window Basis for `D_2`

- **ID:** d2-countable-window-basis
- **Stage:** 2-fully-proven
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
