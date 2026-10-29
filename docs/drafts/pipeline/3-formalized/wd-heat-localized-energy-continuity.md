# Continuity of actual localized vertical energy

- **ID:** wd-heat-localized-energy-continuity
- **Stage:** 3-formalized
- **Source:** [Localized heat energy](../1-in-progress/wd-heat-localized-energy-flux.md)
- **Lean:** `RHTower/HeatZeroSumContinuity.lean`
- **Declaration:** `RHTower.DeBruijn.continuousOn_heatLocalizedVerticalEnergy`

## Statement

For every continuous compactly supported real horizontal weight `w` and
every center `X`, the actual multiplicity-weighted sum

`E_X(t) = sum_z mult(H_t,z) w(Re z-X) (Im z)^2`

is continuous on `t >= 0`, including the right-hand limit at zero.
The sum is defined as a `tsum`; the proof explicitly identifies it with
finite zero sums. It assumes no summability, simplicity, separation,
or root-path regularity for the actual heat function.

## Proof

The heat-time Taylor bound proves locally uniform convergence of
`H_(max(s,0))` at every real parameter, including zero. Select an
enclosing circle whose boundary has no zero at the base time. The
critical-strip bound and compact horizontal support ensure that every
zero contributing to the weighted sum lies inside this circle.

Around each of the finitely many initial zeros, choose a small isolating
disk. The disks are disjoint, lie inside the enclosing circle, and have
arbitrarily small weight oscillation. Local uniform convergence preserves
the multiplicity count in each small disk and in the enclosing disk.
Their total counts agree, so the small disks exhaust all nearby zeros:
any remaining zero would have positive multiplicity and exceed the total.

If the initial total multiplicity is `N`, choose weight oscillation below
`epsilon/(N+1)`. Splitting the finite weighted sum over the small disks
bounds its change by `epsilon N/(N+1) < epsilon`. The clamped parameter
then gives continuity on the full nonnegative time interval.

## Verification and scope

Final plain check passed without errors or warnings:

`lake --old env lean GaloisForLFunctions/RHTower/HeatZeroSumContinuity.lean`

The module is wired into `RHTower.lean`; no umbrella compilation or new
olean generation was needed.

Together with local forward simplicity, this supplies continuity through
collisions. The actual derivative identity, the summed dissipation/flux
bound, its integration, and the WD arithmetic upper estimate remain open.
