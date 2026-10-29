# Localized vertical energy through heat-zero collisions

- **ID:** wd-heat-localized-energy-flux
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [WD](../1-in-progress/wd-directed-source-extinction.md).
- **Statement:** Actual localized squared-height energy satisfies an integrated
  full-count dissipation inequality and an upper right-slope bound through
  arbitrary collisions, uniformly down to heat time zero.

The full statement, dependency-closed paper proof and Lean audit are on the
[localized evolution card](review-2910-w17-localized-heat-energy.md).
For a nonnegative unit-window cutoff w with w≤W, |w′|≤V and Lip(w′)≤M,

`E_w(b)−E_w(a)+2∫_a^b N_w ≤ (2M+2V+4W) C log X ∫_a^b E_outer`

for X≥X₀, 0≤a≤b≤1/8 and b log X≤1. N_w counts every nonreal zero with its
actual multiplicity and weight. The outer cutoff is one on the radius-two packet.
The upper right slope retains the full N_w at every admissible initial time.

The proof combines the [actual exterior field](wd-heat-exterior-force.md),
[gap-independent pair estimate](wd-heat-localized-pair-force.md),
[forward simplicity](wd-heat-forward-simple-clusters.md),
[weighted zero-sum continuity](wd-heat-localized-energy-continuity.md), actual
finite-branch differentiation, and comparison of continuous truncated counts.
Finite collision count and a uniform simplicity interval are unnecessary.

The capstones are
`RHTower.DeBruijn.exists_uniform_heatLocalizedVerticalEnergy_evolution` and
`RHTower.DeBruijn.exists_uniform_heatLocalizedVerticalEnergy_right_slope` in
`RHTower/Heat/HeatLocalizedEnergyDissipation.lean`.

This completes localized energy evolution. Uniform small-time nonreal counts
and the arithmetic absorption needed for WD extinction remain open.
