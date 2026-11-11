# Every prescribed sublogarithmic radius misses the minimal face

- **ID:** A89
- **Stage:** 1-in-progress
- **Type:** CANDIDATE

## Statement

For every `γmin,C>0`, `0<Θ≤1/2`, and nonnegative radius `R(T)=o(log T)`,
there is one simple configuration `Z∈InClassZ γmin C` whose top real part
is `1/2+Θ` and is unattained. For every floor `K` and lower bound `U`,
some centre `T≥U` satisfies

`2 Re lagStructure Z (boxSpline 1 3) u ≥ K` whenever `|u−T|≤R(T)`.

Thus a prescribed sublogarithmic observation radius does not detect the
minimal face, even with tempering, reflection symmetry and logarithmic local counts.

## Proof

At `Γ=T^(1/4)`, use `k=ceil(2048Γ(R(T)+8))` equally spaced imaginary
reference nodes. Solve `exp(Tz_j)=∏_{l≠j}(−z_l)/(z_j−z_l)` by contraction.
Lagrange interpolation and its factorial remainder give
`Re Σ exp((T+v)z_j)≥3/4` throughout the enlarged window.
The normalized node count satisfies `k/Γ²→0` and `k/(Γ log Γ)→0`.

Convolution with the nonnegative unit-mass kernel `upow 1 7` transfers
positivity to the squared transform of `boxSpline 1 3`. Reflect positive
depths across zero. Choose successive separated frequency blocks in depth
bands increasing to `Θ`; their small coefficient masses give tempering
and summable future tails. Each block dominates its predecessors on its
prescribed window. The exact configuration trace is the sum of these blocks.

## Lean status

The calibration, interpolation, grid geometry and asymptotic density bounds
passed Lean. The complete spline and configuration proof is drafted in
`SurfaceOfSpecZ/ScaleLocality/EveryPrescribedSublogarithmicRadiusMissesTheMinimalFace.lean`;
its final check remains.

Declaration:
`SurfaceOfSpecZ.ScaleLocality.exists_classZ_prescribed_sublogarithmic_windows_bddBelow_beyond_every_bound`.

Construction details: [self-consistent interpolation weights](self-calibrated-exponential-window-blocks.md).
