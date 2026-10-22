# Cyclic DA-gauge wall-attainment universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure identified the same positive Gamma Fourier modes in:

- `nonreal_sourceFace_arbitraryDifferentialAlgebraicGaugeBirth`, where every finite packet of
  positive unit-periodic modes is linearly independent and differentially algebraic; and
- `cyclicWall_gaugeAttainment_conservation`, where mode `n+1` is the normalized gauge of the
  shrinking cyclic period `1/(n+1)`, with diverging first jet and vanishing incidence symbol.

The corpus did not connect the arbitrary-rank DA source-face phase to the quantitative cyclic wall.

## Universal law

The complete cyclic wall escapes entirely inside the differentially algebraic sector:

1. every wall gauge `g_n(z)=exp(2πi(n+1)z)` is DA and fixed by its shrinking period
   `q_n=1/(n+1)`;
2. every finite initial packet of wall gauges is linearly independent, every linear combination is
   DA and unit-periodic, and no nonzero packet survives any deleted nonreal translation;
3. `q_n → 0`, the first-jet norm tends to infinity, and the incidence norm tends to zero; and
4. at every finite scale,
   `‖w(q_n)‖⁻¹ = 1 + ‖g_n'(0)‖/(2π)`.

Hence source-face rank, analytic jet escape, and loss of incidence observability can diverge
without producing a hypertranscendental gauge direction.

## Dependency-closed paper proof

1. By definition, `cyclicWallGauge n = gammaPeriodicMode (n+1)`.
2. Each mode is `z ↦ exp(c_n z)`, so the constant-coefficient ODE `y'-c_n y=0` proves it DA.
3. A finite packet of wall gauges is definitionally the positive Gamma Fourier packet. Existing
   source-face DA inertia gives linear independence, DA closure of every packet, unit periodicity,
   and failure of every nonzero packet to remain periodic under a nonreal translation.
4. Existing cyclic-wall theorems give period invariance, exact gauge/attainment conservation,
   shrinking periods, divergent first jets, and vanishing incidence weights.
5. Combining steps 2–4 places the full wall-crossing sequence and every finite face slice in the DA
   phase while retaining the exact quantitative escape law.

No numerical computation, compactness assumption, Gamma-value evaluation, or asymptotic
approximation enters.

## Formal targets

- `cyclicWallGaugePacket`
- `cyclicWallGaugePacket_eq_gammaPositivePeriodicFourierPacket`
- `differentiallyAlgebraic_cyclicWallGauge`
- `nonreal_cyclicWall_arbitraryDifferentialAlgebraicGaugeBirth`
- `cyclicWall_differentialAlgebraicAttainmentUniversality`

## Novelty audit

Post-proof searches found separate literature on arithmetic and closure properties of
differentially algebraic functions, exponential-polynomial Fourier modes, periodic solution
spaces, and shift-operator decompositions. They did not reveal the exact synthesis of
arbitrary-rank DA source-face inertia with a shrinking-period wall whose first jets diverge,
incidence symbols vanish, and inverse incidence obeys the displayed finite-scale conservation law.

The exact wall law remains **[NOVELTY UNVERIFIED]**:

- https://arxiv.org/abs/2305.00702
- https://arxiv.org/abs/2304.02517
- https://doi.org/10.1007/978-1-4613-8445-8_3

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/HTGeometry/CyclicDAGaugeWallAttainmentUniversalityLaw.lean`

with declarations:

- `cyclicWallGaugePacket`
- `cyclicWallGaugePacket_eq_gammaPositivePeriodicFourierPacket`
- `differentiallyAlgebraic_cyclicWallGauge`
- `nonreal_cyclicWall_arbitraryDifferentialAlgebraicGaugeBirth`
- `cyclicWall_differentialAlgebraicAttainmentUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/HTGeometry/CyclicDAGaugeWallAttainmentUniversalityLaw.lean`

Wired into `GaloisForLFunctions/HTGeometry.lean` beside the source-face DA-inertia law.
