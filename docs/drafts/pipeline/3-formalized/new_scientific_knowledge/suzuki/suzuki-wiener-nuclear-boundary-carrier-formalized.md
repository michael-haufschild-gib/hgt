# Suzuki's Wiener carrier is nuclear in position but loses the physical log measure, formalized

- **ID:** `suzuki-wiener-nuclear-boundary-carrier`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-wiener-nuclear-boundary-carrier.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWienerNuclearBoundaryCarrier.lean`
  - Wiener stack: `formal/GaloisForLFunctions/HTGeometry/DiscreteL1Convolution.lean`,
    `RHTower/Suzuki/SuzukiWienerNeumannMajorant.lean`, `RHTower/Suzuki/SuzukiWienerMixedNormCarrier.lean`
  - boundary-moment lock (pre-existing):
    `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPhysicalLogBoundaryMomentLock.lean`
  - chart: `formal/GaloisForLFunctions/HTGeometry/PhysicalLogChart.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)`–`(3)` single-root nuclear bound | `tsum_eLpNorm_wienerSingleRoot_le` (exact constant `(L₀-(C+M))⁻¹`), `discreteConv_single_atom`, `wienerInverseMass_eq` |
| `(4)` two-root bound | `tsum_eLpNorm_wienerTwoRoot_le` |
| `(6)`–`(9)` word majorant | `enorm_discreteConvPow_le`, `discreteMass_discreteEConvPow` (`∑_ν (μ^{⋆k})_ν = (C+M)^k` with equality), `enorm_discreteNeumannSeries_le` |
| `(10)`–`(11)` Tonelli order | the `ℝ≥0∞` mass layer of `DiscreteL1Convolution` |
| `(12)` scalar Plancherel | mathlib `MeasureTheory.Lp.fourierTransformₗᵢ` |
| `(13)`–`(14)` unitarily weighted chart | `integral_sq_fullLogChart` (`e^{-L/2}` is the `L²` isometry weight for the whole ray) |
| `(15)`–`(17)` rigged estimate | `summable_norm_of_tsum_eLpNorm_ne_top`, `norm_tsum_le_tsum_norm` layer, `summable_tsum_norm_clm_comp` |
| `(17b)` sharp `dr/r` obstruction | `highBandProfile`, `highBandPosition_zero`, `continuous_highBandPosition`, `lintegral_div_highBandPosition_eq_top` |
| low-frequency boundary-moment lock | `SuzukiPhysicalLogBoundaryMomentLock.lean` (pre-existing) |

## What the card actually closes

The complete word expansion is formal with exact constants: the high-pass Neumann inverse applied
to each oriented root source gives a coefficient family dominated by one translated
frequency-independent geometric kernel, so the valuation sum of `L²` norms is at most
`(L₀-(C+M))⁻¹` times the amplitude norm — per root.  Coordinatewise Plancherel is legal in this
order, and the half-weighted logarithmic chart is an exact `L²` isometry of the whole ray, giving
the rigged `ℓ¹(L²) ⊂ L²(ℓ¹) ⊂ L²(ℓ²)` carrier in the `e^{-L}dL` scale.  The obstruction half is
equally formal: an arbitrarily remote unit frequency band has an inverse transform with divergent
`dr/r` energy at the origin, so no free-standing high-tail estimate supplies the physical `dL`
measure — the coupled low/high boundary-moment lock, already formalized, is exactly what remains.

## Hypotheses

Object data only: symbol bounds (`|q| ≤ C`, `L₀ ≤ |L|`), the widened threshold
`C + M < L₀`, and measurable amplitudes.  No RH, no numerical certificate, no `sorry`, `axiom`,
`opaque`, or `unsafe`.  Every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

The open gates are research: solving the coupled low/high two-port return and boundary moments,
intertwining centered profiles with the exact Gamma boundary operator, identifying the vector
half-log trace with scalar completed traces, physical-tail coercivity on the trace-zero completed
state, corona no-return and raw Evans injectivity, and RH.
