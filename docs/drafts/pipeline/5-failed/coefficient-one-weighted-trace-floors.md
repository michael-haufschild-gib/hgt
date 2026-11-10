# Weighted trace floors require coefficient two

- **ID:** A92-weighted-coefficient-one
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement refuted:** A floor `F≥−K` implies `∫w|F|≤K∫w+Σ_j|a_j||ŵ(γ_j)|` for every nonnegative integrable weight.

## Obstruction

`F(t)=cos t+cos(2t)` has floor `−9/8`. Equal normalized interval densities near `0,2π/3,4π/3` have total mass `3`, Fourier samples at `1,2` tending to zero, and absolute trace integral tending to `4>27/8`. The strict failure holds for sufficiently short intervals.

## Sharp positive survivor

The optimal universal coefficient is **2**:
`∫w|F|≤2K∫w+Σ_j|a_j||ŵ(γ_j)|`.
Indeed `|F|≤F+2K`, and the weighted signed mean is the Fourier pairing. Optimality uses `Fejer_N−1`, with floor `−1` and positive active frequencies. At the `(N+1)`-st roots its values are `N,−1,…,−1`; all active Fourier samples vanish. Normalized interval densities approximate these samples, giving absolute-mass ratios arbitrarily close to `2N/(N+1)`, hence to `2`.

## Formalization

All modules lie in `SurfaceOfSpecZ/ScaleLocality`, namespace `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`:

- `WeightedFloorCoefficientOneFails.lean`: `exists_weight_violating_floor_coefficient_one`.
- `WeightedTraceFloors.lean`: `weighted_finiteExpSum_abs_le`.
- `FejerFloorsMakeCoefficientTwoSharp.lean`: `exists_weight_violating_any_floor_coefficient_lt_two`.

Each passed direct `lake --old env lean` and transitive axiom audits; only `propext`, `Classical.choice`, `Quot.sound`. All are imported by `SurfaceOfSpecZ.lean`.

The obstruction fixes the exact floor cost in the prime-side resolution assembly; the signed Fourier mean cannot pay the negative part twice with coefficient one.
