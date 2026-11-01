# Harmonic saturation selects the trivial gauge

- **ID:** harmonic-saturation-selects-the-trivial-gauge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0111 Γ12.
- **Statement:** A unitary prime gauge satisfies `S_N/H_N → 1` exactly when every prime phase is one.

## Proof

Write `χ` for the completely multiplicative lift, `d(n)=1−Re χ(n)`,
`D_N=Σ_{1≤n≤N}d(n)/n`, and `H_N=Σ_{1≤n≤N}1/n`.
Unit modulus gives `d(n)≥0`. For each positive integer `p`,

`1−Re χ(p) ≤ 2(d(n)+d(pn))`.

Indeed, apply the squared triangle inequality to
`χ(pn)−χ(n)=(χ(p)−1)χ(n)`. Summation and dilation give

`(1−Re χ(p))H_N ≤ 2(1+p)D_(pN)`.

Since `H_(pN)≤pH_N`, saturation `D_N/H_N→0` forces
`Re χ(p)=1`, hence `χ(p)=1`. The converse is immediate.
This resolves the harmonic-saturation face; the `κ=0` conductor-series
classification is a separate remaining face of Γ12.

## Dependencies and scope

The corpus provides the prime-gauge carrier, complete multiplicativity,
and unit modulus in `PrimeGaugeTorusAndVacuumIntertwiners`.
No prime-density, zero-location, or analytic continuation input.

## Lean

`BiarithmeticGaugeGeometry/HarmonicSaturationSelectsTheTrivialGauge.lean`,
namespace `GaloisForLFunctions.BiarithmeticGaugeGeometry.PrimeGauge`:

- `harmonic_dilation_deficit_ratio` gives
  `1−Re χ(p) ≤ 2p(1+p)D_(pN)/H_(pN)` for `p,N≥1`.
- `harmonicAverage_tendsto_one_iff` gives the exact classification.

Direct `lake --old env lean` check passed. Both declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
