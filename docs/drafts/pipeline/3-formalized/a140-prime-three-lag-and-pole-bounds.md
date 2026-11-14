# Retained Gamma and pole bounds near the prime-three boundary

- **ID:** A140-prime-three-comparison
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/a140-certificates-through-the-prime-five-boundary.md`.
- **Statement:** Explicit Gamma mass, quartic lag, and cosh-pole bounds hold
  through aperture `11/20`. These are comparison estimates, not a positive
  Weil floor at the prime-three boundary.

## Statements

Write `A(t)=∫F(x)F(x+t)dx`, `M=∫F²`, and suppose `a>0` and
`F : ℝ→ℝ` is `C²`, supported on `[-a,a]`.

1. At diameter `log 3`, the Gamma tail is
   `Ω(log 3)=log(2+√3)/2+π/6`; the normalized Gamma mass coefficient is
   at least `−4546/2500`.
2. The fourth correlation moment is at most `17a⁵M/10`, or `a⁵M/10` for
   odd sources. Consequently the quartic lag deficit is at least `47a⁵M/10`,
   or `63a⁵M/10` for odd sources.
3. If `2a≤11/10`, the retained Gamma remainder is at least
   `5a⁴M/2304 + (1/176)∫₀²ᵃ t⁴(A(0)−A(t))dt`.
   Its uniform floor is therefore `(5a⁴/2304+47a⁵/1760)M`, with `63`
   replacing `47` for odd sources.
4. For continuous `G : ℝ→ℝ`, put
   `m_j=∫₀¹G P_j`, `M_G=∫₀¹G²`, and
   `B=(1+a²/24+a⁴/1920)m₀+(a²/12+a⁴/672)m₂+(a⁴/1680)m₄`.
   For `0≤a≤11/20`, the cosh pole is at least `4aB²−M_G/300000`.

## Proof

Fubini gives the fourth correlation moment as
`m₀m₄−4m₁m₃+3m₂²` in raw full-window moments. Expanding in the first five
Legendre moments, applying Bessel's inequality, and completing squares gives
the two unit-window bounds. Dilation supplies the factor `a⁵`.

The degree-fourteen reciprocal hyperbolic bounds imply
`R(t)≥t³/864+t⁴/176` on `(0,11/10]`. On disjoint half-windows,
`|A(t)|≤M/2`, so the cubic deficit contributes at least `15a⁴M/8`.
The quartic deficit remains exact until the uniform bounds are applied.

The quartic cosh projection has pointwise error at most `1/1500000` and
squared size at most `441/400`. Cauchy–Schwarz bounds the integrated
projection and error. Completing the square gives the stated pole loss.
The Gamma tail identity follows by substituting `exp(−log(3)/2)=1/√3`;
rational exponential and harmonic estimates bound its mass coefficient.

## Lean

| Module | Main declarations |
|---|---|
| `WindowTowerOfSpecZ/TheGammaMassAtThePrimeThreeBoundaryIsCertified` | `archLevyAntideriv_log_three`, `gamma_mass_constant_at_aperture_log_three_half` |
| `LatticeSectionTheory/WindowJumpCounts/TheQuarticLagDeficitRetainsAMassReserve` | `autocorr_fourth_moment_le_mass`, `odd_autocorr_fourth_moment_le_mass`, `quartic_lag_deficit_ge_mass`, `odd_quartic_lag_deficit_ge_mass` |
| `WindowTowerOfSpecZ/TheGammaReserveRetainsTheQuarticLagDeficit` | `local_gamma_remainder_ge_fourth_deficit`, `local_gamma_remainder_ge_quartic_reserve`, `local_gamma_remainder_ge_odd_quartic_reserve` |
| `WindowTowerOfSpecZ/ThreeEvenMomentsRetainTheCoshPoleThroughApertureElevenTwentieths` | `even_cosh_pole_ge_three_moments` |

Direct `lake --old env lean` checks passed. Transitive axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are present.
