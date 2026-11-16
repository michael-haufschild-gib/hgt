# The untwisted squarefree theta series has a nonzero pole

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** O2, signed long-column main terms.
- **Statement:** `twistedSquarefreeSeries 1` continues holomorphically from absolute convergence through `2/3 < Re w < 13/6, Im w > 0`, is holomorphic on a punctured neighbourhood of `2/3`, and has a nonzero simple pole there.

## Exact residue

Write `r = constantArithmeticResidue`, `C = rationalSourceThetaScalar`,
`M = besselSqMellin`, `B = 4π‖cuspFrequency 1‖`. The residue is

`R = 243π³r³ / [8 B^(−4/3) C̄² L(1,χ₋₃) M(4/3)] ≠ 0`.

The continuation agrees pointwise with the original series wherever
`2 < Re w < 13/6, Im w > 0`. [Mellin nonvanishing](the-untwisted-continuation-has-no-mellin-poles.md)
removes possible quotient poles from the original meromorphic construction.

## Paper proof [PROVED HERE]

1. Put `U = [[1,ω],[0,1]]`. Opposite conjugations preserve the product multiplier:
   `κ(UnU⁻¹)κ(U⁻¹nU)=κ(n)²`. Their Jacobi denominators multiply to
   `(a+ωc)(a−ωc)=a²−ω²c²`, congruent to `a²` modulo both nine and `c`, since `3∣c`.
2. The product `θ_s(Uw)θ_s(U⁻¹w)` has only one growing rational cusp. For cusp bottom
   rows `(c,d),(c′,d′)`, simultaneous high support forces
   `3∣c′d−d′c+2ωc′c`. Coordinate independence gives `3∣2c′c`; the four rational
   representatives force both cusps to be infinity. Subtracting that cusp profile
   leaves a bounded, square-integrable function of multiplier `κ²`.
3. Parseval reads the phased square
   `C_U(s)=Σ_h T(h)²e(2ωξ_h)(4π‖ξ_h‖)^(−s)`.
   On the source support, `e(ξ_h)=1`, while `e(ωξ_h)` is a cube root of unity and equals
   one exactly when `3∣h`. Pairing `h` with `−h` gives phase sum two on `3O` and
   minus one outside it. Therefore `D−C_U=(3/2)D₀`, where `D₀` is the square on `3∤h`.
4. The existing partial-cusp scattering formula with the singleton infinity cusp
   gives cleared scattering `3π|P|r`. The bounded remainder contributes at most a
   simple pole, so `M C_U` has double-pole coefficient `27π³r³`. The full square has
   coefficient `108π³r³`; the selector gives coefficient `54π³r³` for `M D₀`.
5. Every nonzero source coefficient outside `3O` is at a primary ideal generator or
   its negative. Unique frequency splitting separates these signs; their squares
   and frequency norms agree. Existing cube removal then gives
   `D₀(s)=2 B^(−s) C̄² Z₀(3s/2−1) S₁(s/2)`.
   Since `(s−4/3)Z₀(3s/2−1)→(4/9)L(1,χ₋₃)`, the double pole becomes a simple pole
   of `M(s)S₁(s/2)`, with residue `243π³r³/[4 B^(−4/3) C̄²L(1,χ₋₃)]`.
6. `M` is holomorphic on `Re s>2/3` and nonzero at `4/3`; divide locally and change
   variables `s=2w` to obtain `R`. Its factors are all nonzero by existing corpus
   results. The quotient is meromorphic on the upper strip. Analytic uniqueness
   and `M(4/3)≠0` exclude local vanishing of `M`, proving agreement of germs even at
   its isolated zeros.

## Lean declarations

All paths below are in `formal/GaloisForLFunctions/SpectralTheoryOfTheCubicCover/`.

| Module | Mathematical output |
|---|---|
| `TheOppositeTranslationsPreserveTheCubicMultiplier` | `sourceTheta_opposite_shifts_automorphy` |
| `TheTranslatedThetaProductHasOneCuspSubtraction` | `thetaLinear_translation_mul`, bounded translated remainder |
| `TheTranslationPhaseSeparatesTheUnramifiedSquare` | `source_translation_phase_pair`, `thetaSquare_translation_selector` |
| `TheTranslatedThetaProductReadsThePhasedSquare` | `cuspConstantTerm_translatedThetaProduct` |
| `TheTranslatedCorrelationHasADoublePole` | `translatedCorrelation_double_pole` |
| `TheTranslatedDifferenceIsTheUnramifiedSquare` | `thetaSqDirichlet_sub_translated` |
| `TheUnramifiedSquareFactorsThroughTheUntwistedSeries` | `unramifiedSquare_eq_squarefree` |
| `TheUnramifiedThetaSquareHasADoublePole` | `completedUnramified_double_pole` |
| `TheUntwistedSquarefreeThetaSeriesHasASimplePole` | `untwistedSquarefreeSeries_simple_pole`, `untwistedThetaResidue_ne_zero` |

All nine modules passed final plain `lake --old env lean` checks and are umbrella-wired.
This isolation counts as one contribution. The additional Mellin-nonvanishing module
also passed its final plain check and is umbrella-wired; it strengthens the same result.

## Distinct connection and scope

The full square and rotated correlation already had poles. Rotation weights
`T(ωh)T(h)`, so subtracting its half-residue does not isolate `T(h)²`. Opposite
translations preserve the square while their additive phases select the
unramified layer. This identifies the pole of an actual squarefree arithmetic
series, rather than a mixed combination of twists.

The row-root-number normalization involves the conjugate of this theta-square
weight and a conductor phase. The pole alone proves neither a row-root first
moment nor a smoothed asymptotic or column-uniform remainder. Those parts of O2
remain open. Internal corpus comparison only; no external literature or axiom checks.
