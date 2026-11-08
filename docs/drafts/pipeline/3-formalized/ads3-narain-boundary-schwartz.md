# Schwartz regularity of the actual Narain Mellin boundary

- **ID:** W11-NBS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Quantitative saving](ads3-narain-quantitative-boundary-saving.md)

## Theorem

For every positive target-height pair, both functions

`H(L)=exp(L/2)[exp(−L)A_YZ(exp(−L))−(3/π)L−B_YZ]`

and `t ↦ M(it)`, where `M=narainMellinMean Y Z`, are Schwartz.
Every polynomial clock moment and every polynomial moment of every
spectral derivative converges absolutely. Moreover, `∫ℝ H(L)dL=0`.

## Proof

Put `G(t)=M(2πit)` and `F=Fourier(G)`, with mathlib’s `2π` convention.
Exact boundary normalization gives `H(L)=F(−L)`.
The exponential spectral envelope and compact continuity give every
absolute moment of `G`; Fourier differentiation therefore gives
smoothness of `F` and global boundedness of every derivative.

At negative frequency the actual arithmetic saving gives every
inverse-power bound for `F`. At positive frequency, large-height heat
decay gives `|F(x)|≤C(1+x)exp(−x/2)`. Global boundedness extends these
eventual estimates to both complete rays `x≥1`.

`RHTower.deningerSchwartzOfDecay` propagates function decay to every
derivative by Landau interpolation. Hence `F` is Schwartz. Pointwise
Fourier inversion, using continuity and integrability of `G`, makes
`G` Schwartz as well. Reflection gives the literal clock `H`; frequency
dilation by `(2π)⁻¹` gives the literal unscaled boundary `M(it)`.
Schwartz integrability supplies the asserted moments. Fourier inversion
at zero and `M(0)=0` give `∫H=0`.

## Lean

Five modules in `ArithmeticScatteringHolography/ModularBootstrap`:

- `NarainMeanBoundaryMoments`: spectral moments, Fourier smoothness and bounded derivatives.
- `NarainMeanFourierSource`: exact source normalization and rapid negative-frequency decay.
- `NarainMeanFourierPositive`: exponential positive-frequency bound.
- `NarainMeanSchwartz`: Schwartz Fourier pair and pointwise boundary identification.
- `NarainMeanSchwartzSource`: literal physical and spectral representatives, absolute moments and zero clock integral.

All five modules passed final direct Lean checks and are imported by the
umbrella. All eighteen endpoint axiom audits contain only `propext`,
`Classical.choice` and `Quot.sound`.

The [quantitative derivative bound](ads3-narain-logarithmic-derivative-saving.md)
is also formalized, with one factorial rate and threshold for all orders.
Neither conclusion supplies a fixed power above the square-root remainder boundary.

## Gates

- [x] 0 → 1: spectral moments, exact normalization and interpolation inputs audited.
- [x] 1 → 2: both source tails, Schwartz construction and literal identifications proved.
- [x] 2 → 3: final direct Lean checks, transitive axiom audits and umbrella imports.
