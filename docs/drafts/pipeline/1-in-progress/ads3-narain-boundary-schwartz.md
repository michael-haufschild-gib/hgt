# Schwartz regularity of the actual Narain Mellin boundary

- **ID:** W11-NBS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Quantitative saving](../3-formalized/ads3-narain-quantitative-boundary-saving.md)

## Conjecture

For every positive target-height pair, both functions

`L ↦ exp(L/2)[exp(−L)A_YZ(exp(−L))−(3/π)L−B_YZ]`

and `t ↦ narainMellinMean Y Z (it)` are Schwartz.

This gives all absolute clock moments and rapid decay of every boundary
and clock derivative. It asserts no holomorphic continuation into an
arithmetic zero-free half-plane beyond the proved region.

## Corpus mechanism

Put `M(u)=narainMellinMean Y Z u`, `G(t)=M(2πit)` and `F=Fourier(G)`.
Exact boundary normalization identifies the clock remainder with `F(−L)`.

The proved exponential boundary envelope and compact continuity give every
absolute moment of `G`. The corpus's `deningerFourier_contDiff` and
`deningerFourier_iteratedDeriv_bound` then give smoothness of `F` and
global boundedness of every derivative.

At negative frequency the actual quantitative remainder gives every
inverse-power bound for `F`. At positive frequency, the large-height
source estimate gives
`F(x)=exp(−x/2)[(3/π)x−B_YZ+o(1)]`.
Thus `F` itself decreases faster than every power on both rays.
Global boundedness extends the eventual bounds to the complete rays `x≥1`.

`RHTower.deningerSchwartzOfDecay` in
`Deninger/DeningerSchwartzOfDecay.lean` constructs a Schwartz function
from exactly these inputs. Its Landau interpolation propagates function
decay to every derivative. Fourier inversion then makes `G` Schwartz;
reflection and frequency dilation give the two displayed functions.
No spectral derivative estimate or additional contour shift is needed
for this qualitative conclusion.

The imported Fourier and interpolation endpoints have transitive axiom
audits containing only `propext`, `Classical.choice` and `Quot.sound`.
`NarainMeanBoundaryMoments.lean` proves every absolute spectral moment,
smoothness of the actual Fourier profile, and boundedness of every clock
derivative. Its three endpoint audits have the same standard axiom set.
The two source tails and Schwartz identifications remain to be formalized.
This argument does not by itself preserve a common quantitative saving
constant for all derivative orders; that stronger statement remains on
[the derivative card](../0-backlog/ads3-narain-logarithmic-derivative-saving.md).

## Gates

- [x] 0 → 1: spectral moments, exact normalization and interpolation inputs audited.
- [ ] 1 → 2: both source tails and Schwartz construction proved.
- [ ] 2 → 3: direct Lean checks, transitive axiom audits and umbrella imports.
