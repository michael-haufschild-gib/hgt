# Uniform Gamma stability of actual generator heads

## Target

Find and formalize one constant K, independent of cutoff A, source coefficients,
source cardinality and horizon, such that the constructed finite real cell head
h=P_A f and tail t=f-h satisfy

Gamma(h)+Gamma(t) <= K Gamma(f).

The functions are the actual finite compact BV profiles from
ActualGeneratorHeadsPreserveTheSourceMean. No stability hypothesis may be added.
After this estimate, pay the remaining projected-Gamma term in the complete
even-power head error using the original Gamma reserve.

## Corpus inputs

- Exact stopping-block averages, finite BV realization and ordinary mean preservation.
- GammaMeanVarianceCapacity: simultaneous far-end mean graph and exterior mean
  charges bounded by the original Gamma energy for arbitrary disjoint intervals.
- GammaPairRemainder and GammaExteriorSubsets: actual interval kernels, exact
  averaging defects and a uniform first-moment bound for boundary rows.
- CompleteCellAveragesAreBoundedInGammaEnergy: homogeneous control at one paired
  level. Its constant is not iterated as a substitute for a depth-uniform proof.

## Direct comparison programme

The stopping partition has interval widths at most log 2. Consecutive widths
have uniformly bounded ratios: the initial logarithmic cells decrease slowly,
and the repeated band A<=a<2A resets by a bounded ratio.

For nonadjacent cells, an intervening neighbor makes the nearest separation
at least a fixed fraction of each endpoint width. A scalar density comparison
then bounds the actual kernel by a fixed multiple of the far-end kernel.
For adjacent cells, retain the integrated boundary defect; comparable widths
allow the far-end rectangle to pay that defect. A pointwise kernel comparison
at a touching endpoint is false and will not be used.

Use a finite contiguous partition containing the full source, padded by zero
cells on both ends. This makes nonzero exterior rows separated, avoiding a
false pointwise claim at an exposed nonzero boundary. Compare the complete
energy of the actual block averages with the existing original-source mean
graph and exterior charges. The quadratic triangle bound then pays the tail.

The kernel comparison, partition geometry and source identification each need
their own proofs and Lean formalization. The programme is not yet a proof.

## Scope

Ordinary mean and square-mass identities do not settle the exponential Weil
moments. First-prime payment and retained-orbit positivity are separate from
this Gamma operator bound. Working findings and continuation state are kept in
logs/signed-arithmetic-hodge-research.log.
