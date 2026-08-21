# Nearest-neighbour Gaussian same-draw growth--plateau--recurrence law

- **ID:** nearest-neighbor-gaussian-same-draw-growth-plateau-recurrence-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Brown--Susskind static-local complexity program
- **Statement:** A positive-measure set of one-draw centred Gaussian Hamiltonians in the complete Hermitian onsite-plus-edge space of a fixed qubit path simultaneously has robust laboratory-time linear operator-complexity growth, completed-time circuit-hard occupation, and perpetual recurrence--hardness--recurrence alternation.

## Result

The inverse-square ramp Hamiltonian is proved to lie exactly in the full Hermitian
nearest-neighbour path-local subspace.  Use any canonical real basis of that subspace and draw all
coefficients independently from centred unit Gaussians, once.

For every admissible positive laboratory tube radius, the set of draws that both

1. obey the uniform operator-complexity floor
   `floor(t/(256 π ε)) ≤ C₂,ε(exp(-itH))` throughout the certified laboratory interval, and
2. have maximal projective spectral rank

has strictly positive Gaussian probability.  Every draw in this same event also obeys, for every
finite circuit dictionary satisfying the explicit entropy inequality:

- the completed-time circuit-target occupation bound by projective Haar volume;
- a finite syndeticity constant after every starting time for an ordered recurrence--hard
  epoch--recurrence triple.

No Hamiltonian is redrawn between the three regimes.

## Conjecturing ledger

### C0 -- the engineered ramp is not an ordinary nearest-neighbour Hamiltonian

**Falsified.**  Each matching occupation projector is supported on a matching path edge; each
bridge projector is supported on the following bridge edge (or is exactly zero at the terminal
index).  Their weighted sum is exactly the inverse-square chain Hamiltonian.  Hence it belongs to
the complete onsite-plus-edge Hermitian path subspace.

### C1 -- the early-growth cap may lie inside the spectrally exceptional locus

**Falsified.**  The maximal-projective locus has Lebesgue-null complement in the canonical local
coefficient space.  Centred product Gaussian and Lebesgue measure are mutually absolutely
continuous, while every positive-radius coefficient ball has positive Gaussian mass.  Removing
the exceptional locus therefore preserves positive cap mass.

### C2 -- separate early and late theorems may require separate draws

**Falsified.**  Event membership records growth and maximal spectrum for the identical parameter
vector.  The completed-time plateau and recurrence alternation are deterministic consequences of
that same maximal spectrum.

## Lean certificate

- Growth/genericity module: `GaloisForLFunctions.HTGeometry.NearestNeighborGaussianSameDrawGrowthLaw`
- Same-draw capstone module: `GaloisForLFunctions.RHTower.NearestNeighborGaussianSameDrawGrowthPlateauRecurrenceLaw`
- Main probability theorem: `measure_nearestNeighborPathGaussianGrowthMaximalEvent_pos`
- Main capstone: `nearestNeighborPath_sameDraw_growth_plateau_recurrence`
- Targeted source checks and `lake build` passed for both modules.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Both umbrellas import the new modules.

## Hostile boundary

This is the first closed one-draw bridge across all three qualitative regimes for an ordinary
nearest-neighbour coefficient space, but it is not yet the requested Brown--Susskind theorem:

- growth has positive probability, not probability `1-o(1)`;
- its certified interval is laboratory scale `t ≤ εL`;
- plateau is a completed-time occupation statement, not a quantified continuous plateau with
  effective onset;
- recurrence is qualitative syndetic alternation, not a matching exponential lower bound on first
  return to the full polynomial-complexity circuit set.

The remaining open core is still fixed-time static-local circuit/heap incidence decay strong
enough to beat the full intrinsic circuit capacity after return/carrier excision.

## Log

- 2026-08-21 -- C0 proved in scratch: exact path-local support and subspace membership.
- 2026-08-21 -- C1 proved: positive Gaussian mass survives full-measure spectral genericity.
- 2026-08-21 -- C2 proved: one parameter vector composes uniform growth, completed occupation plateau, and recurrent hard epochs.
- 2026-08-21 -- both Lean modules source-checked, targeted-built, axiom-audited, and wired.
- 2026-08-21 -- Strengthened completed occupation to pathwise continuous hard blocks.  A packing
  theorem proves that wide-target density `b` and visit thickness `delta` force arbitrarily late
  narrow-target-free intervals of every length satisfying `b < delta/(W+delta)`.  For projective
  Choi flow, Lean proves the explicit speed
  `sqrt(2)(1+sum_i |E_0-E_i|)` in Hilbert--Schmidt distance, so the operational trace-radius visit
  thickness is exactly `(eps_w-eps_n)/(1+sum_i |E_0-E_i|)`.  The same nearest-neighbour parameter
  now composes laboratory growth, quantitative continuous avoidance of the complete padded circuit
  dictionary, and perpetual recurrence alternation.  Remaining gap is first onset, not continuous
  plateau filling.
