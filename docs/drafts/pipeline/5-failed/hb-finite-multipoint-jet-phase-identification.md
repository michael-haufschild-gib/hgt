# Failed route: finite multipoint-jet HB phase identification

- **ID:** HB-FINITE-JET-POSITIVE-CLOCK
- **Stage:** 5-failed
- **Status:** KILLED IN LEAN
- **Date:** 2026-08-31

## Failed claim

A finite packet of response derivatives, at any finite depth, can identify the causal
Schwarz-real all-pass phase needed to derive FE/minimum-phase clock covariance.

## Exact killing mechanism

For arbitrary finite `S ⊂ ℝ` and arbitrary `N`, formal theorem
`not_hbFiniteCrossFrequencyJetAllPassUnique` constructs two distinct entire zero-free responses
that share all iterated derivatives through order `N` at every point of `S`. Both obey exact
FE--Schwarz symmetry and unit boundary modulus, and both have strictly positive boundary
log-derivative clock at every real frequency.

Thus no observable or reconstruction rule factoring through a finite multipoint jet vector can
repair the finite-value HB producer. Increasing packet size or derivative depth while keeping both
finite still fails.

## Strongest positive survivor

Finite local jets fail, but the obstruction leaves four genuinely global data classes:

- bounded Hardy/Schur growth excluding the entire exponential witnesses;
- an infinite uniqueness set;
- external time-bilocal phase data;
- literal-source global minimum-phase or winding control.

At least one is logically required before the HB chain can derive source-predeclared FE--Schwarz
clock covariance and reach source-clock extinction.

## New insight

Strict time orientation does not restore finite-jet identifiability. Adding the odd flat phase
`±H` to an odd primitive with derivative `1+(H')²` makes both clocks uniformly positive:
`1+(H')²±H' = (H'±1/2)²+3/4`. Hermite flatness then hides the perturbation from every prescribed
finite analytic jet while a clock discrepancy elsewhere certifies distinctness.

## Paper and Lean status

Dependency-closed paper proof and unconditional Lean proof complete in
`GaloisForLFunctions.RHTower.HBFiniteCrossFrequencyJetPositiveClockNoGo`.
