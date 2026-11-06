# Raw pointwise modular-echo ringdown

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** No constants `A,B,b` give an eventual uniform upper bound `K(t)-A exp(t/2)≤B exp(bt)` for the raw totient echo train.

## Exact obstruction

At each positive denominator `c`, the train at `2 log c+v` dominates
`(ϕ(c)/c) v^(-1/2)` for `v>0`. These spikes are unbounded immediately after arrival, and arrival
times are unbounded. Subtracting an exponential mean cannot control them.

Lean: `GaloisForLFunctions.BlackHoleRingdown.echoKernel_sub_mean_exceeds_every_exponential`
in `TheEchoSpikesAndTheirGaussianObservation.lean`.

## Positive survivor

Gaussian observations converge absolutely and admit an explicit global exponential majorant.
Their transform is exactly the completed-zeta quotient multiplied by a nonzero Gaussian factor;
every Xi resonance retains its pole order. Thus a smoothed source estimate can test the complete
arithmetic divisor despite the raw pointwise obstruction.

Lean: `gaussianEcho_le`, `laplace_gaussianEcho`, and `gaussianEchoSymbol_resonance_order`, in
namespace `GaloisForLFunctions.BlackHoleRingdown`. Paper mechanisms, exact modules, and kernel
audits are recorded in the
[formalized survivor](../3-formalized/modular-horizon-sharp-boundary-and-gaussian-observation.md).

The active successor is the Gaussian-observation route. Its source-derived quarter-line estimate
remains open.
