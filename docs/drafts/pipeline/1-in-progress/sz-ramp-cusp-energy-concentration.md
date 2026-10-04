# SZ: actual ramp current at the Gamma cusp

- **Stage:** 1-in-progress; conjecture, not a claimed theorem.
- **Target:** unconditional canonical-head Gamma--prime--polar positivity.

## Corpus-grounded conjecture

The actual exponential-ramp visible energy cannot be uniformly bounded as
the physical cutoff grows. More precisely, its current disappears away
from zero displacement, while its signed total action does not tend to
zero. Gamma capacity of a shrinking neighborhood of zero vanishes, so
bounded visible energy would force the action to vanish.

The intended positive survivor is an actual concentration law: cofinally
large visible energy in every fixed neighborhood of zero, together with
vanishing current outside that neighborhood. This would identify why an
absolute energy estimate loses the cancellation required by route SZ.
It would not prove that the signed action is unbounded or decide RH.

## Dependency-closed paper plan

1. `CCMPrimeQuantileHeightLimit` proves both literal cell displacements
   tend to zero. Extend the terminal displacement to real physical time.
2. `CCMPrimeDeficitFluxBoundary` identifies the flux state as the future
   exponential convolution of the normalized deficit. A tail bound
   epsilon on the incoming amplitude bounds the state by 2 epsilon.
   `CCMPrimeDeficitWeilFlux` identifies outgoing amplitude with actual
   Weil lag plus its archimedean correction. The unconditional lag
   oscillation in `WeilLagFunctionOmega` excludes incoming decay to zero.
3. `CCMQuantileExponentialRampDeficit` identifies the full signed ramp
   action with that incoming amplitude minus a decaying transient.
4. Outside any fixed cusp window, all late cells and terminal current
   vanish exactly. Only a fixed finite head remains; its coefficients
   decay as exp(-T/2) times an affine function of T.
5. Localize the weighted-square identity of
   `CCMExponentialRampCurrentProjection`. Integrability of the capacity
   density forces its shrinking-window integral to zero. Combine with
   steps 2--4 to exclude a cofinal tail bound on cusp visible energy.

No premise asserting RH, a source bound, a spectral gap, or a convergence
rate is allowed in the final actual-source obstruction. Intermediate
implications must be discharged. Full prime powers and both terminal
orientations remain present.

## Retrieval audit

Search `sz_ramp_cusp_search` (generation1220617) was partial, coverage
pending, with no useful primitive-oscillation hit. Direct source reads
established the flux-convolution mechanism above. Search misses do not
establish absence or novelty. Paper proof and Lean audit remain pending.
