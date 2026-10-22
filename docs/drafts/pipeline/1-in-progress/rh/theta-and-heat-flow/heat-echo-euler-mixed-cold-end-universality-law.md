# Heat-echo/Euler mixed cold-end universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `RHTower/HeatApertureEchoHankel.lean`
  - `heatApertureRealLogEchoValue_add_eq_moment`
  - reciprocal prime-power node/base-weight representation
- `RHTower/EulerFisherLowTemperature.lean`
  - `eulerPrimePowerMoment_scaled_tendsto`

## Universal law

Heat depth and Euler Fisher order are two coordinates on one prime-power moment carrier. Define the
mixed moment by multiplying the heat base measure by the `k`th reciprocal-prime-power node and the
`m`th logarithmic-energy power. It is exactly the `m`th Euler Fisher moment at inverse temperature
`1 - sigma + q + k`. Therefore, for every logarithmic order `m`,

```text
2^(1-sigma+q+k) * mixedMoment(sigma,q,k,m) -> (log 2)^m.
```

The `m=0` member is the raw real heat-aperture log echo, giving its exact dyadic normalization and
prime-two ground-state limit `1`. The `m=2` member is the shifted Fisher conformal scale.

## Paper proof

For each prime-power node `N`, multiplication by its `k`th reciprocal power changes
`N^(-(1-sigma+q))` into `N^(-(1-sigma+q+k))`; the logarithmic-energy power is untouched. Termwise
equality gives the mixed/Fisher identity. Compose the all-real inverse-temperature ground-selection
theorem with the cofinal map `k |-> 1-sigma+q+k`. At logarithmic order zero, the heat-echo moment
identity removes the energy factor and identifies the mixed sum with the raw echo.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/HeatEchoEulerMixedColdEndUniversalityLaw.lean`.

Direct source check is deferred to final audit because both provenance modules currently lack
cached `.olean` artifacts; no early `lake build` was run.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
the separate heat-depth moment identity and Fisher cold-end limit but no mixed hierarchy or raw
heat-echo dyadic limit.
