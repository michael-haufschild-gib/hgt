# Critical power-comb Abel integrability detects RH

- **Stage:** 3-formalized
- **Target:** A82; Abel replacement for ordinary critical divergence.
- **Claim:** `LogarithmicAbelIntegrable (powerCombTail (1/2)) ↔ RiemannHypothesis`.
  Under these equivalent conditions the actual logarithmic Abel mean tends
  to `criticalPowerCombAbelLimit`.

Let `B(s)=-ζ′/ζ(s+1/2)-ζ(s+1/2)` and
`E=criticalPowerCombElementaryLimit`. The limit is `E−2B′(0)`.
The critical comb never converges ordinarily; absolute Abel integrability
and its finite Abel limit provide the surviving endpoint statement.

RH gives subpolynomial critical-comb growth, hence absolute integrability
at every positive logarithmic damping. Conversely, absolute integrability
makes the literal contact transform holomorphic on `Re s>0`. Its continued
Dirichlet symbol has a nonzero pole at every right-hand zeta zero, forcing RH.

The exact comb decomposition is its convergent elementary remainder minus
twice the harmonic contacts. Central symmetry and the archimedean row
identity give `B(0)=criticalPowerContactCoefficient`. The harmonic-contact
Abel mean is `ζ(ε+1)(B(ε)−B(0))`. Its analytic extension is
`zetaResidueUnit(s+1) * dslope B 0 s`, whose value at zero is `B′(0)`.

Lean declarations in `CriticalPowerCombAbelIntegrabilityDetectsRH`:
- `logarithmicAbelIntegrable_criticalPowerComb_iff_rh`;
- `tendsto_logarithmicAbelMean_criticalPowerComb_of_rh`;
- `tendsto_logarithmicAbelMean_criticalPowerComb_of_integrable`.

Supports: `CriticalPowerContactAbelIntegrability`,
`CriticalPowerContactSymbolIsRegularAtZero`, `CriticalPowerContactAbelMean`.
Required support oleans and final single-file check passed; umbrella wired.
This extends contribution 12. No central ξ-curvature identity or interchange
of power-parameter and Abel limits is asserted.
