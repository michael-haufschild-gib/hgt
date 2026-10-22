# Xi prime--archimedean thermal endpoint universality law

- **ID:** xi-prime-arch-thermal-endpoint-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proved, hostile-audited, Lean-direct-checked; no priority claim)
- **Source:** Bottom-up join of terminal critical prime--polar abscissa classifiers found in the
  post-Law-19 endpoint scan
- **Statement:** For every positive rectangular window and admissible tail, the critical
  prime--polar negative-source abscissa bound is one datum simultaneously realized in 31
  Hausdorff, Bernstein, finite-KMS, positive-atomic, orientation, thermal-moment, endpoint
  resolvent, scattering, projective, cold-partition, free-energy, and Born--Witten charts.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one` identifies the
   positive-window prime--polar abscissa endpoint with RH.
2. The scaled/raw Hausdorff, cofinal quadrant/diagonal, Bernstein negative-mass, and endpoint-purity
   classifiers identify nine calibrated moment realizations with RH.
3. The finite KMS Wightman, finite positive-atomic local, and positive-atomic diagonal-approximation
   classifiers identify three finite localization realizations with RH.
4. The rectangular and weighted Hausdorff-tail classifiers and cofinal Bernstein-square
   discrepancy classifier identify three direct prime--polar endpoint consequences.
5. The orientation-energy, thermal second-moment, and truncation-limit classifiers identify three
   thermal source realizations with RH.
6. The endpoint-resolvent value, endpoint-resolvent truncation, and scattering-phase classifiers
   identify three endpoint spectral realizations with RH.
7. Eventual and frequent diagonal bounds, cofinal projective moments, cold-partition bounds,
   two-scale thermodynamic bounds, first-moment vanishing, and diagonal free-energy convergence
   identify seven projective thermal realizations with RH.
8. Equality, inequality, and truncation convergence to the Born--Witten source identify three
   explicit source realizations with RH.

## Paper proof

Fix `L > 0` and an admissible tail cutoff `N`. Assume the critical prime--polar abscissa bound.
Input 1 gives RH. Each RH classifier in Inputs 2--8 yields its certificate component; the three
direct prime--polar endpoint classifiers in Input 4 yield theirs without an intermediate rewrite.
This proves all 31 components.

Conversely, the first certificate component is scaled Hausdorff nonnegativity. Its exact
prime--polar endpoint classifier recovers the critical abscissa bound. Therefore the abscissa bound
is equivalent to the full simultaneous certificate. `[PROVED HERE]`

## Formalization target

- Module: `formal/GaloisForLFunctions/RHTower/XiPrimeArchThermalEndpointUniversalityLaw.lean`
- Certificate: `XiPrimeArchThermalEndpointUniversalCertificate`
- Capstone:
  `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointUniversalCertificate`

## Internal noncollision audit

`scripts/formal_tools.py research "prime polar negative abscissa thermal endpoint resolvent
projective diagonal cold partition orientation energy"` returned the individual endpoint families,
their RH classifiers, and local Hausdorff/KMS closure theorems, but no common certificate. Direct
consumer search found no module importing and consuming all Hausdorff/Bernstein, finite-KMS,
resolvent, projective, and Born--Witten terminal families. The 31-way closure was therefore absent
from the Lean corpus before this module.

## Hostile literature audit

Exact searches combining prime-polar sources with Hausdorff moments, Bernstein purity, KMS closure,
thermal endpoint resolvents, projective free energy, and Born--Witten moments found no collision.
Hedenmalm's primary
[Spectral interpretation of Riemann zeta zeros](https://arxiv.org/abs/2606.17494) develops the
theta differential-operator setting, not this 31-chart equivalence. Zhang's
[Complete Monotonicity of Special Functions](https://arxiv.org/abs/1506.07012) studies complete
monotonicity and Xi-related special functions but not these calibrated prime--archimedean endpoint
objects. Dueñas--Svaiter's
[Thermodynamics of the Bosonic Randomized Riemann Gas](https://arxiv.org/abs/1401.8190) uses zeta
partition functions in a different statistical-mechanical model. Connes--Consani's
[Weil positivity and trace formula](https://arxiv.org/abs/1910.14368) concerns the Weil criterion
and trace-formula geometry, not this Hausdorff/KMS/resolvent/projective synthesis. Evidence supports
noncollision only; no priority claim is made.

## Log

- 2026-07-22 — Found by reading terminal prime--polar negative-abscissa endpoints and then tracing
  their actual RH consumers across Hausdorff, Bernstein, KMS, thermal, projective, and source modules.
- 2026-07-22 — Capstone formalized and exact direct check
  `lake env lean GaloisForLFunctions/RHTower/XiPrimeArchThermalEndpointUniversalityLaw.lean` passed.
- 2026-07-22 — Hostile exact and neighboring-concept literature audit passed; nearest Hedenmalm,
  complete-monotonicity, Riemann-gas, and trace-formula sources are materially different.
