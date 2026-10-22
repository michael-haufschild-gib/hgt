# Hedenmalm--Sonin finite-divisor analytic gauge flexibility

- **Label:** `P-G133`
- **Route:** P
- **Parents:** `P-G130`, `P-G132`, `XiHadamardFactorization`
- **Status:** theorem proved in Lean; umbrella integration complete

## Conjecture tested

P-G130 leaves discrete Xi support as one possible escape from the transverse analytic cusp no-go.
Test whether holomorphy on finite actual Xi-support packets constrains the required cancellation
values, or whether finite packets admit arbitrary analytic interpolation.

## Scientific decision gate

- **Success:** prove coefficient-exact entire interpolation of the Sonin cancellation modulus on
  every finite actual Xi-support packet, and determine whether more general data remain flexible.
- **Failure:** reject abstract interpolation unless nodes are the literal injective centered Xi
  divisor and the geometric aperture coefficient is included.
- If every finite packet is flexible, no finite discrete-gauge condition counts as producer;
  next gate must be a cofinal, packet-independent analytic budget.

## Prior-research audit

- 2026-08-13 — P-G130 proves no gauge holomorphic through a transverse neighborhood can have
  modulus `exp(-c|x|)` for all real `x` when `c>0`.
- 2026-08-13 — `XiHadamardFactorization` proves injectivity of the literal centered divisor map
  `xiSpectralPointSupport`.
- 2026-08-13 — Corpus contains general finite Lagrange interpolation and endpoint-corona density,
  but no Route-P specialization determining whether the discrete Sonin survivor is rigid.

## Conjecturing log

- 2026-08-13 — C1 proved in scratch: for every finite Xi-support packet `S` and rate `c`, explicit
  Lagrange polynomial has degree `< |S|` and exactly prescribed values
  `exp(-c |Im(xiSpectralPointSupport(rho))|)`.
- 2026-08-13 — C2 proved in scratch: interpolating polynomial is entire and nonzero at every node;
  its nodewise norm is coefficient-exact Sonin cancellation.
- 2026-08-13 — C3 proved in scratch: conclusion holds for every genuine geometric coefficient
  `N log(r)>0`, `N>0`, `r>1`.
- 2026-08-13 — C4 proved in scratch: arbitrary complex target values on every finite actual
  Xi-support packet admit an entire interpolant.  Finite holomorphic samples impose no constraint
  specific to Sonin escape or RH.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmSoninFiniteDivisorAnalyticGaugeFlexibility.lean`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSoninFiniteDivisorAnalyticGaugeFlexibility`
  (`12960/12960`).
- 2026-08-13 — Axiom audit passed for every new theorem; dependencies are exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Result and pivot

- Discrete analyticity without a uniform global budget is completely flexible at every finite
  level.  It cannot furnish a finite RH certificate or force neutral Cartan saturation.
- Strongest positive survivor is a sharp localization of the missing input: one needs a single
  cofinal entire/meromorphic gauge whose order, exponential type, norm, or source normalization is
  bounded independently of finite packet.  Degree `< |S|` witnesses exactly where uncontrolled
  complexity enters.
- Next target: test whether Route-P source data supplies a packet-independent growth/type budget.
  If not, retire analytic discrete gauges and pivot to a singular arithmetic trace.
