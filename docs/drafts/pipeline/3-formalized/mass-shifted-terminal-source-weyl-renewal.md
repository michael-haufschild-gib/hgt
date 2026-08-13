# Mass-shifted terminal-source Weyl renewal

- **ID:** mass-shifted-terminal-source-weyl-renewal
- **Stage:** 3-formalized
- **Type:** THEOREM + SHARP NO-GO BOUNDARY
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** Terminal Γ-completed source resistance has an exact Cauchy aggregate equal to the adjacent orthogonal-polynomial ratio, and this aggregate obeys nonlinear Jacobi coefficient stripping across degree.

## Goal

Construct missing admission-sensitive arithmetic source carrier before reflection aggregation.  Unlike a
fixed linear reporter, the carrier must retain terminal source mass and renew with the changing finite
Hankel admission.  Door passport: finite positive moment blocks only; no representing measure, no
infinite moment extension, no RH-equivalent hypothesis, no computation.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit standard-only
- [ ] 3 → 4 publication-ready: standalone theorem + proof + Lean certificate + Door-2

## Frozen conjectures and hostile tests

### C1 — terminal-resistance Weyl identity

For `m + 1 < N` and `P_{m+1}(z) ≠ 0`, define

`W_m(z) = Σ_{x : P_{m+1}(x)=0} r_m(x)/(z-x)`,

where `r_m(x)=λ_m(x)P_m(x)^2/h_m` is terminal source resistance.  Then

`W_m(z)=P_m(z)/P_{m+1}(z)`.

Attack: interpolate `P_m` in normalized Christoffel--Darboux Gauss basis and use finite-block
Christoffel--Darboux pointwise.  Failure criterion: any use of a global representing measure or an
unavailable infinite positivity extension.

### C2 — nonlinear degree renewal

For consecutive admissible blocks,

`W_{m+1}(z)=1/(z-α_{m+1}-β_{m+1}W_m(z))`.

Attack: substitute C1 into the corpus three-term recurrence.  Failure criterion: renewal needs a
fixed moment law beyond the supplied finite positive block.

### C3 — Γ-completed source representation

At an admitted mass-shifted Xi root, terminal source amplification gives

`r_m(x) Γhat_m(x)=t_m(x)^4`.

Therefore each Weyl atom has the source-first representation

`r_m(x)/(z-x)=t_m(x)^4/(Γhat_m(x)(z-x))`.

This is bilinear/nonlinear in admission data and source completion before any reflection sum.
Failure criterion: division by a source that may vanish, or replacement by a fixed linear reporter.

### C4 — budget test

C1--C3 preserve source under degree renewal, but do not themselves provide a finite all-degree
budget.  Hostile audit must distinguish exact carrier construction from closure of RH.  If total
de-resisted pole mass grows with degree, record this as the exact remaining obstruction rather than
claiming route completion.

## Approach

1. Prove C1 and C2 generically in `HTGeometry` from finite-block primitives.
2. Specialize C3 to canonical shifted-Xi admissions using existing terminal source amplification.
3. Audit positivity, denominators, axiom footprint, and all-degree budget.  Promote only the exact
   theorem actually proved.

## Theorem and proof `[PROVED HERE]`

Let `P_j` be finite-block monic orthogonal polynomials, `X_m` the roots of `P_(m+1)`, and

`r_m(x) = lambda_m(x) P_m(x)^2 / h_m`.

For `P_(m+1)(z) != 0`, Gaussian interpolation of `P_m` in the normalized Christoffel--Darboux
basis gives

`P_m(z) = sum_(x in X_m) P_m(x) B_(m,x)(z)`.

Christoffel--Darboux at `P_(m+1)(x)=0` gives, pointwise,

`P_m(x) B_(m,x)(z) = P_(m+1)(z) r_m(x)/(z-x)`.

Summing and dividing by the nonzero current admission proves

`W_m(z) := sum_x r_m(x)/(z-x) = P_m(z)/P_(m+1)(z)`.

Substitution into the finite-block three-term recurrence proves

`W_(m+1)(z) = 1/(z-alpha_(m+1)-beta_(m+1)W_m(z))`.

At a complex aperture, the same identity and the imaginary part of the inverse Riccati law give

`Q_(m+1)=|W_(m+1)|^2(eta+beta_(m+1)Q_m)`,

where `Q_m=-Im W_m`.  Since `W_(m+1) != 0`, division yields exact normalized source injection

`Q_(m+1)/|W_(m+1)|^2-beta_(m+1)Q_m=eta`.

For shifted-Xi admissions, the previously proved terminal source product says

`r_m(x) * (Padé residue * completed P^sharp capacity) = w^2 x^4 h_m`.

Thus reciprocal normalization of the already-formed source product lands exactly in `r_m(x)`, so
the literal completed-source aggregate is `W_m` and inherits its nonlinear renewal.

To test fidelity, multiply `r_m(x)` by the actual completed-source product and divide by the hard
forcing `w^2 x^4 h_m`.  Every nonzero admitted node then has coefficient exactly one.  Since a
degree-`n` current admission has exactly `n` simple nodes, faithful total source is exactly `n` and
adjacent total increment is exactly one.

Finally finite-block splitting gives `P_n(z)=prod_x(z-x)`.  Differentiating the finite product and
dividing away from the real roots proves

`sum_x 1/(z-x) = P_n'(z)/P_n(z)`.

Taking negative imaginary parts gives faithful Poisson localization of the literal de-resisted
completed source.

All arguments use only the supplied finite positive moment block.  No representing measure,
infinite moment extension, limiting computation, or RH premise occurs.

## Sharp boundary and positive survivor

The hostile test closes the no-go, rather than merely recording failure:

- normalized terminal resistance has total mass one and exact nonlinear degree renewal, but an
  individual admitted share has no positive uniform lower bound;
- de-resisted completed source is faithful at every node, but its raw positive total is exactly
  degree and therefore grows without bound along every unbounded admission tower.

Hence no raw positive diagonal normalization can simultaneously be finite and faithful.  This is
the exact normalization--fidelity boundary.  Positive survivor is the source-first unit-pole
carrier

`sum_x 1/(z-x)=P_n'(z)/P_n(z)`,

with positive Poisson localization at every nonreal aperture.  Remaining route must center this
faithful carrier at the moving apex and produce a signed/adaptive arithmetic coboundary; another
positive trace budget, orientation map, or fixed linear reporter cannot close the route.

## Lean certificate

- `HTGeometry/GaussTerminalWeylRenewal.lean`: terminal Weyl ratio, real/complex Riccati renewal,
  positive Poisson localization, exact normalized aperture injection.
- `HTGeometry/GaussTerminalSourceLogDerivative.lean`: finite Gauss-node factorization, faithful
  unit-pole/log-derivative identity, Poisson density.
- `RHTower/XiShiftedCanonicalAdmissionTerminalSourceWeylRenewal.lean`: literal shifted-Xi
  completed-source landing and nonlinear renewal.
- `RHTower/XiShiftedCanonicalAdmissionDeResistedCompletedSource.lean`: coefficient-one fidelity,
  total-degree law, one-unit renewal, literal log-derivative landing.

All four targeted modules build.  `#print axioms` on principal theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Route-specific source coupling remains
`[NOVELTY UNVERIFIED]`.

## Log

- 2026-08-13 — created in 1-in-progress after corpus search found terminal resistance conservation
  and Γ amplification but no terminal Weyl/continued-fraction renewal theorem.
- 2026-08-13 — C1--C4 proved on paper and unconditionally in Lean.  Hostile audit exposed and
  closed normalization--fidelity no-go; positive unit-pole/log-derivative survivor extracted.
