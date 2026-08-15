# Route P resolved Ward generator graph

- **ID:** `route-p-primitive-burnol-ward-resolved-generator-graph`
- **Stage:** 3-formalized
- **Type:** POSITIVE BRIDGE with sharp unboundedness classification
- **Label:** `P-G199`
- **Source:** P-G197 resolved Ward columns, P-G186 primitive Burnol windows, P-G182 completed-Xi
  conormal residues, P-G198 polarization obstruction
- **Statement:** P-G197's resolved column is the Laplace transform of a radial exponential mode.
  Applying the common radial position generator before reporting gives the squared resolvent and
  exactly P-G182/P-G186's cubic conormal feature. Its exact real-rate graph amplification is
  `1/(2a^2)`, so no uniform bounded generator estimate exists on `0<a<=1/2`.

## Conjecture loop

P-G198 rules out direct positive polarization over distinct zero labels and leaves a common
generator on the external-node carrier as the live mechanism. The first candidate was to repeat
P-G168's abstract mixed Hardy jet. Corpus audit rejected that as theatre: P-G168 already computes
cubic order, while P-G182 and P-G186 already construct target and source cubic radial columns.

`C199-B` instead asks whether these independently constructed objects are literally one graph
operation applied to P-G197's resolved mode. For radial rate `lambda`, define

```text
e_lambda(L) = exp(-lambda L),
G e_lambda(L) = L exp(-lambda L).
```

Lean proves the exact chain

```text
C_lambda(w) = integral_0^infinity exp(-wL) e_lambda(L) dL
            = 1/(w+lambda),

integral_0^infinity exp(-wL) G e_lambda(L) dL
            = 1/(w+lambda)^2
            = -d/dlambda C_lambda(w),

G e_lambda(L)
            = routePXiBaseConormalResidueFeature(lambda+1/2,L)
            = xiWardCubicBurnolWindowConormalFeature(L,lambda+1/2).
```

Every primitive Burnol source column is exactly this generated mode multiplied by its original
resolved von Mangoldt depth amplitude. For arbitrary complex strict-right rates, the cross-Gram
of generated modes is exactly P-G181/P-G182's cubic Cauchy kernel.

## Sharp graph wall

For a positive real rate `a`, the base and generated energies are

```text
||e_a||^2   = 1/(2a),
||G e_a||^2 = 1/(4a^3),
||G e_a||^2 / ||e_a||^2 = 1/(2a^2).
```

For every proposed bound `C`, Lean constructs `0<a<=1/2` with `C<1/(2a^2)`. Therefore no uniform
bounded operator estimate can convert the base Hardy family into the cubic conormal family over
the strict-right chamber. This is the exact graph-norm obstruction hidden behind P-G198.

## Higher principle and next conjecture

P-G197 positivity is a bounded frame statement; W-H184 is a graph-domain statement. Cubic charge
appears only after the unbounded radial generator, and its boundary blow-up is exactly quadratic
in inverse centered rate. The missing polar--Gamma producer cannot be a bounded contraction on the
base Hardy completion. It must be a source-selected graph-domain map whose coefficient weights pay
the `1/(2a^2)` amplification while retaining P-G196's aperture commutator anomaly.

Next conjecture: the polar--Gamma boundary surplus supplies precisely the graph quadratic form of
`G` on finite primitive packets, including reflected cross terms. If its source form dominates the
actual Xi graph form with total primitive trace `<2`, W-H184 closes. If not, classify the exact
signed surplus or domain defect and pivot there.

## Hostile novelty audit

Individual cubic Laplace/Gamma identities and the source/target conormal columns already existed.
Novel content is the exact source-coefficient-faithful bridge from P-G197's resolved Ward mode
through one common radial generator to both P-G186 and P-G182, together with the exact graph-energy
ratio and uniform boundedness no-go in the strict-right chamber. No RH premise, zero-location
premise, boundedness premise, or new axiom occurs.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolWardResolvedGeneratorGraph.lean
```

Capstones:

- `xiWardCayleyResolventColumn_zero_eq_radialMode_laplace`;
- `routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode`;
- `integral_star_xiWardResolvedRadialGeneratorMode_mul`;
- `integral_xiWardResolvedRadialGeneratorMode_laplace`;
- `xiWardResolvedRadialGenerator_energy_ratio`;
- `not_exists_uniform_xiWardResolvedRadialGenerator_energy_bound`.

Verification:

- `/tmp/pg199.lean`: `lake env lean /tmp/pg199.lean` passed with zero output;
- exact leaf target built successfully; no umbrella/full build run;
- `/tmp/pg199_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] identify P-G197 resolved column as radial Laplace mode
- [x] identify common generator transform as squared resolvent / mode derivative
- [x] identify generated mode with P-G182 completed-Xi conormal feature
- [x] identify generated mode with P-G186 Burnol window feature
- [x] retain exact primitive von Mangoldt depth coefficient
- [x] prove full complex cross-Gram is cubic Cauchy kernel
- [x] prove exact base and graph energies
- [x] prove uniform bounded-generator no-go on strict-right chamber
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [x] identify every primitive generated reporter with its canonical reflected Deninger negative
  Cauchy square (P-G200)
- [ ] construct coefficient-faithful polar--Gamma graph quadratic form
- [ ] prove finite-packet source domination of actual Xi graph form
- [ ] instantiate W-H184 and prove unconditional RH
