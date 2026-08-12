# Mass-shifted hard-edge worldline/source conservation

- **ID:** `mass-shifted-hard-edge-worldline-source-conservation`
- **Stage:** 3-formalized
- **Type:** THEOREM / ARITHMETIC SOURCE PRODUCER / EFFECTIVITY INTERFACE
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL] [SCALE INTERPRETATION CORRECTED] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core

## Result

Let `P_n(y)` be actual degree-`n` inverse-Hankel shifted-Xi admission in a finite positive
chamber, `x(y) != 0` a differentiable local root branch, `lambda` its Christoffel weight, and

```text
u(y) = x(y)⁻¹-y,
h_n(y) = L_y(P_n(y)^2),
Gamma(y) = y*x(y)^4*lambda(y)*P_n'(y,x(y))^2.
```

Actual coefficient ODE, half-density landing, and finite confluent Christoffel--Darboux give

```text
∂_y P_n(y,x) = x^2*P_n'(y,x) + 2*n*beta_n*P_(n-1)(y,x),
beta_n*lambda*P_n'(y,x)*P_(n-1)(y,x) = h_n.
```

Implicit differentiation at the root therefore yields exact source/worldline conservation

```text
u'(y)*Gamma(y) = 2*n*y*x(y)^2*h_n(y).
```

Existing adaptive completed-source capacity identity `rho*C_eff=Gamma` upgrades this to

```text
u'(y)*rho(y)*C_eff(y) = 2*n*y*x(y)^2*h_n(y).
```

After shape normalization:

```text
u'(y)*(Gamma(y)/h_n(y)) = 2*n*y*x(y)^2.
```

With `y=w^2`, actual parabolic hard-coordinate derivative is `dot u=2*w*u'`, hence

```text
dot u(w)*(Gamma(w)/h_n(w)) = 4*n*w^3*x(w^2)^2.
```

If `x=(w^2+u)⁻¹`, `u/w² -> 0`, and `n/w -> c`, Lean proves explicit forcing tends to `4*c`.
Any uniform speed cap `dot u <= K`, `K>0`, forces

```text
Gamma/h_n >= 4*n*w^3*x^2/K.
```

The last two identities control **relative** mass `Gamma/h_n` inside a positive chamber. They do
not control absolute terminal mass `Gamma` at a flat face, where `h_n=0`. In particular,
`Gamma -> 0` does not imply `Gamma/h_n -> 0`, and no speed-escape conclusion follows without a
separate lower comparison between `Gamma` and `h_n`.

## Conjecture → proof/failure loop

1. **Existing fixed integral-Lipschitz law bounds hard-root speed — FAILED.** It controls Hankel
   quadratic forms for one coefficient vector. Growing-degree root mobility also divides by root
   derivative and is not bounded by that theorem.
2. **Gauss terminal mass is passive observer data — FALSIFIED.** It is inverse mobility for actual
   admission dynamics.
3. **Coefficient transport requires a chosen orientation — FALSIFIED.** Canonical inverse-Hankel
   derivative plus source-native half-density connection evaluates exactly at every admitted root.
4. **Ordinary confluent Darboux needs an infinite positive moment form — FALSIFIED.** One finite
   positive block proves exact derivative/Christoffel coupling.
5. **Zero absolute terminal mass forces unbounded critical root motion — FALSIFIED.** The
   bounded-speed corollary supplies a floor only for `Gamma/h_n`; at flat contact both numerator
   and norm can vanish. This was a scale error, not a missing estimate.

## Higher universal principle

Source capacity, Padé residue, and root motion form force–relative-mass–mobility variables inside
the open positive chamber:

```text
source forcing = root speed * residue * adaptive source capacity.
```

At the singular face, this coordinate chart degenerates because orthogonal norm vanishes. The
positive survivor is exact chamber dynamics; the correct boundary invariant must retain contact
order. Subsequent flat-contact transmutation proves first-order hard-root mobility vanishes while
adaptive completed source survives in a higher norm-flux jet.

## Exact remaining burden

No root-speed theorem can repair the absolute/relative scale mismatch by itself. Route now splits:

1. positive terminal mass: exclude surviving positive-axis Padé atoms by a source-derived local
   boundedness/extinction theorem for canonical Padé resolvents;
2. zero terminal mass: exploit parity-doubled radical and higher contact-order adaptive source.

Flat-contact source transmutation is formalized separately in
`XiShiftedCanonicalAdmissionFlatContactSourceTransmutation`. RH is not yet proved.

## Lean realization

Generic finite infrastructure:

```text
GaloisForLFunctions.HTGeometry.FiniteConfluentDarboux
```

Route module:

```text
GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw
```

Principal capstones:

```text
HTGeometry.cdKernel_diag_mul_eq_below
HTGeometry.christoffel_mul_derivative_mul_prev_eq_normSq_below
HTGeometry.monicOrthoBeta_mul_christoffel_mul_derivative_mul_prev_eq_normSq_below
hasDerivAt_finitePolynomialCurve_eval
finitePolynomialVelocity_xiShiftedCanonicalAdmission_eval_root
xiShiftedCanonicalAdmission_rootCurve_chain
xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_terminalMass_eq_normSq
xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_residue_mul_sourceCapacity_eq_normSq
xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_normalizedTerminalMass
xiShiftedCanonicalAdmissionParabolicHardEdgeWorldline_mul_normalizedTerminalMass
xiShiftedCanonicalAdmissionHardEdgeNormalizedTerminalMass_pos
xiShiftedCanonicalAdmissionParabolicHardEdgeNormalizedTerminalMass_ge_of_speed_le
tendsto_xiShiftedParabolicHardEdgeWorldlineForcing
hasDerivAt_xiShiftedParabolicReciprocalHardRoot
```

## Verification

- direct `lake env lean GaloisForLFunctions/HTGeometry/FiniteConfluentDarboux.lean`: PASS;
- targeted `lake build GaloisForLFunctions.HTGeometry.FiniteConfluentDarboux`: PASS;
- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw.lean`: PASS;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw`: PASS;
- `#print axioms` audit of ten route capstones: only `propext`, `Classical.choice`, and
  `Quot.sound`;
- theorem-area umbrella imports: wired and recognized by formal lint;
- repository-wide formal lint remains red only on unrelated concurrent unreachable modules;
- no computations, `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declarations.
