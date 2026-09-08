# Actual cutoff-period value and physical Xi calibration

## Mathematical result

Let `E_u` be the complete original scalar Eisenstein field, `mu` the original
hyperbolic measure on the modular fundamental domain, and

```text
eta(y) = smoothTransition(y-2),
h_k(y) = eta(y)*y^k,
C_k = Delta_H(h_k)-k(k-1)*h_k,
K(u,k) = integral E_u C_k dmu.
```

The already admitted integral `K` has an exact value for all complex parameters.
For either original Weyl exponent `delta`, put

```text
B(delta,k) = integral_1^4 y^(delta-2)*h_k(y) dy,
V(delta,k) = (k-delta)*4^(delta+k-1)
             + [delta(delta-1)-k(k-1)]*B(delta,k).
```

If `c_-(u), c_+(u)` are the original coefficients and
`delta_-(u), delta_+(u)` the original exponents, then

```text
K(u,k) = c_-(u)*V(delta_-(u),k) + c_+(u)*V(delta_+(u),k).
```

At either Weyl root `k=delta_branch(u)`, this specializes to

```text
K(u,k) = (2k-1)*c_opposite(u).
```

These are values derived from the full integral. The all-parameter formula
retains the eigenvalue-mismatch bulk term.

## Physical Xi specialization

For every Xi divisor copy `q`, the literal spectral-point and physical-momentum
definitions give `u=i*chi_q=(q-1)/2`. The original Weyl exponents are `q/2`
and `1-q/2`; their coefficients are respectively `Lambda(q)` and
`Lambda(q-1)`, where `Lambda(s)=GammaR(s)*zeta(s)` in the corpus.

Lean proves, without a zero-location or nonvanishing premise,

```text
K((q-1)/2,q/2) = (q-1)*Lambda(q-1) != 0,
K((q-1)/2,1-q/2) = 0.
```

The original full scalar field obeys modular inversion at this physical
parameter, and its principal part is exactly
`Lambda(q-1)*y^(1-q/2)`.

## Proof

The complete Fourier tail has zero horizontal mean. Generalizing the existing
native cusp-field integration theorem to every threshold `L>=1` transports
the actual full-field pairing, with its hyperbolic density, to a height
integral. The differential commutator vanishes below height two and above
height three, so endpoints one and four retain the entire transition.

The cutoff-height field is globally smooth, including through nonpositive
height. Its actual hyperbolic Laplacian is `y^2*h_k''`. Differentiate the
literal Wronskian

```text
W(delta,k;y) = y^delta*h_k'(y)-delta*y^(delta-1)*h_k(y).
```

Its derivative is

```text
y^(delta-2)*C_k(y)
  + [k(k-1)-delta(delta-1)]*y^(delta-2)*h_k(y).
```

The original cutoff's endpoint germs give `W(1)=0` and
`W(4)=(k-delta)*4^(delta+k-1)`. The fundamental theorem of calculus yields
the stated moment value. For `delta=k`, the moment is zero; for `delta=1-k`,
it is `2k-1`. Both mismatch coefficients then vanish algebraically.

At every Xi target, `Lambda(q)=0` follows from Xi support and the strict
strip. At the nonreal point `q-1`, the Gamma factor is nonzero and
`Lambda(q-1)` equals the completed zeta value. The functional equation
reflects it to `2-q`, whose real part is greater than one. The corpus's
zero-free-half-plane theorem makes that value nonzero. Nonreal `q` also
gives `q-1!=0`. Finally, the existing entire cleared scalar inversion law
descends because its explicit clearing factor is nonzero at this parameter.

## Lean implementation

All modules below have prefix `GaloisForLFunctions.RHTower.ThetaCuspHawking`.

- `BMHeightLaplacian`: reusable actual height Laplacian, extracted from the
  existing `BMCuspCutoffMean` caller.
- `BMCuspFieldIntegral`: generalized native cusp-strip integration, used by
  the existing `BMCuspNativeSourcePair` caller.
- `BMCutoffPowerHeight`: actual smooth cutoff powers, full commutator, and
  both original endpoint germs.
- `BMCutoffPowerFlux`: differentiated Wronskian, endpoint values,
  integrability, and `cutoffPowerMoment_eq`.
- `BMScalarCutoffPeriodStrip`: full Fourier averaging and exact original
  measure transport into the two actual moments.
- `BMScalarCutoffBoundaryValue`: `scalarCutoffPeriod_eq_boundary_value`,
  `scalarCutoffPeriod_weyl`, and substitution of all three derived cutoff
  values into `continuedAngularSourceProjection`.
- [BMPhysicalAngularCutoffCalibration](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhysicalAngularCutoffCalibration.lean):
  original physical parameter, principal part, modular inversion, and
  `physicalScalar_cutoff_calibration`.

## Scope and remaining obstacle

This evaluates the cutoff contribution to the actual angular source integral.
The complete source also contains its native square-residual period
`J(q,u)`, which remains unevaluated. Its three source exponents are generally
different from the physical testing roots, so their bulk terms remain.
The nonzero calibration on one cutoff input does not decide the projection
of the original complete source.

The actual outgoing joint inverse, agreement with its original causal
overlap, full advanced/adjoint left residue, independent Hawking-clock
extinction, and RH remain open. Assigned scalar triple-product reporters
cannot replace the native residual integral: existing
`BMEisensteinScalarLandingNoGo` and
`BMEisensteinActualUnfoldedScalarNormalizationNoGo` already exhibit exact
normalization discrepancies for their specified constructions.

## Broader corpus evidence

Separate corpus-tool searches returned 1289 declarations in 78 modules for
`Fokas`, then 239 declarations in 21 modules for `Higgs`.
`FokasLenellsCauchyResolvent` constructs its normalized two-channel inverse;
`FokasLenellsAnalyticRH` realizes its Riemann--Hilbert boundary problem.
Neither inspected theorem identifies the BM source or outgoing domain.
`HiggsMechanism` supplies a selected-vacuum stabilizer interface;
`HiggsCausalOrbit` proves an exact quaternionic radial-orbit decomposition.
`CausalRayPolarityNonselection` proves that positive null outer-square data
and scalar weight alone do not select a causal ray. No transfer from these
constructions to the BM physical left pairing is assumed.

## Verification

Seven new leaves, totaling 606 lines and 24 public theorems, passed scratch
`lake env lean` checks. Both extracted helper callers were preserved and
audited in their updated form. All nine canonical modules passed individual
foreground `lake build <module>` audits without Lean warnings, reusing
existing dependency artifacts and producing exactly nine target oleans.
No full or umbrella build was run.

Scratch-only `#print axioms` checked exactly the 24 new public theorems and
the two changed callers. Each reported only `propext`, `Classical.choice`,
and `Quot.sound`. Nine installed sources and eighteen installed olean/ilean
artifacts were byte-verified against the canonical audit. The seven new
imports are wired into the RHTower umbrella. No numerical experiment or
computational certificate was used. The frontier map was not edited.
