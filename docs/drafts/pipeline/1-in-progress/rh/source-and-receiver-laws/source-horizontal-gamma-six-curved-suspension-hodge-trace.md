# Source-horizontal Gamma-six curved suspension and Julia determinant seam

- **ID:** `source-horizontal-gamma-six-curved-suspension-hodge-trace`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / THREE EXACT NO-GOS / FRANKENSTEIN SEAM / NOT RH
- **Source:** `rh-current-frontier-map.md`;
  `source-horizontal-gamma-six-paired-defect-gauss-hodge-curvature.md`;
  `HedenmalmThetaMobiusHyperbolicRapidity.lean`;
  `SourceFormationHarmonicMechanics.lean`;
  `HedenmalmThetaGammaSixWoldCarrier.lean`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixCurvedSuspensionHodgeTrace.lean`

## Result

Put

```text
delta+(a) = exp(a)-1,
delta-(a) = exp(-a)-1,
D(a)      = [[0,delta+(a)],[delta-(a),0]],
K(a)      = 2(cosh(a)-1) = -delta+(a)delta-(a).
```

Lean proves unconditionally

```text
D(a)^2 = -K(a) I,
det D(a) = K(a),
tr(D(a)^2) = -2K(a),
D(a)^2=0 <-> det D(a)=0 <-> a=0.
```

Thus forward and reflected Gamma-six cyclic defects form one literal curved odd suspension.  It is
an honest differential exactly at neutral horizontal grade.  Away from neutrality it is invertible
and has the explicit contracting homotopy `h(a)=-(2K(a))^-1 D(a)`.

## Heavy conjecture loop

### C0 -- cyclic trace annihilates curvature

**Conjecture.**  Put the two reflection orientations in opposite odd corners and use ordinary
cyclic trace to force their commutator curvature to vanish.

**Verdict: FALSIFIED EXACTLY.**  Ordinary trace of the split-leg commutator is zero for every
`a`, including every `K(a)>0`.  The two corner compressions retain `-K(a)` and `K(a)`, and graded
trace of the commutator retains `2K(a)`, but the uncompressed cyclic trace cancels them.

### C1 -- supertrace or Hodge transgression forces flatness

**Conjecture.**  Oddness of `D(a)` and the graded Hodge identity should make nonzero curvature
incompatible with a harmonic compression.

**Verdict: FALSIFIED MORE STRONGLY.**  `Str(D(a)^2)=0` for every `a`.  For every `a!=0`, `D(a)` is
contractible and the generic corpus Hodge-transgression theorem applies with harmonic projector
`P=0` to every observable.  Bare Hodge compression accepts the off-center curved sector.  Any use
of Hodge theory must establish `D^2=0` independently before compression.

### C2 -- determinant retains the missing coordinate

**Conjecture.**  Exterior determinant of the two odd corners survives trace cancellation and reads
the same positive current as Gamma-six boundary curvature.

**Verdict: PROVED.**  `det D(a)=K(a)`.  The ordinary curvature-trace energy
`-Re tr(D(a)^2)/2`, determinant, paired cyclic curvature, and the prime-clock Gauss energy are one
quantity.  Gauss Hodge mass is its exact Euler derivative with the existing residue coefficient.

### C3 -- P/R Julia geometry is only analogous

**Conjecture.**  The normalized Hedenmalm aperture may encode a related hyperbolic variable but not
the coefficient-exact Gamma-six grade.

**Verdict: FALSIFIED; STRONGER IDENTITY PROVED.**  Define the source aperture

```text
u(a)=(exp(2a)-1)/2.
```

Its P/R rapidity is exactly `a`.  If `G(a)` is the normalized Hardy overlap and `C(a)` the literal
Xi-Ward Cayley discrepancy, then

```text
C(a)=tanh(a),
G(a)=1/cosh(a),
Re(det D(a))*G(a)*(1+G(a)) = 2*C(a)^2.
```

This is division-free and every omitted gauge factor is strictly positive.  Consequently
determinant flatness and Julia saturation are the same pointwise condition on one source aperture.

### C4 -- conserved theta/Route-R current kills determinant curvature

**Conjecture.**  Transport the curved suspension to the Route-R hyperbolic source plane and use the
intrinsic theta current as an annihilating conservation law.

**Verdict: FALSIFIED EXACTLY.**  The theta current is constantly `-2` along the entire canonical
aperture curve, while `det D(a)` is nonzero exactly for `a!=0`.  Orbit-current conservation is
transverse-blind and cannot force Julia saturation.

### C5 -- source-formation completion supplies bilateral admission

**Conjecture.**  Newly formalized exponent-edge formation mechanics may automatically place both
cyclic orientations in one completed energy domain.

**Verdict: CLASSIFICATION PROVED; PRODUCER FALSIFIED.**  The squared forward boundary defect is
literally the first formation-edge energy at radial character `exp(a)`; the reflected defect is the
first energy at its reciprocal.  Full bilateral exponent-edge summability is equivalent to
`det D(a)=0`.  Source formation generates every labelled edge, but does not prove bilateral
completion.  Assuming that admission at every Xi class is the already classified RH-equivalent
receiver.

### C6 -- Xi root kernel transfers into the suspension

**Conjecture.**  The actual Hedenmalm theta source pencil is noninvertible at every Xi divisor;
transport its nonzero root class to the two-state suspension, contradicting off-center
contractibility.

**Verdict: OPEN COMPARISON, NOT PROVED.**  The corpus has the root line of the parameterized theta
pencil and a separate fixed supersymmetric Dirac for the closed weighted derivative.  It does not
have a coefficient-faithful similarity or unstabilized chain map from that root line to `D(a)`.
Ordinary stabilization is inadmissible: existing R/L work proves a stabilized complex can retain a
relative class while also retaining raw curvature.  The required map must preserve the two cyclic
corner coefficients, divisor multiplicity, and both reflection orientations, and must land in the
unstabilized `D(a)`-homology.

## Exact survivor and open producer

One object now welds five corpus organs:

```text
Gamma-six cyclic boundary
  = first bilateral exponent-edge formation block
  = curved odd suspension D(a)
  = positive-gauge Julia Cayley energy
  = determinant / ordinary curvature-trace energy
  -> Euler derivative = Gauss Hodge mass.
```

The surviving producer is correspondingly narrower:

> Construct a source-normal, coefficient-faithful comparison from the actual Xi theta-pencil root
> line (or the strict Rost--Schmid/Meyer source class) to the unstabilized curved suspension, proving
> that the transported nonzero divisor class is a `D(a)`-cycle.  Since `D(a)` is contractible for
> `a!=0`, such a comparison forces `D(a)^2=0`, hence Julia saturation and critical-line placement.

This is not supplied by determinant packaging, reflection exchange, invariant current,
supertrace, Hodge compression, source-edge generation, or stabilized homology.

## Formal capstones

- `sourceHorizontalGammaSixCurvedSuspension_sq`
- `sourceHorizontalGammaSixCurvedSuspension_contractible_of_ne_zero`
- `sourceHorizontalGammaSixCurvedSuspension_offCenter_hodgeTransgression`
- `det_sourceHorizontalGammaSixCurvedSuspension`
- `re_det_sourceHorizontalGammaSixCurvedSuspension_mul_hardyGauge_eq_cayleyEnergy`
- `sourceHorizontalGammaSix_thetaCurrent_constant_but_determinant_nonzero_iff`
- `sourceHorizontalGammaSix_bilateralFormationAdmission_iff_det_eq_zero`
- `gaussHodgeMassCurrent_eq_euler_gaussGammaSixSuspensionDeterminant`
- `sourceHorizontalGammaSixPhysicalSuspensionsFlat_iff_riemannHypothesis`

## Status

- [x] heavy conjecture/fail/pivot loop recorded;
- [x] exact curved suspension and contracting homotopy formalized;
- [x] trace, supertrace, Hodge, and invariant-current no-gos formalized;
- [x] P/R Julia, formation-edge, determinant, and Gauss-Hodge seams formalized;
- [ ] coefficient-faithful unstabilized theta-root/source-class comparison;
- [ ] source proof that the transported divisor class is a `D(a)`-cycle;
- [ ] RH.

No external novelty claim is made before a dedicated literature audit.  All Lean declarations are
unconditional; the terminal RH theorem is an equivalence, not a proof of its left-hand side.
