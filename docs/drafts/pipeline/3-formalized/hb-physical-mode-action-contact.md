# HB: reconstructed physical Einstein current and local QNM temporal residue

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source →
physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

This result identifies the mixed Einstein current of the reconstructed
physical projected response and transfers its temporal component to the
original fundamental QNMs. It does not prove RH.

## Objects and exact equations

Let x<0 be the original tortoise coordinate, R=-coth(x)>1, and
`lambda = physicalAngularParameter(r)^2-1/4`. The physical parameter is
`(rho_r-1)/2`. Let f be the complete physical projected response, F its complete
projected forcing, and g either original homogeneous radial mode. The angular
covector J is the actual coexact completed Eisenstein covector at this same
physical parameter. Set `N = sum_j J_j^2`; this is complex bilinear.

The reconstructed streams have radial coefficients Rf and Rg, time
frequencies w and -w, and angular covector J. Their complete coordinate
TwoJets are proved equal to actual derivatives of those fields. Their
original stream masters are respectively

```
-R^3 F J/(R^2-1),    0.
```

The equations follow from the actual physical response derivatives and the
proved angular equation of J. No angular eigen-equation or radial ODE is
added as a physical premise. On the original causal Green band the right
stream is almost everywhere the radius lift of the physical projection of
the actual causal transform.

The volume-weighted Einstein action current, evaluated at time zero, is

```
A^0 = [-2w(lambda-2)fg/(R^2-1) - w R^2 g F/(R^2-1)^2] N,
A^1 = [-(lambda-2)(g'f-gf') - C] N,
A^2 = A^3 = 0,
C = [Rg + R^2 g'/(R^2-1)] F.
```

Both contacts are fixed by the original Einstein current. The four-component
formula comes from actual Einstein boundary-current variations, not an
assigned scalar Wronskian. On every interior interval s≤t<0,

```
A^1(t)-A^1(s) = [-(lambda-2) integral_s^t gF - (C(t)-C(s))] N.
```

The complete F includes the residual angular period and all three cutoff
commutators.

## Local temporal QNM transfer

For the same source and target Xi copy, substituting the previously
identified continued physical field into the displayed A^0 defines
`continuedPhysicalTimeAction`. It equals the actual Einstein component on
the physical band. It is meromorphic for Im(w)≠0 and Re(w)>-2.

At either original fundamental frequency w0, the full projected F is
analytic. This follows from the proved source-rate noncollision and the
analyticity of each of the three principal corrections. The original left
radial mode is analytic there too. Thus the temporal source contact is
regular, and the derived residue is exactly

```
Res(A^0)(x,z) = -2 w0 (lambda-2) g(w0,x) Res(f)(x) N(z)/(R^2-1).
```

An analytic Laurent remainder is constructed after subtracting this
coefficient. Both original fundamental radial normalizations equal

```
Psi(x) = zeta^(w0/2) sqrt(1-zeta),  zeta=sech(x)^2.
```

Consequently the residue factors as

```
[-2 w0 (lambda-2)/(R^2-1)] Psi(x)^2 N(z)
  * [angularSource * fundamentalSourceMoment * clearedOnset / denominatorSlope].
```

The denominator slope is the previously proved original slope. The new
transfer proves that w0, lambda-2 and Psi(x) are nonzero. In particular,
nonzero original field residue and nonzero pointwise N imply nonzero local
Einstein temporal residue. Their nonvanishing is not assumed to hold after
angular or horizon integration.

## Lean modules

All declarations below belong to namespace `RHTower.D4BMPhysicalModeAction`.

- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModeActionReconstruction`:
  `radiusLift_derivatives`, `radial_mode_action`, `staticStreamJet_actual`,
  `radialStreamJet_actual`, `radial_stream_master`.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalModeAction`:
  `physicalModeAngularJet_operator`, `physicalProjectedStream_jet`,
  `physicalLeftModeStream_jet`, `physicalProjectedModeAction_value`,
  `physicalProjectedStream_master`, `physicalLeftModeStream_master`,
  `physicalProjectedStream_causal_origin`, `physicalProjectedModeAction_transport`.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalTimeActionContinuation`:
  `projectedSource_fundamental_analytic`,
  `continuedPhysicalTimeAction_eq_actual`, `continuedPhysicalTimeAction_meromorphic`,
  `continuedPhysicalTimeAction_residue`, `physicalTimeResidue_fundamental_value`,
  `physicalTimeResidue_ne_zero`, `continuedPhysicalTimeAction_laurent`.

Validation: all three source files pass individual foreground
`lake env lean /tmp/...lean` checks without warnings. All three leaves passed exact isolated `lake build <leaf>` audits, using
cached imports only: reconstruction 24 seconds, physical action 161 seconds,
temporal continuation 146 seconds. Each audit reported two jobs.
Completed leaves are wired into `GaloisForLFunctions.RHTower`; no umbrella
build is used. The formal lint gate passed; it reported only existing
large-file warnings.

## Remaining hard problem

The proof is local and concerns one reconstructed projected mixed sector.
It does not establish the full unprojected angular reconstruction, independent
SS/VV sectors, physical retarded/advanced Peierls pairing, integrated horizon
and cusp limits, or the all-multiplicity angular dual. The source angular
coefficient, radial moment and fixed onset still require nonvanishing or a
source-derived replacement that proves the full retained pairing survives.
Hawking-clock extinction remains open.

A concrete next target is the original radial finite part of Psi squared.
The candidate scalar integral is

```
I(w)=1/w-1/(2(w+1))
     -(1/2) integral_0^1 z^(w+1)/(1+sqrt(1-z))^2 dz,
```

with conjectured evaluation
`w(w+1)I(w)=Gamma(w+2)Gamma(3/2)/Gamma(w+3/2)` for nonreal w with Re(w)>-2.
The exact square-root remainder specifies the two horizon subtractions.
This candidate and interchange with the actual continued current are not
formal results in these modules. An angular dual must also be derived from
the original cusp pairing, including multiple Xi zeros; pointwise N≠0
cannot substitute for that integration.

Corpus searches used broad lexical, deep lemma, and method/source-argument
retrieval. Deep results were partial and candidate applicability was not
assumed. Every ingredient used in the new proofs was read in source and
checked in Lean. No numerical experiment was used.
