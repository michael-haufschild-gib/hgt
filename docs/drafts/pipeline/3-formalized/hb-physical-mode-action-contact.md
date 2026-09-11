# HB: physical Einstein current, QNM residue, and original radial finite part

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

## Closed original radial finite part

Set z=sech(x)^2 and u=-tanh(x), so z'=2uz and sqrt(1-z)=u
for x<0. The original fundamental mode is Psi_w=z^(w/2)sqrt(1-z).
Its bilinear square therefore has the exact finite-interval identity

```
integral_L^0 Psi_w(x)^2 dx
  = (1/2) integral_{z(L)}^1 z^(w-1) sqrt(1-z) dz,  L<0.
```

The exact endpoint decomposition is

```
sqrt(1-z)=1-z/2-z^2/[2(1+sqrt(1-z))^2].
I(w)=1/w-1/[2(w+1)]
     -(1/2) integral_0^1 z^(w+1)/(1+sqrt(1-z))^2 dz.
```

For Re(w)>-2 and w different from 0,-1, Lean proves the actual cutoff limit

```
lim_{L -> -infinity} [integral_L^0 Psi_w(x)^2 dx
  + z(L)^w/(2w) - z(L)^(w+1)/(4(w+1))] = I(w)/2.
```

The remainder has an explicit uniform O(z) bound after the first quotient,
which gives an analytic cleared finite part on Re(w)>-2. In Re(w)>0 the
restored integral equals the ordinary beta integral. Analytic continuation
of the cleared sides gives

```
w(w+1) I(w)=Gamma(w+2) Gamma(3/2)/Gamma(w+3/2).
```

At every nonreal w in this strip,

```
I(w)/2=Gamma(w) Gamma(3/2)/[2 Gamma(w+3/2)] != 0.
```

Both original Xi fundamental frequencies satisfy these frequency conditions
by the existing corpus theorem, without a new strip or simplicity premise.
The nonzero radial factor is now derived from the original cutoff integral.

For the actual temporal Einstein Laurent coefficient define

```
C = angularSource * fundamentalSourceMoment * clearedOnset / denominatorSlope,
K(z_angular) = -2 w0 (lambda-2) C N(z_angular).
```

The original radius derivative is R'=R^2-1. Lean proves

```
(R(x)^2-1) Res(A^0)(x,z_angular) = K(z_angular) Psi_w0(x)^2.
```

Its finite-interval integral and two-counterterm horizon limit are proved:

```
FP integral_{-infinity}^0 (R^2-1) Res(A^0) dx
  = K * Gamma(w0) Gamma(3/2)/[2 Gamma(w0+3/2)].
```

This result integrates the already derived Laurent coefficient. It does
not interchange the frequency-residue limit with horizon exhaustion of the
whole continued current. Angular integration, its original measure and
cusp terms, and survival of C remain open. The formal equality to zero is
exactly equivalent to K=0; the radial finite part adds no cancellation.

New modules:

- `GaloisForLFunctions.HTGeometry.HalfOrderBetaFinitePart`, namespace
  `GaloisForLFunctions.HTGeometry.HalfOrderBeta`:
  `finitePart_cutoff_tendsto`, `cleared_eq_gamma`, `finitePart_eq_gamma`,
  `finitePart_ne_zero`.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialNorm`:
  namespace `RHTower.D4BMFundamentalNorm` supplies `mode_square_intervalIntegrable`, `mode_square_integral`,
  `mode_square_cutoff_tendsto`, `normFinitePart_eq_gamma`,
  `normFinitePart_ne_zero`; namespace `RHTower.D4BMPhysicalModeAction`
  supplies `physicalTimeResidue_radial_density`,
  `physicalTimeResidue_radial_integral`, `physicalTimeResidue_radial_cutoff_tendsto`,
  `physicalRadialResidueFinitePart_eq_gamma`,
  `physicalRadialResidueFinitePart_eq_zero_iff`.

Validation of both new leaves: warning-free foreground scratch checks;
exact isolated leaf audits passed with two jobs each (Beta finite part
93 seconds; physical radial norm 136 seconds), using cached imports only.
Both imports are wired into their respective umbrellas. The formal lint
gate passed with only existing large-file warnings.

## Local action Lean modules

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

## Uniform horizon expansion of the original Green block

For the actual continued Green response G and incoming mode h=z^(w/2)H,
the original Wronskian proves (G/h)'=T, with

```
T = firstEndpointMellin(H*sourceRemainder) * continuedOnset
      / [2 z sqrt(1-z) h^2].
d(w) = sourceRemainder(w,0) * continuedOnset(w) / [2(w+1)].
```

The connection denominator cancels in this derivative. A normalized Mellin
estimate and a derived common bound 1/2<=|H|<=3/2 give |T-d|<=Cz uniformly
in frequency near nonreal w with Re(w)>-2 and w!=2s. Both actual Xi
fundamental frequencies satisfy these conditions by existing theorems.

For a derived positive b, define A_b=G(w,b)/h(w,b)-integral_0^b T(w,z)dz.
Lean proves the uniform quadratic remainder

```
|G(w,z)/h(w,z)-A_b(w)-d(w)z| <= C z^2,  0<z<=b,
```

on the frequency neighborhood away from connection zeros. The actual
source integral reaches the horizon analytically, by the corpus's
Cauchy-dominated integral theorem. Thus A_b is meromorphic. These are
statements about the original Green blocks; assembly with the explicit
gradient lift, all principal corrections and the full current remains open.

Checked and audited leaves:

- `GaloisForLFunctions.HTGeometry.NormalizedFirstEndpointMellin`:
  `normalizedFirstEndpointMellin_uniform_bound`, `normalizedFirstEndpointMellin_tendsto`.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingSourceTransport`:
  `continuedResponse_div_horizon_hasDerivAt`, `incomingSourceTransport_analyticAt`,
  `incomingSourceTransport_tendsto_horizon`, plus both physical specializations.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonGaussBound`:
  `horizonGauss_uniform_first_bound`, `horizonGauss_uniform_nonzero`.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingSourceBound`:
  `incomingSourceTransport_uniform_first_bound`,
  `physical_fundamental_incomingSourceTransport_uniform_bound`.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingHorizonExpansion`:
  `continuedResponse_horizon_quadratic_expansion`, `incomingResponseEndpoint_meromorphic`.

All five passed warning-free foreground scratch checks and exact isolated
leaf audits using cached imports. Their umbrella imports are wired.

## Exact horizon factor in the full temporal contact

The actual reduced source polynomial factors as
`reducedPolynomial(s,w,v)=(1-v^2)*reducedHorizonQuotient(s,w,v)`.
Its quotient is explicit, with denominator 1+v, which is positive in the
original radial chart. Together with the exact z factors in all three
cutoff coefficients, this proves F=z F_hor for the complete angular source
integral. All four source channels remain present.

The original radius identity R^2 z=R^2-1 then yields

```
(R^2-1) A^0 = [-2w(lambda-2)fg-w g F_hor] N.
```

Thus the temporal source contact's additional explicit horizon denominator
cancels. `ThetaCuspHawkingBMTemporalContactHorizonFactor` supplies
`continuedAngularSourceProjection_horizon_factor`,
`radius_sq_mul_horizonCoordinate`, and
`continuedPhysicalTimeAction_radial_density`. The remaining endpoint
analysis must use this complete source quotient.

## Remaining hard problem

The completed horizon integral concerns the temporal Laurent coefficient of
one reconstructed projected mixed sector. Residue extraction must still be
interchanged with horizon exhaustion of the full continued current. The
full unprojected angular reconstruction, independent SS/VV sectors, original
retarded/advanced Peierls pairing and all-multiplicity angular dual remain
open. The source angular coefficient, radial source moment and fixed onset
still require nonvanishing or a source-derived construction proving that
the complete retained pairing survives. Hawking-clock extinction and RH
remain unproved.

The active angular conjecture derives a divided-difference jet matrix from
the literal cusp Green boundary identity. Its proposed antidiagonal uses
the first nonzero incoming cusp coefficient at the actual Xi multiplicity.
The detailed boundary calculation and unproved full-field identification
are recorded on the working card. No invertible physical jet pairing is
assumed by the completed radial proof.

Corpus searches used broad lexical, deep lemma, and method/source-argument
retrieval, including endpoint beta finite part, coordinate substitution,
biorthogonal, confluent, MaassSelberg, and repeated-zero jet Gram mechanisms.
Results were partial; candidate applicability was not assumed. Every
ingredient used in the new Lean proofs was read in source and checked in
Lean. No numerical experiment was used.
