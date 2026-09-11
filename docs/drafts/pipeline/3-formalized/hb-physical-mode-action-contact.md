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

The contact identities passed their scratch check. The final source passes
its exact isolated leaf audit without warnings; its umbrella import is wired.
The formal lint gate passed for all six new leaves, reporting only existing
large-file warnings.

## Actual incoming pairing endpoint coefficients

Four further leaves pass warning-free foreground scratch checks and exact
leaf audits; their umbrella imports are wired:

- `HTGeometry.HypergeometricTaylorEndpointBounds`: arbitrary finite-order
  Gauss remainder from the actual coefficient majorant (6.8-second audit).
- `RHTower.ThetaCuspHawkingBMLaplaceHorizonTaylorBound`: uniform quadratic
  horizon Gauss expansion; actual analytic h1=gaussA*gaussB/gaussC; h1=-1/2
  at either fundamental root (90-second audit).
- `HTGeometry.QuadraticEndpointProducts`: explicit product-remainder bound
  and |1/(2sqrt(1-z))-1/2-z/4|<=2z^2 for 0<=z<=1/2 (4-second audit).
- `RHTower.ThetaCuspHawkingBMIncomingPairingEndpoint`: exact native radial
  density attachment and uniform second-order incoming pairing expansion
  (177-second audit).

For Q=G/h=A_b+d*z+O(z^2), the checked original density is

```
core=(G/h)*H^2/[2sqrt(1-z)],
z^(w-1)*core=G*h/[2z sqrt(1-z)],
core0=A_b/2,
core1=(h1+1/4)*A_b+d/2,
|core-core0-core1*z|<=C*(|A_b|+|d|+1)*z^2.
```

The density identity assumes only 0<z<1, including any zeros of h under
Lean's totalized division. The remainder bound holds on a derived common
frequency neighborhood away from connection zeros, for nonreal w with
Re(w)>-2 and w!=2s. It retains the possible connection pole in A_b; it does
not assert an unproved bound on A_b. The actual source slope d is analytic
through the connection zero. At a fundamental frequency the derived
linear coefficient is -A_b/4+d/2, retaining the analytic source term.

The new actual APIs are `incomingPairingFactor_uniform_second_bound`,
`incomingResponseSlope_analyticAt`, `incomingResponsePairingCore_density`,
and `incomingResponsePairingCore_uniform_second_bound`.
Every audit ran only its exact new leaf, with cached imports and no
dependency or umbrella builds. The formal lint gate passed with existing
large-file warnings. No numerical experiments were used.

## Restored actual incoming horizon integral

The exact source quotient split and its common analytic bounds now pass
Lean in `incomingSourcePrimitive_common_data`, an extension of
`ThetaCuspHawkingBMIncomingHorizonExpansion` (118-second exact audit):

```
Q(u,z)=A_b(u)+P(u,z),   P(u,z)=integral_0^z T(u,t)dt,
|P|<=M*z,              |P-d*z|<=C*z^2.
```

P is spatially continuous and pointwise analytic in frequency on one
derived neighborhood through the connection zero. The new general leaf
`HTGeometry.QuadraticEndpointMellin` proves analyticity and cutoff
restoration for a frequency-dependent kernel with a common quadratic
endpoint remainder (47-second exact audit).

Their native application is
`ThetaCuspHawkingBMIncomingPairingFinitePart` (35-second exact audit).
`incomingPairingFinitePart_horizon_restoration` gives one fixed 0<b<=1/2
and a frequency neighborhood on which the original integral obeys

```
lim_{e->0+} [integral_e^b G(u,z)*h(u,z)/[2z sqrt(1-z)] dz
  +(A_b(u)/2)*e^u/u
  +((h1(u)+1/4)*A_b(u)+d(u)/2)*e^(u+1)/(u+1)]
= A_b(u)*N_b(u)+J_b(u).
```

The literal N_b uses kernel M=H^2/[2sqrt(1-z)] and coefficients
1/2, h1+1/4. The literal J_b uses P*M and coefficients 0, d/2.
N_b, J_b, and P(u,b) are analytic through the connection zero, with
all majorants derived from the original source and Gauss family.
The cutoff identity holds away from the connection zero, retaining its
possible pole in A_b. Physical residue extraction through this horizon restoration is now
proved below. The opposite-mode logarithmic channel is also proved below;
full source/contact assembly and outer endpoint restoration remain open.

All new leaves passed warning-free scratch checks and exact leaf audits;
umbrella imports are wired. An import collision exposed by the native
check was repaired by renaming the helper in
`NormalizedFirstEndpointMellin` to `normalizedMellinRemainder_norm_le`
and its single local use (18-second exact audit). The earlier
`FirstEndpointMellinLimit` API is unchanged. No numerical data were used.

## Physical residue after horizon restoration

`ThetaCuspHawkingBMPhysicalIncomingPairingResidue` passes its exact leaf
audit without warnings (29 seconds, two jobs, cached imports). Its import
is wired. For every Xi copy q, source branch and fundamental side, define
w0=physicalFundamentalFrequency, s=physicalRate, chi=physicalRadialFrequency
and K=reducedGreenGradient(chi,s,1). The proved source amplitude is

```
C_src=fundamentalSourceMoment(w0,s,a)*continuedOnset(s,w0)
      /[-connectionSimpleSlope(w0,chi,side)]
     =fundamentalSourceMoment(w0,s,a)*clearedOnset(s,w0)
      /physicalFundamentalDenominatorSlope(q,branch,side).
```

The equality is `physicalIncomingPoleAmplitude_eq_cleared`.
`physicalIncomingQuotient_residue` derives lim_(u->w0)(u-w0)*G(u,b)/h(u,b)
=C_src at every interior b. Its proof uses the analytic original quotient
numerator, nonvanishing fundamental mode, exact fixed source-moment
identity, and the derived simple connection zero.

`physicalIncomingPairing_residue_and_restoration` gives one common b and
frequency neighborhood with both the original two-counterterm cutoff
limit above and

```
lim_(u->w0) (u-w0)*incomingPairingFinitePart(s,chi,a,1,K,b,u)
  = C_src*incomingNormFinitePart(chi,b,w0).
```

The finite part is taken before this frequency limit. The theorem supplies
all frequency-strip, source-rate separation and analytic-primitive facts
from the corpus; no residue or interchange premise is supplied. This
closes the incoming horizon block. The opposite logarithmic block is
regular by the theorem below. Outer interval restoration, full physical
current assembly and source-moment/onset nonvanishing remain open.

## Logarithmic endpoint and opposite Gauss product

`HTGeometry.LogarithmicEndpointFinitePart` proves the actual logarithmic
cutoff identity and limit for a frequency-dependent kernel F with a common
linear endpoint remainder F(w,z)-a0(w). Its restored integral is

```
a0(w)*log(b) + integral_0^b (F(w,z)-a0(w))/z dz.
```

The remainder is integrable, bounded by C*b, tends to zero with b, and is
analytic in frequency under the proved common domination conditions.
Scratch and exact leaf audit passed without warnings (6.3 seconds,
two jobs); source, artifacts, and umbrella import are installed.

`ThetaCuspHawkingBMOppositePairingFactor` derives |V-1/2|<=C*z and |V|<=M
for the actual opposite Gauss product on one frequency ball and 0<=z<=1/2.
It also proves frequency analyticity, spatial continuity and the exact
opposite radial-density identity wherever the incoming mode is nonzero.
Scratch and exact leaf audit passed without warnings (338 seconds,
two jobs). Its six direct imports use cached dependencies; its source,
artifacts and umbrella import are installed.

`ThetaCuspHawkingBMOppositePairingFinitePart` now derives the original
logarithmic cutoff limit and analyticity of L_b, K_b and P_b on one common
source-derived cutoff. The actual coefficient is connection/(2w), and
its counterterm is connection/(2w)*A_b*log(e)/2. Scratch and exact leaf
audit passed without warnings (87 seconds, two jobs, cached imports).
Source, artifacts and umbrella import are installed.

`ThetaCuspHawkingBMPhysicalOppositePairingRegularity` proves an explicit
analytic extension of the actual restored opposite pairing. Write C for
the connection, A_b for the incoming endpoint coefficient, P_b for its
source primitive, L_b for the opposite norm finite part and K_b for its
source-pairing finite part. The actual cleared source numerator B_b obeys
C*A_b=-B_b-C*P_b on the original punctured germ. The extension is

```
E_b(w) = [(-B_b(w)-C(w)*P_b(w))*L_b(w)+C(w)*K_b(w)]/(2*w).
```

At each physical fundamental frequency w0, the exact value is

```
E_b(w0) = -fundamentalSourceMoment(w0,s,a)*continuedOnset(s,w0)
            *oppositeNormFinitePart(chi,b,w0)/(2*w0).
```

`physicalOppositePairing_analytic_restoration` derives one common cutoff
with analyticity of E_b, convergence of the actual restored pairing to
E_b(w0), zero pole residue, and the original logarithmic cutoff limit to
E_b(u) throughout a punctured frequency neighborhood. Nonzero observation
mode, isolated connection zero and source-rate separation are derived for
the physical parameters. No interchange or regularity premise is supplied.
The totalized pairing's assigned point value is not asserted analytic.

The exact leaf audit passed without warnings (107 seconds, two jobs,
cached imports). Source, artifacts and umbrella import are installed.
Denominator algebra uses a small scalar lemma rather than expanded Green
integrals; no heartbeat or other resource limit was raised.

## Independent-frequency outer majorant

`ThetaCuspHawkingBMReducedGreenUniformBound` proves the actual cleared
reduced response's first spatial jet, frequency analyticity of that jet,
and its forced ODE away from the original denominator zeros. The response
is the existing `clearedReducedGreen`, retaining both source moments and
the explicit gradient lift. Its forcing is

```
-connection(w,chi)*reducedCoefficient(s,w,a,clearedOnset(s,w),t).
```

The corpus's compact source-family bound and symmetric second-order ODE
estimate yield `clearedReducedGreen_compact_bound`: for any compact
frequency set in the nonreal strip Re(w)>-2, one constant C satisfies

```
|clearedReducedGreen(w,chi,s,a,t)| <= C*exp(-|Re(w)|*t)
```

for every interior frequency and every t<0. Continuity of the explicit
numerator extends the estimate through source and connection zeros.
The angular parameter is independent; it is not restricted to the three
principal cusp powers.

`physicalClearedReducedGreen_outer_uniform_bound` derives a frequency ball
and a constant majorant for each Xi copy, branch, side, amplitude and
finite outer interval T<=t<0, including the physical resonance. All ODE,
forcing, initial-value and limit inputs are supplied by actual source
theorems. Scratch and exact leaf audit passed without warnings (67 seconds,
two jobs, 4,326 cached project imports). Source, artifacts and umbrella
import are installed; resource limits are unchanged.

## Original outer pairing after integration

`ThetaCuspHawkingBMReducedOuterPairing` derives a common bound for the
original normalizable left mode through its outer endpoint and on each
finite tortoise interval. Spatial continuity of the undivided response
uses the actual moving-endpoint derivatives of both source moments.
The resulting product density is absolutely integrable, and its integral

```
R_T(w) = integral_(T,0) clearedReducedGreen(w,chi,s,a,t)*n(w,t) dt
```

is analytic throughout the nonreal strip Re(w)>-2, including source and
connection zeros. Every domination and continuity input is derived.

The leaf identifies this analytic function with D(w)*Q_T(w), where
`D(w)=-(w-2*s)*connection(w,chi)` and Q_T is the original outer integral of
`continuedReducedGreen(w,chi,s,a,1,t)*n(w,t)`. Its theorem
`physicalReducedOuterPairing_residue` proves

```
lim_(w->w0) (w-w0)*Q_T(w)
  = [fundamentalSourceMoment(w0,s,a)*clearedOnset(s,w0)
       *integral_(T,0) n(w0,t)^2 dt]
      /physicalFundamentalDenominatorSlope(q,branch,side).
```

Outer integration precedes this frequency limit. The reduced response
retains its explicit gradient lift, and the slope is the original derived
nonzero denominator slope. Scratch and exact leaf audit passed without
warnings (34 seconds, two jobs, 4,332 cached project imports). Source,
artifacts and umbrella import are installed. Scalar cancellation uses
direct multiplication/division identities; resource limits are unchanged.

The fundamental norm is now joined at the common coordinate cutoff by
`D4BMFundamentalNorm.physicalFundamentalNorm_join` in
`ThetaCuspHawkingBMFundamentalNormJoin`. For every physical fundamental
frequency w0 and T<0, with b=horizonCoordinate(T),

```
incomingNormFinitePart(chi,b,w0) + integral_(T,0) n(w0,t)^2 dt
  = D4BMFundamentalNorm.normFinitePart(w0).
```

The proof derives the kernel sqrt(1-z)/2 and subtraction coefficients
1/2,-1/4 from the original Gauss mode, then applies the exact quadratic
Mellin cutoff identity and original coordinate substitution. It assigns
no independent finite-part normalization. Scratch and exact leaf audit
passed without warnings (28 seconds, two jobs, 4,415 cached project
imports); source, five artifacts and umbrella import are installed.
Resource limits are unchanged.

Assembly of the complete source/contact current remains open. The norm
identity does not prove source-moment or onset nonvanishing.

## Joined regular branch and outer residue

`ThetaCuspHawkingBMRegularOuterPairing` proves analyticity of the actual
normalizable-mode horizon coefficient from its interior Wronskian. It
constructs a tortoise cutoff matching the restored incoming cutoff, then
combines the incoming residue with the original outer-integral residue:

```
lim_(w->w0) (w-w0)*[Aplus(w)*incomingPairingFinitePart(w)+Q_T(w)]
  = physicalIncomingPoleAmplitude(q,branch,side,a)*normFinitePart(w0).
```

The original Wronskian normalization gives Aplus(w0)=1. The theorem
`physicalRegularOuterPairing_residue_and_restoration` also proves that the
positive-cutoff expression, with both derived incoming counterterms and
the original outer integral, tends to this joined pairing before taking
the frequency residue. It supplies its cutoff and frequency ball without
additional premises. Scratch and exact leaf audit passed without warnings
(37 seconds, two jobs, 4,419 cached project imports); source, five
artifacts and umbrella import are installed. No heartbeat or other
resource limits were raised.

This regular-branch result is extended below to include the opposite
horizon branch at the same cutoff. The inner explicit lift and complete
four-channel, two-contact physical current still require assembly.

## Both normalizable horizon branches at one cutoff

The incoming and opposite restoration theorems now hold for every
sufficiently small positive cutoff on one frequency ball. Their original
signatures remain corollaries. Re-centering the endpoint amplitude uses
the exact source identity Q(z)=Q(b)-P(b)+P(z). Both strengthened leaves
passed scratch checks and exact audits: incoming 124 seconds/4,337 cached
project imports, opposite 9.3 seconds/4,335; each audit ran two jobs.

`ThetaCuspHawkingBMNormalizableHorizonPairing` proves the exact original
positive-cutoff decomposition, deriving spatial integrability from the
actual continued-response and mode jets. The single normalizable integral
retains both power counterterms and the logarithmic counterterm. Scratch
and exact leaf audit passed without warnings (100 seconds, two jobs,
4,341 cached project imports).

`ThetaCuspHawkingBMPhysicalNormalizablePairing` constructs a shared
cutoff b=horizonCoordinate(T) and frequency ball. Its theorem
`physicalNormalizableOuterPairing_residue_and_restoration` proves both
restoration of the single original normalizable horizon integral and

```
lim_(w->w0) (w-w0)*[Aplus(w)*incomingPairingFinitePart(w)
                    +oppositePairingFinitePart(w)+Q_T(w)]
  = physicalIncomingPoleAmplitude(q,branch,side,a)*normFinitePart(w0).
```

The opposite block's analytic extension and zero residue are proved at
this same b. The incoming amplitude, fixed onset and connection slope
retain their source-derived normalization. Scratch and exact leaf audit
passed without warnings (10 seconds, two jobs, 4,425 cached project
imports). All four updated/new leaves have installed sources and
artifacts and umbrella imports; no umbrella or dependency rebuild ran.
No heartbeat or other resource limit was raised.

## Remaining hard problem

The completed admission now includes the actual forced response paired
with both normalizable horizon branches and the original outer reduced
response. The inner explicit lift must still be restored and combined
with this pairing, followed by all four source channels and both Einstein
contact terms. Residue extraction for the complete continued current
remains unproved. The
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

Latest repository lint exits with eight unreachable modules outside these
edits:

- `RHTower.ThetaCuspHawkingBMHorizonCoordinateJets`
- `RHTower.ThetaCuspHawkingBMPrincipalChannelHorizonJet`
- `RHTower.ThetaCuspHawkingBMSelfChannelHorizonJet`
- `RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonJet`
- `HTGeometry.AnalyticJetGerm`
- `HTGeometry.ElementaryHorizonJets`
- `HTGeometry.SecondEndpointMellinLaurentInterchange`
- `HTGeometry.UniformSecondOrderJet`

Both strengthened restoration leaves and both new normalizable-pairing
leaves passed exact audits and are reachable from their umbrella. The
global lint gate is not passed. Unrelated pending modules were not changed
or rebuilt. Frontier map and universal STATUS remain untouched.
