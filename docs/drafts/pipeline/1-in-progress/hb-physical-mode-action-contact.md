# HB: actual projected Einstein current and QNM pairing

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source →
physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
RH remains unproved. The frontier map is read-only.

## Actual RH closing obligation

The active target is the literal augmented Einstein causal pairing and its
fixed-clock extinction. The overtone source-moment argument below is an
unproved auxiliary approach; completing it alone does not close this target.

`ThetaCuspHawkingBMSecondHarmonicPeierlsPolarizedLanding` requires an actual
source-pairing incidence in
`d4BMXiSecondHarmonicCokernelCausalCut_eq_PeierlsPolarizedCandidate`.
`ThetaCuspHawkingBMSourceFixedPeierlsReflectionRigidity` proves RH from this
incidence on source families exchanged by reflection in one cyclic/skew
Peierls theory. The packet model in
`ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence` has algebraic
incidence, but its required source covariance is itself an RH equivalent.
It does not discharge the literal metric's physical incidence.

A checked amplitude reduction targets this missing physical pairing. Put
`Q(p)=B(p,p)/2` and `Omega(f,g)=pairing(Delta(f),g)`. Under the existing
cyclicity and Peierls-skewness assumptions, the complete cubic cut is
`C(p,m)=2*Omega(Q(p),Q(m))`. Its double polarization is

```
C(pS+pV,mS+mV)-C(pS,mS+mV)-C(pV,mS+mV)
  -C(pS+pV,mS)+C(pS,mS)+C(pV,mS)
  -C(pS+pV,mV)+C(pS,mV)+C(pV,mV)
  = 2*Omega(B(pS,pV),B(mS,mV)).
```

This identity passed `lake env lean` in scratch at default resource limits
on 2026-09-12. Its proof expands the existing polarized-cut theorem by
bilinearity and symmetry of `B`. It is conditional Peierls algebra, not a
new unconditional physical theorem, and was not installed as a Lean leaf.
The selected quartic coefficient depends only on the mixed radiative
sources once physical cyclicity/skewness has been established. This does
not remove those physical assumptions or prove extinction.

The raw-source attachment is essential. The all-component theorem
`D4BMQuadraticMixedSource.einstein_component` states
`B(S,V)+L(k)=T`, where `k` is the explicit ingoing correction and `T` is
the constructed mixed tensor. Thus its source pairing must retain

```
Omega(Bplus,Bminus) = Omega(Tplus,Tminus)
  -Omega(L(kplus),Tminus)-Omega(Tplus,L(kminus))
  +Omega(L(kplus),L(kminus)).
```

The next physical incidence calculation must evaluate this entire
expression using the original retarded/advanced responses and the four
components of `D4BMMixedActionCurrent.stream_complete_action_current`,
including the correction's horizon/onset traces. No theorem presently
identifies it with the RH-detecting BM boundary concomitant. Nor is its
fixed-Hawking-clock extinction proved. These are the closing obligations;
the displayed algebraic reductions do not settle them.

## Incoming correction and its significance for the full chain

The incoming temporal correction is formalized in
`ThetaCuspHawkingBMCorrectionTemporalRestoration`. Scratch verification and
the exact leaf audit passed at default resource limits; the leaf is wired
into `RHTower` without an umbrella build. The starting points are the
original mixed correction jet, the
complete Einstein action current, the literal source amplitude and the
existing quadratic endpoint Mellin theorem.

Write `s=D4BMModularCore.physicalRate q branch`, `kappa=s*(s+1)/2`,
`r=-coth(x)`, `u=1/r` and `z=1-u^2`. The original onset amplitude is

```
A(w,x)=exp(w*x)*(1+u)^(2*s)*a^2*continuedOnset(s,w).
c(r)=kappa*A(w,tortoise(r))*(r^2-1)/r^3.
c'(r)-2*c(r)/r
  =kappa*A*((w-2*s)/r^3-3/r^2+(5+2*s)/r^4).
```

For the correction angular covector `J` and an independent left covector
`K`, the exact temporal Einstein density is
`w*d/(r^2-1)*(c'-2*c/r)*sum(J_j*K_j)`. The original correction's metric and
every first derivative are identified with this separated representation.
The covectors are not identified with each other. At the original
frequency `w=2*s`, the reduced derivative is
`kappa*B^2*((2*s+5)/r^4-3/r^2)`.

For the incoming left mode, the original radial Jacobian gives
`z^(w-1)*H(w,z)`, where

```
H = w*kappa*angular/2 * amplitudeProfile(s,a,continuedOnset(s),w,z)
    * gaussProfile(q,w,z)
    * ((w-2*s)*sqrt(1-z)-3+(5+2*s)*(1-z)).
```

The common-cutoff integral is restored with both terms
`c0(w)*e^w/w+c1(w)*e^(w+1)/(w+1)`. Its finite part is analytic at every
physical fundamental QNM, hence has zero pole residue. Its finite value
is retained. `incoming_corrected_residue` proves that subtracting this
restored correction preserves exactly the original incoming temporal
pole coefficient `FP(clearedDensityProfile)(w0)/denominatorSlope`.

The resulting no-go is specific: this incoming temporal contribution
cannot remove an already nonzero pole. Its positive content is exact
coefficient preservation, with the full restored correction still
present. This is not a proof that the full raw-source Peierls pairing is
unchanged. Opposite-horizon, radial, angular and outer contributions, and
the causal inverse's treatment of the correction, still need evaluation.

The full-chain implications determine the next conjectures, rather than
treating this component as the sole path to RH:

- `physicalSelfSourceCoefficient_zero_iff_xi` independently identifies
  angular-source cancellation with zeros at `5*rho/2-1`, `rho/2`, or
  `3*rho/2`. A regular correction does not exclude these incidences or
  radial source cancellation. A candidate replacement is detection by a
  family of original adjoint channels; joint detection must be proved
  without replacing the source.
- `physicalPrimitiveCurrent_balance` identifies integrated complete
  source work with the retained final-time physical primitive current.
  `retardedPulse_late_history` identifies the entire late onset-pulse
  response with its original initial-history strip. Thus the fixed-clock
  conjecture must estimate the retained response/current in the original
  observable. Vanishing of the shifted source alone does not give that
  estimate.
- `d4BMXiSourceFixedPeierls_global_BM_incidence_forces_rh` supplies another
  closing mechanism: actual oriented incidence and source exchange in
  one cyclic/skew theory force RH. The candidate bridge from the native
  physical Green balance to the joined Einstein Peierls action must
  retain its original source, pairing, conjugation and boundary terms.
  The abstract reciprocal half-jump construction supplies none of those
  physical identifications.

The literal source-exchange conjecture is now proved for independent,
unchanged scalar/vector amplitudes in
`ThetaCuspHawkingBMLiteralSourceReflection.lean`. The complete field and
every nonlinear Einstein-source coefficient exchange under functional-
equation reflection. Matching the RH candidate's normalized amplitudes
and physical pairing remains an obligation; the source identity alone
does not establish that incidence.

These are unproved closing mechanisms. The new correction theorem does
not prove angular coupling, full physical incidence, extinction or RH.

## Literal source reflection and consequences for closure

**Status:** paper proof closed; scratch checked with default Lean limits;
exact new leaf audit passed. The leaf is imported by `RHTower.lean`;
no umbrella build was run.

The successful conjecture is a field identity, rather than an inference
from an integrated Eisenstein vertex. For every positive integer `n`,
the original arithmetic coefficient obeys

```
a_u(n) = n^u * sum_(d|n) d^(-2u) = a_(-u)(n).
```

Divisor complement `d -> n/d` proves this equality term by term after
reindexing the finite sum. The corpus's `modifiedBesselKOrder_neg` then
preserves every signed Fourier mode and hence the complete infinite
zero-word tail. At nonreal `u`, the completed functional equation
exchanges `Lambda(2u)` with `Lambda(1+2u)` under `u -> -u`, simultaneously
exchanging their Weyl powers. Thus the full literal scalar satisfies
`scalar(-u)=scalar(u)` at every coordinate. Its actual coexact covector
and the complete metric reconstruction inherit the identity.

At each multiplicity-labelled Xi occurrence, put `u=rho-1/2` and use the
original fundamental rate `s=D4BMModularCore.physicalRate(q,b)`. The
metric frequency is `omega=I*s`, since the temporal factor is
`exp(-I*omega*t)`. The new `physicalPerturbation_eq_qnm` verifies both
frequency conversions against the original plus/minus QNM definitions;
`physicalPerturbation_first_source_zero` closes their linear Einstein
equations using the existing literal source theorem. Reflection gives

```
u(reflect(q)) = -u(q)
s(reflect(q),b) = s(q,!b)
h(reflect(q),b,aS,aV) = h(q,!b,aS,aV).
```

`physicalSource_reflect` proves equality of the actual full Einstein
source as a function of perturbation amplitude. Consequently
`physicalSource_coefficient_reflect` covers every derivative order,
including the original quadratic and cubic coefficients. These Xi
identities have no supplied symmetry, regularity or field-equation
premises. The amplitudes `aS` and `aV` remain independent.

**Effect on the complete RH chain:** source exchange is available for
the concrete on-shell metric family. Taking its two branches as `p,m`
supplies the exchange identities in the existing cyclic/skew Peierls
receiver at fixed amplitudes. The remaining construction must match
those fields, the actual source bilinear map, the causal inverse and
the normalized BM candidate in one physical pairing, with every
correction and boundary term retained. Neither an abstract reciprocal
half-jump nor an injective finite channel map makes that identification.
Source-coupling nonvanishing and fixed-clock extinction remain open.

The broad helicity search also found `collisionHelicity_reconstruct`
and `angularCoefficient_collisionHelicityPlus/Minus` in
`PolyatomicAngularHelicity.lean` (namespace
`RHTower.D4BMQuadraticAngularSource`). They give exact reconstruction
and factorization of the original quadratic angular tensor. This is a
concrete joint-detection candidate when one scalar angular projection
vanishes: prove the physical adjoint channel family detects these
components of the same source. Pointwise tensor reconstruction does
not itself prove a nonzero global left-QNM overlap.

Broad/deep/method retrieval also located
`SelbergModularCurrentGreen.current_green_identity`, retaining side,
top and curved-arc fluxes. It is a candidate integration mechanism for
the original current, not a ready-made Einstein reciprocity theorem.
The broad literature search found a related methodological example in
[Khankhoje–Kundu, arXiv:2606.14486, §III](https://arxiv.org/html/2606.14486v1):
full reaction integrals restore reciprocity missed by a reduced
scattering description. Its electromagnetic result is not imported
as a theorem about this gravitational source.

Keep the source's `center(q)` distinct from the original left probe's
`physicalAngularParameter(q)=(rho-1)/2`, and the fundamental rate above
distinct from the doubled rate in `D4BMCuspProjection`.

The next physical-pairing conjecture has a specific source in the corpus:
`EinsteinActionBoundary.densityPath_first_variation` gives the original
Einstein--Hilbert variation as minus the volume-weighted raised Einstein
residual plus its complete connection-current divergence. Differentiate
twice in independent on-shell directions, using the same volume branch.
The candidate identity is that the cyclicity defect
`<x,B(y,z)> - <z,B(x,y)>` equals minus the boundary divergence of the
`y`-variation of the original symplectic current of `x,z`. With the
corpus's relative-density convention, that variation must differentiate

```
volumeRatio J.metric Y.metric 0 0 t *
  actionSymplectic (affine J Y t) X Z a
```

rather than `actionSymplectic` alone. This is an unformalized conjecture
about the actual current; no global cyclicity is claimed. The existing
`CubicSource.pairedSource_cubic` separately exhibits the varying-test
weight multiplying the complete quadratic residual. These are concrete
terms to track when joining the source action and the boundary pairing.
If the resulting boundary flux cancels in the original common-cutoff
limit, it supplies the physical cyclicity premise. If it survives, its
exact value belongs in the full action incidence and in the fixed-clock
observable. Either outcome changes the whole closing argument.

## Closed local action attachment

The local action attachment uses three checked and audited leaves:

- `ThetaCuspHawkingBMModeActionReconstruction`: actual two-jets of separated
  fields, original radius reconstruction, full mixed Einstein current.
- `ThetaCuspHawkingBMPhysicalModeAction`: actual causal projection, original
  coexact Eisenstein covector, homogeneous original left stream, complete
  forced right stream, finite-interval Einstein flux including both contacts.
- `ThetaCuspHawkingBMPhysicalTimeActionContinuation`: actual temporal current
  continuation, exact fundamental residue, analytic Laurent remainder and
  transfer of local field-residue nonvanishing.

At an interior original tortoise point x<0 set R=-coth(x),
lambda=u^2-1/4, u=physicalAngularParameter(r). Let f be the complete physical
projected response, g either original radial mode, and F the complete projected
source. All three cutoff corrections remain in F. Reconstruct the stream
coefficients as Rf and Rg with time frequencies w and -w, and retain the actual
coexact angular covector J. Write N=sum_j J_j^2, a complex bilinear square.
The original volume-weighted Einstein current at time zero is

```
A^0 = [-2w(lambda-2)fg/(R^2-1) - w R^2 g F/(R^2-1)^2] N,
A^1 = [-(lambda-2)(g'f-gf') - C] N,
A^2 = A^3 = 0,
C = [Rg + R^2 g'/(R^2-1)] F.
```

Every derivative slot is an actual field derivative. The angular equation is
derived from the literal Eisenstein covector. The right stream master is
`-R^3 F J/(R^2-1)` and the left stream master is zero. No radial ODE or angular
eigen-equation is supplied as an extra physical assumption. In the causal
Green band the reconstructed field is the radius lift of the actual causal
transform's physical projection, almost everywhere in the original measure.

For interior s≤t<0 the checked Einstein flux identity is

```
A^1(t)-A^1(s) = [-(lambda-2) integral_s^t gF - (C(t)-C(s))] N.
```

This identifies a projected mixed sector. The temporal-current restoration
below retains the full normalizable left mode, joins both original radial
intervals and evaluates its residue after the horizon limit. Full angular
reconstruction, independent SS/VV sectors, retarded/advanced Peierls
identification and nonvanishing of the source-evaluated residue remain open.

## Closed local temporal QNM transfer

The temporal current has a proved meromorphic continuation from the actual
physical band. Its exact QNM residue is

```
-2 w0 (lambda-2) g(w0,x) Res(f)(x) N/(R^2-1).
```

Proof mechanism: the source-rate pole is distinct from either fundamental
frequency; all three principal cutoff responses are analytic there. Their
finite angular decomposition therefore makes the complete F analytic there.
The original radial mode is analytic there. Consequently the retained
source contact is regular and contributes zero residue. The existing exact
field-residue limit then transfers to the actual temporal Einstein current.
All three leaves pass scratch checks and exact leaf audits. The current has
an analytic Laurent remainder. At every interior point its radial
multiplier is nonzero, so a nonzero field residue and nonzero angular
bilinear square imply a nonzero local Einstein temporal residue.

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

## Other unresolved source factors

The source-moment substitution produces an incomplete beta integral; it does
not supply a nonvanishing proof. Source transposition retains the onset
remainder and horizon finite part. The actual angular source, radial source
moment, fixed onset, angular integration, and Hawking-clock extinction remain
substantive open problems. No numerical experiments are used.

## Active angular conjecture: the original cusp jet pairing

Use s=u+1/2, so the unchanged physical parameter is s0=rho/2. The literal
constant term read from `ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly` is

```
E(s;Y)=A(s)Y^s+D(s)Y^(1-s)+tail,
A(s)=reflectedCompletedLambda(2s),
D(s)=reflectedCompletedLambda(2s-1).
```

The candidate follows from the original Green boundary identity, before
choosing any dual. For two spectral parameters s,t, division of the constant
term Wronskian by t(t-1)-s(s-1) gives the four terms

```
 A(s)A(t)Y^(s+t-1)/(s+t-1)
-D(s)D(t)Y^(1-s-t)/(s+t-1)
+[D(s)A(t)Y^(t-s)-A(s)D(t)Y^(s-t)]/(t-s).
```

Expand in s-s0 and t-s0 first, then take the fixed-parameter cusp finite
part of each jet. Because 2s0-1=rho-1 is nonzero and nonreal, the first two
terms retain nonzero cusp powers and their log derivatives. Their finite
part is subtracted. The constant log coefficient of the last term is

```
K(s,t)=[D(s)A(t)-A(s)D(t)]/(t-s),
K(s,s)=D(s)A'(s)-A(s)D'(s).
```

This is an analytic divided difference near (s0,s0). If A vanishes to order
m at s0 and A_m=A^(m)(s0)/m!, its normalized Taylor matrix
G_ij=[(s-s0)^i(t-s0)^j]K, 0<=i,j<m, has

```
G_ij=0             for i+j<m-1,
G_ij=D(s0)A_m      for i+j=m-1,
det G=(-1)^(m(m-1)/2) [D(s0)A_m]^m.
```

The algebraic implication is a paper derivation. The substantive conjecture
is that G is the jet pairing of the **full original angular fields** after
integrating on the actual truncated modular cell. This requires the literal
Green identity, cancellation of paired modular sides, uniform cusp-tail
bounds for every spectral jet, and the stated order of differentiation and
finite part. It is not an analytically varying finite part at distinct
fixed parameters; changing that order discards the diagonal information.
The coexact covector pairing must then be attached, with its actual measure
and boundary contacts. The corresponding generalized modes must enter the
left-QNM action and full source projection. None of these identifications
is claimed proved by the radial-norm modules.

Corpus ingredients read: `ReflectedDividedDifference` gives factorial-exact
normalized jets; `XiHedenmalmMultiplicityChain` gives vanishing below and
nonvanishing at the actual Xi multiplicity; `GammaShiftConfluentCasoratian`
contains triangular jet determinant arguments. `KeldyshQNMAlgebra` assumes
an invertible finite modal basis, so it supplies subsequent matrix algebra
only after the physical pairing above is established. Broad/deep searches
for biorthogonal, confluent, and MaassSelberg were partial; unrelated search
hits were not treated as applicable proofs.

## Closed incoming Green horizon expansion

Write G for the original `continuedResponse`, h=z^(w/2)H for its incoming
mode, S for the literal `sourceRemainder`, and O(w) for the fixed continued
onset 1/(w-2s)+onsetCorrection(2s,w). The original Wronskian gives

```
Q=G/h,
Q' = T = M(z,w) O(w) / [2 z sqrt(1-z) h(z,w)^2],
M = firstEndpointMellin(H*S).
```

This is the actual quotient derivative on the punctured connection germ.
The connection denominator cancels exactly. Removing the incoming powers
gives T = Mhat O/[2 sqrt(1-z) H^2], where Mhat=M/z^(w+1).
The new normalized Mellin bound is

```
|Mhat-S(w,0)/(w+1)| <= C z/(Re(w)+2).
```

Lean derives one frequency-horizon neighborhood with 1/2<=|H|<=3/2.
Combining its reciprocal bound with the actual source estimate proves,
uniformly in frequency near every nonreal w with Re(w)>-2 and w!=2s,

```
d(w)=S(w,0) O(w)/[2(w+1)],
|T(w,z)-d(w)| <= C z.
```

The physical specializations discharge these frequency conditions at both
Xi fundamental frequencies. No nonvanishing horizon mode or uniform
source remainder is added as a physical premise.

Define the endpoint coefficient from a positive radius b by

```
A_b(w)=G(w,b)/h(w,b)-integral_0^b T(w,z) dz.
|G(w,z)/h(w,z)-A_b(w)-d(w)z| <= C z^2,  0<z<=b.
```

The quadratic bound is uniform in a frequency ball wherever the connection
is nonzero. The fundamental theorem of calculus proves it for the actual
Green block. The source integral is analytic through the connection zero:
spatial continuity and the derived common bound feed the corpus theorem
`differentiableAt_integral_of_cauchy_dominated`. Consequently A_b is
meromorphic. These statements have passed scratch checks and exact leaf
audits in `NormalizedFirstEndpointMellin`, `ThetaCuspHawkingBMIncomingSourceTransport`,
`ThetaCuspHawkingBMLaplaceHorizonGaussBound`, `ThetaCuspHawkingBMIncomingSourceBound`,
and `ThetaCuspHawkingBMIncomingHorizonExpansion`.

G here is an original Green block. Passing this expansion through the
explicit gradient lift, all principal corrections, and the full physical
current is still part of the assembly below.

## Original incoming density: explicit endpoint coefficients

The actual Gauss coefficients now give, uniformly near each nonreal
frequency and for 0<=z<=1/2,

```
H(w,z)=1+h1(w)z+O(z^2),
h1(w)=gaussA(w)*gaussB(w)/gaussC(w),
1/[2sqrt(1-z)]=1/2+z/4+O(z^2).
```

Lean proves the arbitrary finite-order Gauss remainder from its coefficient
majorant, as well as the second-order specialization above. The Jacobian
remainder has the explicit bound 2z^2. The coefficient h1 is analytic at
nonreal frequencies, and h1(w0)=-1/2 at either fundamental root.

Multiplying these bounds with the actual Green quotient expansion gives

```
core(w,z)=(G/h)*H^2/[2sqrt(1-z)],
core0(w)=A_b(w)/2,
core1(w)=(h1(w)+1/4)*A_b(w)+d(w)/2,
|core-core0-core1*z| <= C*(|A_b(w)|+|d(w)|+1)*z^2.
```

The constant C is uniform on a derived frequency neighborhood away from
connection zeros. The dependence on A_b is retained explicitly; its pole
has not been bounded away. The actual source coefficient d is analytic
through connection zeros. The exact geometric attachment is

```
z^(w-1)*core(w,z)=G(w,z)*h(w,z)/[2z sqrt(1-z)],  0<z<1.
```

This identity also covers zeros of h, using Lean's totalized division; no
nonvanishing-mode hypothesis is added to it. At a fundamental frequency,
the linear coefficient is -A_b/4+d/2. The analytic source term d/2 must
remain in a subtraction of the full current, even though it has no residue.

These statements pass the foreground Lean scratch check in
`ThetaCuspHawkingBMIncomingPairingEndpoint`. The supporting leaves
`HypergeometricTaylorEndpointBounds`, `QuadraticEndpointProducts`, and
`ThetaCuspHawkingBMLaplaceHorizonTaylorBound` have passed exact leaf audits.
The incoming pairing leaf also passed its warning-free exact audit (177 seconds,
two jobs, cached imports only). All four umbrella imports are wired.
The formal lint gate passed, reporting existing large-file warnings.

## Exact temporal-contact horizon factor

The complete projected forcing has a proved exact factorization F=z F_hor.
It is obtained from the existing affine-frequency decomposition and both
proved horizon zeros of the reduced source polynomial:

```
reducedPolynomial(s,w,v)=(1-v^2)*reducedHorizonQuotient(s,w,v),
reducedHorizonQuotient = [reducedHorizonPolynomial(s,v)
  + w*s*(s-1)*v^2*((2s+3)v+3)/2]/(1+v).
```

Here v=radialUnit(x), 1+v>0, and z=1-v^2. The three cutoff coefficients
already carry z. Thus F_hor retains the native residual angular period and
all three complete principal-difference/cutoff periods. The exact original
radius identity R^2 z=R^2-1 then gives

```
(R^2-1) A^0 = [-2w(lambda-2)fg-w g F_hor] N.
```

This is the full continued temporal current, including its source contact.
The apparent additional horizon denominator cancels against a zero of the
literal source. The identities passed Lean in
`ThetaCuspHawkingBMTemporalContactHorizonFactor`, including a warning-free
exact leaf audit using cached imports; its umbrella import is wired. Uniform endpoint estimates
for F_hor and the restored full-current integral are still required.

All six new leaves passed their exact audits. The formal lint gate passed
with only existing large-file warnings.

## Active residue/interchange target

The complete temporal horizon-mode current now has a source-derived
uniform quadratic jet, exact identification with the original current,
spatial/frequency regularity, two-counterterm restoration at every
sufficiently small cutoff, and a residue theorem after integration.
The inner lift, all three principal channels and temporal source contact
are retained in this result, detailed below.

The complete normalizable left-mode current still needs its opposite
horizon branch and original outer interval joined at the same cutoff.
The original mode decomposition has opposite coefficient connection/(2w).
Its cancellation against the original Green denominator suggests an
analytic logarithmically restored opposite-current profile. Evaluating
and proving survival of the complete joined residue remain open.

### Direct analytic split for the incoming channel

The quotient derivative and its integrable endpoint bound give, by the
fundamental theorem of calculus, the exact paper identity

```
Q(w,z)=A_b(w)+P(w,z),       P(w,z)=integral_0^z T(w,t)dt.
M(w,z)=H(w,z)^2/[2sqrt(1-z)],
m1(w)=h1(w)+1/4,
M=1/2+m1*z+O(z^2),         P=d*z+O(z^2).
```

Here T is analytic through the connection zero. The same dominated-integral
argument already used for integral_0^b T gives pointwise analyticity of P.
The estimates imply P*M=d*z/2+O(z^2), uniformly on a smaller frequency
neighborhood. This leads to the following concrete finite parts:

```
N_b(w)=b^w/(2w)+m1(w)*b^(w+1)/(w+1)
       +integral_0^b z^(w-1)*(M-1/2-m1*z)dz,
J_b(w)=d(w)*b^(w+1)/(2(w+1))
       +integral_0^b z^(w-1)*(P*M-d*z/2)dz,
FP incoming integral = A_b(w)*N_b(w)+J_b(w).
```

The active formalization extends the existing source-transport module with
one common-neighborhood theorem for P: spatial continuity, pointwise
frequency analyticity through connection zeros, |P|<=Mz,
|P-dz|<=Cz^2, and the exact Q=A_b+P identity. It uses the already derived
transport neighborhood, the fundamental theorem of calculus, and the
Cauchy-dominated integral argument. The extension passed its warning-free
scratch check and exact module audit (118 seconds, two jobs, cached imports).
Its API is `incomingSourcePrimitive_common_data`.

`HTGeometry.QuadraticEndpointMellin` also passed its warning-free scratch
check and exact leaf audit (47 seconds, two jobs). For a fully frequency-
dependent F and a common bound |F-a0-a1*z|<=Cz^2 it proves integrability of
the subtracted density, its explicit norm bound and vanishing endpoint
limit, the exact original cutoff identity, convergence after restoring
both counterterms, and analyticity of the restored finite part. The APIs
are `remainder_integrable`, `remainder_norm_le`, `remainder_tendsto_zero`,
`remainder_analyticAt`, `cutoff_eq`, `cutoff_tendsto`, and
`finitePart_analyticAt`. The new umbrella import is wired.

The application to M and P*M passes its warning-free Lean scratch check.
`incomingPairingFinitePart_horizon_restoration` derives all analyticity,
spatial continuity, and uniform remainder conditions from the literal Gauss
family and actual source primitive, on the same fixed b. Its endpoint
limit has the original density G*h/[2z sqrt(1-z)], with coefficients
A_b/2 and (h1+1/4)A_b+d/2. Both restored pieces and P(w,b) are analytic
through the connection zero. The exact leaf audit passed (35 seconds,
two jobs, cached imports); the new umbrella import is wired.

The remainder integrands are bounded by a common constant times
z^(beta+1), for beta>-2. Thus the paper reduction is to prove N_b and J_b
analytic near the nonreal fundamental frequency, using the actual Cauchy-
dominated integral theorem. At a simple pole of A_b this yields
Res(FP incoming)=N_b(w0)*Res(A_b). The finite-part definitions and native cutoff-limit identity now pass
Lean. The physical residue exchange now passes its Lean scratch check.
The integral from b to the outer endpoint must also be restored before
identifying the complete Gamma radial norm.

The physical incoming residue is derived from a direct paper proof and
a successful Lean scratch check. For
K=reducedGreenGradient(chi,s,1), set

```
B_b(u)=[(normalizable(u,b)/h(u,b))*sourceMellin_b(u)
        +outerSourceIntegral_b(u)]*continuedOnset(u).
Q(u,b)=B_b(u)/[-connection(u,chi)].
```

At either physical fundamental frequency w0, h is nonzero on 0<b<1,
normalizable=h, and the two source moments combine into the already proved
fixed `fundamentalSourceMoment`. The derivative of -connection is the
proved nonzero -connectionSimpleSlope. Hence the actual punctured limit is

```
lim (u-w0)*Q(u,b)=sourceMoment(w0)*continuedOnset(w0)/[-connectionSlope(w0)].
```

Subtracting analytic P(u,b) gives the same residue for A_b. Analyticity of
N_b and J_b then gives the residue of the restored integral. The physical leaf
`ThetaCuspHawkingBMPhysicalIncomingPairingResidue` proves this and the actual
cutoff restoration at one common b, for every Xi copy, source branch and
fundamental side, without a supplied residue or interchange premise. Its
exact leaf audit passed without warnings (29 seconds, two jobs, cached
imports); its umbrella import is wired.
`physicalIncomingPoleAmplitude_eq_cleared` identifies the coefficient with
the existing sourceMoment*clearedOnset/physicalDenominatorSlope.
`physicalIncomingQuotient_residue` proves the pointwise quotient residue
at every interior radius; `physicalIncomingPairing_residue_and_restoration`
proves the residue after restoring the original horizon integral.
The source moment and onset may still vanish; no pole-survival claim is
added by these exact residue identities.

For the opposite left mode, the actual coefficient is c_minus=C/(2w),
where C=connection(w,chi). Its opposite Gauss product is
V=H(w,z)*H(-w,z)/[2sqrt(1-z)]=1/2+O(z). The exact logarithmic finite parts
suggested by the same source split are

```
L_b(w)=log(b)/2+integral_0^b (V-1/2)/z dz,
K_b(w)=integral_0^b P(w,z)*V(w,z)/z dz,
FP opposite integral = c_minus*(A_b*L_b+K_b).
```

The counterterm added at e is c_minus*A_b*log(e)/2. The paper proof of
analytic restoration uses the common O(z) bounds for V-1/2 and P, giving
bounded subtracted integrands. The actual quotient numerator above gives
C*A_b=-B_b-C*P(w,b) on the punctured connection germ. Consequently the
restored opposite pairing has the explicit analytic extension

```
[(-B_b-C*P(w,b))*L_b+C*K_b]/(2w).
```

Its value at a fundamental frequency is -B_b(w0)*L_b(w0)/(2w0), and its
residue is zero.

The general logarithmic restoration now passes a warning-free Lean scratch
check in `HTGeometry.LogarithmicEndpointFinitePart` (namespace
`LogarithmicEndpoint`). It proves integrability and |remainder|<=C*b,
vanishing remainder at zero, exact cutoff identity, actual cutoff limit,
and analyticity of the restored finite part for a frequency-dependent
kernel with a common O(z) endpoint remainder. Its warning-free exact
audit passed (6.3 seconds, two jobs, three cached project imports); its
umbrella import is wired.
The native opposite-mode application derives a common nonzero
incoming-mode interval; unlike the incoming square, the opposite density
cannot use totalized division at a zero of h. Shrinking to that interval
preserves A_b by the exact Q=A_b+P identity evaluated at the new cutoff.

`ThetaCuspHawkingBMOppositePairingFactor` passes its warning-free scratch
check and exact leaf audit (338 seconds, two jobs, 4,004 cached project
imports). Its narrowed imports avoid the unrelated field-wave layer.
It derives the original product's common bounds |V-1/2|<=Cz and |V|<=M,
frequency analyticity and spatial continuity, and its exact density
identity under h!=0. Its source and artifacts are installed and its
umbrella import is wired.
`ThetaCuspHawkingBMOppositePairingFinitePart` combines the Gauss nonzero
neighborhood with the source primitive's neighborhood, proves A_b is
preserved at their common smaller cutoff, and derives the original
c_minus*G*h(-w)/[2z sqrt(1-z)] logarithmic cutoff limit. Its scratch check
and exact leaf audit passed without warnings (87 seconds, two jobs,
4,335 cached project import metadata entries). Source, artifacts and
umbrella import are installed. The theorem
`oppositePairingFinitePart_horizon_restoration` supplies analytic L_b,
K_b and P_b at the same cutoff used by the original integral.

`ThetaCuspHawkingBMPhysicalOppositePairingRegularity` proves the physical
analytic extension, its source-determined resonance value, the punctured
limit of the actual restored pairing, its zero residue, and its original
logarithmic cutoff restoration on the same common cutoff. Its exact leaf
audit passed without warnings (107 seconds, two jobs, 4,341 cached project
import metadata entries). Source, artifacts and umbrella import are
installed. Denominator cancellation is isolated in a seven-variable scalar
lemma, avoiding normalization of expanded Green integrals; resource limits
are unchanged. Analyticity is proved for the explicit extension, not
inferred from the totalized pairing's assigned value at the pole.

Corpus searches include broad single-word queries, deep all-view method
retrieval, unlimited per-module results, pagination and exclusion of HB
modules. All candidate, source-method, idea and ingredient-set sections
are inspected. The latest division deep query was partial over 56,948
inventoried files (compiler metadata mostly pending); its order-theoretic
division suggestions do not establish a complex residue theorem. The
source-moment query completed its retrieval and located the exact
`fundamental_source_sum_eq_moment` method used in the physical proof.
The Cauchy-dominated integral mechanism, source primitive, Gauss remainder
and actual connection slope are the useful verified ingredients. Broad
arXiv queries also explored transgression, gluing and renormalization;
no retrieved June–September 2026 theorem supplied an applicable ingredient.

Latest repository lint exits with five unreachable modules outside these edits:
`RHTower.DeningerOriginalGreenPoleCalculus`,
`RHTower.ThetaCuspHawkingBMHorizonCoordinateJets`,
`HTGeometry.ElementaryHorizonJets`,
`HTGeometry.SecondEndpointMellinLaurentInterchange`, and
`HTGeometry.UniformSecondOrderJet`.
The new restoration and outer-pairing leaves are wired and their exact
audits passed. The global lint gate is not claimed passed for this state.


### Frequency Lagrange route for full radial assembly

The corpus supplies the complex compact-interval Lagrange identity in
`HTGeometry.SturmLagrangeIdentity` and the actual forced radial bracket in
`ThetaCuspHawkingBMOriginalForcedBoundaryPairing`. The next candidate uses
frequency differentiation of the original normalizable solution n. In the
tortoise equation G''-(w^2+V)G=F, where F is minus the corpus
`originalForcing`, and n''-(w^2+V)n=0, putting v=partial_w n
gives v''-(w^2+V)v=2*w*n, hence

```
2*w*integral_L^0 G*n = [G*v'-G'*v]_L^0 + integral_L^0 F*v.
```

This is a paper mechanism, not yet an endpoint theorem in Lean. It requires
the actual mixed frequency/radial derivatives and restored Wronskian limit;
the compact-interval identity alone does not supply those conclusions.
The original outer source already has a common bounded majorant through
z=1 (`outerSource_uniform_bound`), and its actual integral is entire
(`outerSourceIntegral_entire`). These are available ingredients for the
remaining outer-endpoint proof.

The mechanism has an exact normalization check from the existing Gamma
formulas. At a fundamental connection zero, the other Gamma argument is
w+3/2, so Gamma recurrence gives

```
connectionSimpleSlope(w,chi,side) = 2*w*normFinitePart(w).
```

Consequently the already integrated temporal Laurent density simplifies
on paper to

```
(physicalAngularParameter(q)^2-1/4-2) * physicalSelfSourceCoefficient(q)
  * fundamentalSourceMoment(w,s,a) * continuedOnset(s,w)
  * modeAngularSquare(physicalModeAngularJet(q,z)).
```

This cancellation identifies the desired source quantity in the full
restored action. It does not by itself interchange the original current's
radial exhaustion and frequency residue. This exact simplification is not
yet a new Lean theorem.

Latest broad searches include transposition and Lagrange, with all retrieval
views, uncapped module hits and (for Lagrange) exclusion of HB modules.
The Lagrange method retrieval located the actual integrated Sturm bracket;
its proposed polynomial-interpolation ingredient set is not applicable.
Retrieval completed, but compiler metadata remains mostly pending and
semantic coverage unavailable. The scoped outer search located the actual
uniform-bound and entire-integral theorems above. ArXiv Volterra and
isospectral searches with a recent-date preference returned older papers;
`Isospectrality and heat content` (arXiv:1304.4030, revised 2014) was opened.
No external theorem from it has been used in these proofs.


The outer-integral candidate uses the regular tortoise ODE rather than a
Gauss estimate at z=1. `continuedTortoiseGreen_hasDerivAt` and
`continuedTortoiseGreen_equation` supply its actual two spatial derivatives
and forced equation on t<0. On a fixed interval T<=t<0, the potential
horizonCoordinate(t)*(1/4+chi^2) is bounded. A common frequency ball and
bounded initial values of the connection-cleared response and its first
derivative at T therefore give a uniform bound on both via Gronwall.
The same argument applies to the normalizable mode. Their product then
has a constant integrable majorant on (T,0), allowing frequency analyticity
of the cleared outer pairing by the Cauchy-dominated integral theorem.

The stronger usable corpus estimate is
`forcedSecondOrder_horizon_bound_symmetric` in `HTGeometry.SymmetricHorizonGrowth`.
Its original principal-frequency application is
`JointSourceClearedUniformBound.clearedPrincipalDifference_compact_bound`.
The independent-angular-frequency application now passes Lean in
`ThetaCuspHawkingBMReducedGreenUniformBound` (scratch and exact leaf audit
passed without warnings; 67 seconds, two jobs, 4,326 cached project imports).
Its source, artifacts and umbrella import are installed. It uses the already
defined `clearedReducedGreen`, including its explicit gradient lift, and
proves the corresponding first jet and actual cleared ODE:

```
U'' = w^2*U + z(t)*(1/4+chi^2)*U - F_clr,
F_clr = -connection(w,chi)*reducedCoefficient(s,w,a,clearedOnset(s,w),t).
```

Both initial jets are analytic in frequency. The existing
`reducedCoefficient_family_norm_le_exp` derives the compact-family forcing
bound. The resulting theorem `clearedReducedGreen_compact_bound` states

```
|U(w,t)| <= C*exp(-|Re(w)|*t),
  w in interior(Omega), t<0,
```

for every compact Omega in the nonreal strip Re(w)>-2. The estimate extends
through source and connection zeros using continuity of the explicit
analytic numerator. It does not require an ODE for a totalized response at
those zeros. `physicalClearedReducedGreen_outer_uniform_bound` then derives,
for each Xi copy, branch, side and finite T, a frequency ball and one
constant bounding the actual full reduced numerator for all T<=t<0.
No forcing, growth, initial-data or resonance-regularity premise is supplied
to that physical theorem. Denominator algebra is isolated in scalar lemmas;
resource limits are unchanged.

The common bound for the frequency-dependent normalizable left mode and
Cauchy-dominated integration of its product with this numerator now pass
Lean in the outer-pairing leaf described below. `outerGauss_uniform_bound`
and the positive-radius power formula supply the concrete estimates. Spatial
continuity of the undivided moments is available through
`horizonFirstMoment_hasDerivAt` and `outerSourceIntegral_hasDerivAt` in
`JointSourceClearedRadialAdmission`. The full temporal current still needs
all four source channels and both contacts assembled before its residue
interchange is proved.

A broad deep `Gronwall` search also located the phase-pair proof in
`HTGeometry.LinearSecondOrderComparison.phasePair_norm_le`. Its existing
statement is real and homogeneous; its useful mechanism is controlling
the solution and first derivative together. The native application needs
the complex forced pair and actual source bounds described above. The
retrieval completed over 56,989 inventoried files, with 44,547 compiler
entries pending and stale snapshots reported; candidates, source methods,
proof ideas and ingredient sets were inspected, not treated as verified
applications.

Further broad searches used `forced`, `normalizable`, and OR matching for
`bound uniform`, plus a deep query describing the paired complex forced
ODE mechanism. The bound query was partial; its candidate and method
sections led to the existing cleared-principal estimate and its underlying
symmetric growth theorem. The normalizable query completed retrieval over
56,998 files, with compiler metadata mostly pending and stale coverage
snapshots reported. Its normalizable boundary theorem still assumes the
original chamber and is not used as a uniform continued-frequency bound.
Broad arXiv searches for Volterra and impedance included
[Volterra Generative Models](https://arxiv.org/abs/2606.18071), submitted
16 June 2026. Its approximate stochastic lifts supply no exact theorem
used in this deterministic Green-response proof.

### Actual outer pairing and residue

The explicit outer Gauss factor and positive-radius power formula derive
one uniform bound for `normalizable(u,chi,z(t))` on a frequency ball and
T<t<0. Combined with the full reduced numerator bound above, this gives
absolute integrability and frequency analyticity of

```
R_T(w) = integral_(T,0) clearedReducedGreen(w,chi,s,a,t)*n(w,t) dt.
```

The original pairing is
`Q_T(w)=integral_(T,0) continuedReducedGreen(w,chi,s,a,1,t)*n(w,t) dt`.
Its original scalar denominator gives the exact identity
`R_T(w)=D(w)*Q_T(w)`, where `D(w)=-(w-2*s)*connection(w,chi)`.
At each physical fundamental w0, the actual fixed-source factorization
then gives

```
lim_(w->w0) (w-w0)*Q_T(w)
  = [fundamentalSourceMoment(w0,s,a)*clearedOnset(s,w0)
       /physicalFundamentalDenominatorSlope(q,branch,side)]
      *integral_(T,0) n(w0,t)^2 dt.
```

The same amplitude already occurs in the restored incoming horizon block.
The outer integral is taken before the frequency limit. This argument
retains the original reduced response's gradient lift. The prepared Lean
leaf `ThetaCuspHawkingBMReducedOuterPairing` passes its scratch check and
exact leaf audit without warnings (34 seconds, two jobs, 4,332 cached
project imports). Source, artifacts and umbrella import are installed.
Matching the inner and
outer coordinate cutoffs and assembling the complete source/contact
current remain separate obligations. No source-moment or onset
nonvanishing follows from the residue identity alone.

### Common-cutoff fundamental norm

The joining identity is now proved for every actual fundamental frequency
and every T<0, with b=horizonCoordinate(T):

```
incomingNormFinitePart(chi,b,w0)
  + integral_(T,0) n(w0,t)^2 dt = D4BMFundamentalNorm.normFinitePart(w0).
```

`D4BMFundamentalNorm.physicalFundamentalNorm_join` in
`ThetaCuspHawkingBMFundamentalNormJoin`
identifies the incoming Gauss factor with sqrt(1-z), its first coefficient
with -1/2, and the pairing kernel with sqrt(1-z)/2. Its two subtraction
coefficients are exactly 1/2 and -1/4. The exact
`QuadraticEndpointMellin.cutoff_eq` identity then cancels the arbitrary
cutoff against the original tortoise-coordinate outer integral. The
finite part at upper endpoint one equals the already established
`D4BMFundamentalNorm.normFinitePart`; no new normalization is assigned.

Scratch and exact leaf audit passed without warnings (28 seconds, two
jobs, 4,415 cached project imports). Source, five artifacts and umbrella
import are installed. Small scalar identities and integral congruences
keep elaboration local; no resource limits were raised.

### Regular horizon branch joined to the original outer integral

The verified `ThetaCuspHawkingBMRegularOuterPairing` derives frequency
analyticity of the actual Wronskian coefficient Aplus(w), with Aplus(w0)=1
supplied by the original fundamental normalization theorem. Continuity of
the original horizon coordinate and the intermediate value theorem match
the restored horizon cutoff to an actual T<0. Thus

```
S_T(w) = Aplus(w)*incomingPairingFinitePart(s,chi,a,1,K,z(T),w)
           +continuedReducedOuterPairing(chi,s,a,T,w)
lim_(w->w0) (w-w0)*S_T(w)
  = physicalIncomingPoleAmplitude(q,branch,side,a)*normFinitePart(w0).
```

`regularOuterPairingCutoff` retains the original positive-cutoff incoming
integral and both derived counterterms, multiplied by Aplus(w), then adds
the original outer integral. Its cutoff limit is S_T(w) on the actual
connection-nonzero germ. This restoration precedes the frequency-residue
limit. The theorem constructs its matching cutoff and frequency ball;
neither is an added premise. Scratch and exact leaf audit passed without
warnings (37 seconds, two jobs, 4,419 cached project imports). Source, five
artifacts and umbrella import are installed; no resource limits changed.

The opposite horizon block and inner explicit lift still need admission
at this same cutoff, followed by all four source channels and both
Einstein contact terms. The assembled current, retained pairing survival,
fixed Hawking-clock extinction and RH remain unproved.

Broad searches for gluing, cutoff and tortoiseOf and natural-language deep
method searches were inspected alongside candidate lemmas, source
arguments and proposed ingredient sets. The exact quadratic Mellin
identity was applicable; generic lattice-join suggestions were not. The
Wronskian search recovered both actual frequency-analytic radial jets.
Coverage inventoried about 57,010 files, with most compiler metadata
pending and semantic coverage unavailable; the Wronskian deep request was
partial. New candidate applications were verified by Lean. Broad arXiv
factorization searches included the July 2026
[Landweber unique-factorization paper](https://arxiv.org/abs/2607.03475);
its algebraic finite-jet result is not used in this analytic cutoff proof.

The repository lint gate still reports unreachable modules outside this
work, including the pending horizon-jet and endpoint-interchange leaves.
Both new joining modules are wired and passed exact audits; global lint
is not claimed passed. Frontier map and universal STATUS were not edited.

### Simultaneous incoming/opposite cutoff restoration

The two restoration theorems now hold at every sufficiently small positive
cutoff, using one frequency ball and one upper cutoff. The endpoint
amplitude is re-centered exactly by Q(z)=Q(b)-P(b)+P(z), so restriction
preserves the original response and counterterms. Existing theorem
signatures remain as corollaries at the upper cutoff. Scratch checks and
exact leaf audits passed for `ThetaCuspHawkingBMIncomingPairingFinitePart`
(124 seconds, two jobs, 4,337 cached project imports) and
`ThetaCuspHawkingBMOppositePairingFinitePart` (9.3 seconds, two jobs, 4,335
cached project imports). Updated sources and artifacts are installed.

The active joining proof takes a cutoff below both bounds and retains the
actual normalizable decomposition n=Aplus*horizon+connection/(2w)*horizon(-w).
The proposed finite part is Aplus*incomingPairingFinitePart plus
oppositePairingFinitePart. Its original single-integral restoration keeps
both power counterterms and the logarithmic counterterm. Spatial
integrability is derived from `continuedResponse_hasDerivAt` and the
actual mode jets before applying integral additivity. The incoming
residue is the original fixed-source amplitude times N_b; the opposite
block has an analytic extension and zero residue at this same b. Joining
the original outer integral should then give the established full radial
norm with the same source amplitude. The original single-integral splitting theorem in
`ThetaCuspHawkingBMNormalizableHorizonPairing` has passed scratch and exact
leaf audit (100 seconds, two jobs, 4,341 cached project imports); source,
five artifacts and umbrella import are installed. The physical residue
and simultaneous restoration theorem is now proved in
`ThetaCuspHawkingBMPhysicalNormalizablePairing`:

```
F_T(w) = Aplus(w)*incomingPairingFinitePart(w)
           +oppositePairingFinitePart(w)+Q_T(w)
lim_(w->w0) (w-w0)*F_T(w)
  = physicalIncomingPoleAmplitude(q,branch,side,a)*normFinitePart(w0).
```

`physicalNormalizableOuterPairing_residue_and_restoration` constructs one
T<0 and one frequency ball. On the original connection-nonzero germ,
`normalizableOuterPairingCutoff` tends to F_T(w): this expression contains
the single original normalizable horizon integral, both power
counterterms, the logarithmic counterterm, and the original outer
integral. The proof derives ordinary spatial integrability before
splitting the horizon integral. The opposite analytic extension and its
zero residue are established at exactly the same b=horizonCoordinate(T)
as the incoming block. The source amplitude and normalization remain the
original ones. Scratch and exact leaf audit passed without warnings
(10 seconds, two jobs, 4,425 cached project imports); source, five
artifacts and umbrella import are installed. The scalar source-endpoint
step uses explicit normalization and mul_sub instead of expanding the
source integral inside ring. No resource limits were raised.

The incoming full-current result below retains the inner lift and complete
source contact. Their opposite-branch restoration and full outer-current
assembly remain open for the normalizable left mode.

The next inner-lift correction has a concrete source-derived kernel.
Writing r=sqrt(1-z), the actual definitions give

```
radialLift(s,w,a,T,t)
  = (-s*(s-1)/4)*z^(w/2)*(1+r)^(2*s-w)*a^2*T*r^3.
```

Thus its incoming pairing density is z^(w-1) times
`(-s*(s-1)/8)*amplitudeProfile(s,a,T,w,z)*(1-z)*H_w(z)`;
the opposite pairing has z^(-1) and H_(-w) instead. The leading kernel
need not vanish. The proposed correction therefore retains two incoming
power subtractions and one opposite logarithmic subtraction.
`ThetaCuspHawkingBMHorizonCoordinateJets` already supplies
`radialLift_eq_profile`, `amplitudeProfile_jet` and `liftProfile_jet`.
Combining the amplitude jet with the exact factor 1-z and the Gauss jet
avoids introducing an inverse-square-root estimate. The fixed onset is
analytic off its source pole, separated from every physical fundamental
frequency by the existing source-rate theorem. The incoming full-current proof below retains this lift directly inside
its source-derived profile; a separate lift-only finite part is not needed
for that result. Its opposite-channel restoration remains open.

The restriction, cutoff-method, continuedResponse and lift searches used
broad and deep corpus retrieval, including source arguments and proposed
ingredient sets. The actual spatial derivative theorem and explicit
amplitude/lift jets supplied applicable ingredients; generic restriction
and transport suggestions did not replace the required source identity.
Retrieval completed with compiler metadata mostly pending and semantic
coverage unavailable. Broad arXiv sewing/localization searches included
[nonlocal localization](https://arxiv.org/abs/2606.27387), June 2026. Its
normalized detector-kernel variance law supplies no theorem used in this
complex bilinear radial pairing. No computation was run.

All four affected leaves passed scratch and exact-module checks with no
resource-limit increases. New imports are wired; no umbrella build ran.
Final lint status is recorded with the full-current result below.

## Full temporal horizon current: original density, restoration and residue

`ThetaCuspHawkingBMTemporalCurrentHorizonIdentification` identifies the
complete horizon-mode temporal current with the existing uniform profile.
The proof separately reconstructs the reduced self response, all three
principal cutoff channels, the full source contact and the radial Jacobian.
`clearedDensityProfile_eq_actualAction` identifies the same expression
with component zero of the actual projected Einstein action on its physical
Laplace band. This is the horizon left-mode leg (`outer=false`).

`ThetaCuspHawkingBMTemporalCurrentHorizonRegularity` proves spatial
continuity and frequency analyticity of the full cleared profile through
the fundamental QNM. Its continuity proof differentiates the undivided
source moments directly; it never obtains a value at the QNM by dividing
by the vanishing connection coefficient. Frequency analyticity requires
only the existing nonreal strip and separated source/principal poles,
which the physical restoration theorem discharges on one neighborhood.

Write D(w)=-(w-2s)*connection(w,chi), F(w,z)=clearedDensityProfile(w,z),
and j(w,z)=continuedTemporalRadialDensity(w,z). The checked identity is

```
z^(w-1)*F(w,z) = D(w)*j(w,z).
```

The density j is the original temporal current evaluated at tortoiseOf(z),
including the exterior radial Jacobian. Let N_b(w) be the two-term Mellin
finite part of F, with c0(w),c1(w) supplied by its proved uniform quadratic
jet. `physicalTemporalCurrent_horizon_restoration_and_residue` proves,
without supplied regularity or residue assumptions, that actual physical
q, branch, side, amplitude and angular point determine R>0 and B>0 such
that for EVERY 0<b<=B:

- N_b is analytic at the physical fundamental frequency w0.
- For w in the common frequency ball and connection(w,chi) nonzero,
  the original cutoff expression
  `integral(e..b,j(w,z)) + [c0(w)*e^w/w+c1(w)*e^(w+1)/(w+1)]/D(w)`
  tends to N_b(w)/D(w) as e tends to zero from above.
- After radial integration and endpoint restoration,
  `(w-w0)*N_b(w)/D(w)` tends to
  `N_b(w0)/physicalFundamentalDenominatorSlope(q,branch,side)`.

The source lift and contact are retained inside F. The power counterterms
come from the common source-derived jet; neither a residue nor a finite
part is assigned. Allowing every smaller cutoff permits later joining to
the opposite branch at exactly the same endpoint.

The proofs use explicit continuity/analyticity composition and polynomial
evaluation instead of broad tactic expansion of the full source. Redundant
ring/cast steps were removed. All three modules passed scratch checks at
default resource limits. Exact leaf audits passed warning-free: identification 80 seconds,
regularity 36 seconds, restoration/residue 110 seconds; each built only
the requested leaf (two Lake jobs) against cached dependencies. Sources,
five artifacts per new leaf and umbrella imports are installed. The three
used jet-support modules are also wired into HTGeometry. No umbrella,
full or dependency build ran; no resource limit was raised.

The full-normalizable-current conjecture is proved in the four companion
leaves described below: the actual opposite coefficient cancels the
self-channel pole, its uniform jet gives a logarithmic subtraction, and
the original complete horizon integral is restored before residue extraction.
The full radial join below now supplies the original outer interval and
evaluates the joined residue. Nonvanishing of its explicit source amplitude,
Hawking-clock extinction and RH remain unproved.

Broad amplitude/profile/logarithmic searches and mechanism-based deep
searches inspected candidate lemmas, source arguments and ingredient sets.
`QuadraticEndpointMellin.finitePart_analyticAt` and its cutoff theorem were
applicable and verified in the new Lean proof. Retrieval reported stale
coverage snapshots, unavailable semantic coverage and one unfinished
reranking stage; corpus search coverage was not treated as a proof.
A broad arXiv transmutation search also found the
[June 2026 revision of the Kannai-transform paper](https://arxiv.org/abs/2601.03616).
Its diffusion/wave representation was not used as a premise here.

Repository lint passes after the full radial join and all four new
imports. Previously pending companion modules are now reachable.
Frontier map and universal STATUS remain untouched.

## Full normalizable temporal horizon current

The pole-cancellation conjecture succeeds for the original current, with
the complete self response, all three principal channels, explicit lift
and temporal source contact retained. Four leaves supply the construction:

- `ThetaCuspHawkingBMTemporalOppositeCurrentProfile`: the exact ratio
  `-1/(2w*(w-2s))`, a uniform analytic quadratic jet for the opposite
  profile, and its spatial/frequency regularity through the physical QNM.
- `ThetaCuspHawkingBMTemporalNormalizableCurrentDensity`: the opposite
  contribution is the difference between the original normalizable
  current and its actual incoming-mode component. The original
  homogeneous-mode connection formula identifies this difference with
  the derived opposite profile divided by z. Finite-cutoff integrability
  is proved before decomposing the current integral.
- `ThetaCuspHawkingBMTemporalOppositeCurrentRestoration`: the profile's
  own constant jet coefficient supplies the logarithmic counterterm.
  Its restored integral is analytic through the QNM and has zero residue.
- `ThetaCuspHawkingBMTemporalNormalizableCurrentRestoration`: one original
  normalizable-current integral has a common-cutoff restoration with
  both power counterterms and the logarithmic counterterm. Residue
  extraction follows this restoration.

Let A(w) be the original normalizable mode's horizon-regular coefficient,
j_n the original temporal radial density with `outer=true`, j_h its
`outer=false` counterpart, and D(w)=-(w-2s)*connection(w,chi). The exact
opposite-mode coefficient is connection(w,chi)/(2w). Consequently

```
j_o = j_n - A(w)*j_h = F_o(w,z)/z,
F_o = [-1/(2w*(w-2s))] *
      N * [-2w(lambda-2)*selfPart - w*contactPart] * H_(-w)(z)
      / (2*sqrt(1-z)).
```

Here selfPart and contactPart are the original cleared source profiles,
N is the actual angular bilinear square, and H is the original Gauss
factor. The connection zero cancels algebraically; no self-connection
nonvanishing assumption is used for the profile's analytic germ.
The Gauss lower bound supplies a common spatial/frequency neighborhood
for the original finite-current decomposition.

For the source-derived incoming coefficients c0,c1 and opposite coefficient
d, set

```
N_b(w) = QuadraticEndpointMellin.finitePart(F,c0,c1,b,w),
L_b(w) = LogarithmicEndpoint.finitePart(F_o,d,b,w),
M_b(w) = A(w)*N_b(w)/D(w) + L_b(w).
```

The physical data determine R>0 and B>0, B<=1/2, such that for EVERY
0<b<=B and every w in the common ball with connection(w,chi) nonzero,

```
integral(e..b,j_n(w,z))
 + A(w)*[c0(w)*e^w/w + c1(w)*e^(w+1)/(w+1)]/D(w)
 + d(w)*log(e)  -->  M_b(w)                       (e --> 0+).
```

The actual normalizable coefficient satisfies A(w0)=1. The separately
proved analytic continuation of L_b and incoming restored residue give

```
(w-w0)*M_b(w) --> N_b(w0)/physicalFundamentalDenominatorSlope.
```

This closes the original normalizable left-mode temporal current's
horizon restoration at each angular point. The full radial join below
adds its original outer interval; a nonzero retained action is still open.

The proved residue-evaluation identity below is the exact factorization
`F(w0,z)=K*incomingPairingFactor(w0,chi,z)`, where

```
K = N * (-2*w0*(lambda-2)) * physicalSelfSourceCoefficient(q)
    * fundamentalSourceMoment(w0,s,a) * clearedOnset(s,w0).
```

The existing fundamental Green factorization gives its self-channel
identity; the clearing factor kills the principal/contact terms at w0.
The new proof identifies the actual endpoint coefficients, retains their
uniform-jet witnesses through restoration, and evaluates N_b(w0) as K
times the original incoming norm finite part. The corpus's
`JetCoefficientUniqueness` supplies the coefficient-uniqueness mechanism,
and `physicalFundamentalNorm_join` supplies the norm's exact cutoff join.
Neither substitutes for the full-current outer-integral proof or
nonvanishing of the physical coefficient.

Broad opposite-mode retrieval and mechanism-based deep searches inspected
candidate lemmas, source arguments and proposed ingredient sets. The
original connection identity, analytic jet closure and logarithmic
endpoint theorem were applicable and checked in Lean. A later deep
coefficient/finite-part search returned a proposed gamma-pole ingredient
set whose premises do not identify this current; it is not used.
That search completed, but its coverage was a snapshot with mostly
pending compiler metadata and unmeasured semantic coverage. A broad
arXiv confluence/impedance search included the August 2026
[finite-array active-impedance paper](https://arxiv.org/abs/2608.17844);
no result from it is used in the proof. No computation was run.

All four new leaves passed `lake env lean` scratch checks and exact
`lake build <module>` audits against cached dependencies. Audit times:
opposite profile 88 seconds, original current density 133 seconds,
opposite restoration 57 seconds, normalizable restoration 9.8 seconds.
Each audit built only the requested leaf (two Lake jobs). The proofs use
explicit analytic composition, local identities and narrow associative
rewrites; no heartbeat or other resource limit was raised. Sources, five
artifacts per leaf and all four RHTower imports are installed. No full,
umbrella or dependency build ran, and no axiom checks were run. Repository
lint now passes with the full radial join and its imports.

Owned Lean/Lake processes have completed. Scratch files, search outputs
and the isolated audit package/helper were removed; installed proofs and
artifacts remain.

The full radial join below integrates the companion sources
`ThetaCuspHawkingBMTemporalCurrentClearedDensityBound`,
`ThetaCuspHawkingBMTemporalCurrentRadialCutoff` and
`ThetaCuspHawkingBMTemporalCurrentRadialPackage`. The last exposes the
incoming current's endpoint-jet witness, analytic outer integral and
original full radial cutoff limit. The full normalizable join retains
the opposite branch and passed a combined import check before assembly.

## Full normalizable radial current: source evaluation and outer join

The checked full radial join attaches the original normalizable temporal
horizon current to its original outer integral. Its source-evaluated residue is

```
K * normFinitePart(w0) / physicalFundamentalDenominatorSlope,
K = N * (-2*w0*(lambda-2)) * physicalSelfSourceCoefficient(q)
    * fundamentalSourceMoment(w0,s,a) * clearedOnset(s,w0).
```

`ThetaCuspHawkingBMTemporalCurrentFundamentalFactor` is installed and
audited. It evaluates the complete cleared horizon profile as
`K*incomingPairingFactor`, proves uniqueness of its actual two endpoint
coefficients, and evaluates its quadratic finite part as K times the
original incoming norm finite part. The source moment is the original
fixed endpoint pairing; no residue value is assigned.

`ThetaCuspHawkingBMTemporalOppositeOuterCurrent` is also installed and
audited. Its density is the coefficient `-1/(2w*(w-2s))` times the
complete cleared source factor and the original opposite homogeneous
mode. The original connection formula identifies it with
`(R^2-1)*A^0_normalizable - A(w)*(R^2-1)*A^0_incoming`. Uniform source
bounds and the horizon-mode bound centered at -w0 give a common outer
majorant. Spatial continuity, frequency analyticity and dominated Cauchy
integration prove an analytic original opposite outer integral through
w0. The full source, principal terms, lift and source contact are retained.

`ThetaCuspHawkingBMTemporalNormalizableOuterCurrent` proves integrability
of the original normalizable outer current before splitting its integral,
extracts its residue and evaluates its cleared fundamental density as
K times the square of the original normalizable mode. It also proves
`physicalTemporalFundamentalRadialResidue_ne_zero_iff`: the radial residue
is nonzero exactly when K is nonzero. This leaf is installed and audited.

`ThetaCuspHawkingBMTemporalNormalizableRadialJoin` is installed and audited.
Its `physicalNormalizableTemporalCurrent_full_radial_restoration_and_residue`
joins the restored horizon current and original outer integral at the same
negative tortoise cutoff, for every sufficiently small positive cutoff.
It proves the original cutoff limit, integrability of the outer current,
the displayed source-evaluated residue and independence of the joined
numerator from that cutoff.

The two existing horizon-restoration leaves now expose their uniform-jet
witnesses in `physicalTemporalCurrent_horizon_restoration_data` and
`physicalNormalizableTemporalCurrent_horizon_restoration_data`. Their
original public theorem statements are preserved as wrappers. Thus the
coefficient evaluation applies to the same source-derived counterterms;
no second choice of endpoint coefficients is assumed. The original norm
and denominator are nonzero at every physical fundamental frequency.
Nonvanishing of K, full angular/action comparison and Hawking-clock
extinction remain open.

All six affected leaves passed `lake env lean` scratch checks and exact
`lake build <module>` audits. Final audit times: fundamental source factor
52 seconds, opposite outer current 22 seconds, incoming horizon data
6.3 seconds, normalizable horizon data 58 seconds, original normalizable
outer current 74 seconds, full radial join 36 seconds. Each audit built
only its requested leaf against cached dependencies (two Lake jobs).
Four new leaves are wired into RHTower; the two modified leaves retain
their existing imports. No full, umbrella or dependency build was run
by this work. No heartbeat or other resource limit was raised, and no
axiom checks or mathematical computations were run.

The independent incoming-current work now includes
`ThetaCuspHawkingBMTemporalCurrentRadialLaurent`. Its source was inspected;
an untested duplicate incoming-radial draft was discarded and this work
continued with the missing opposite outer contribution. A scratch import
check confirmed that the incoming radial package and normalizable horizon
module can be imported together. The broad moment search and deep
endpoint/source-factorization search inspected candidate lemmas, source
arguments and proposed ingredient sets; the Fokas matrix proposal does
not supply this current's endpoint identity. Retrieval completed with
snapshot coverage and unmeasured semantic coverage. Broad transmission
and factorization arXiv searches did not return verified June–September
2026 matches; the opened [soft-collinear factorization paper](https://arxiv.org/abs/hep-ph/0109045)
is not used as a premise. No computation was run.

### Exact source-moment reduction

The original physical `fundamentalSourceMoment` now has a Lean-checked
polynomial-coordinate evaluation. Set `z=x*(2-x)`, with `0<x<=1`, and write

```
A = (5*s^2+15*s+4)/4,
B = s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4,
H_n(x) = (1-x)^n*(2-x)^(2*s),
I_n = firstEndpointMellin(H_n,1,w),
d = 2*s-w,  e = w+2*s+2.
```

The actual source density times the substitution's Jacobian is exactly
`2*a^2*x^w*(A*H_2(x)+B*H_4(x))`. Both A and B come from the original source.
The original integral above `epsilon*(2-epsilon)` therefore equals the
polynomial integral above epsilon. The counterterm difference is exactly

```
F(0)/(w+1) * epsilon^(w+1)*((2-epsilon)^(w+1)-2^(w+1)).
```

Its last factor is a differentiable endpoint difference. The slope limit
and `Re(w)>-2` prove that the whole difference tends to zero. Compact
bounds on the actual derivatives of H_n prove admission of each moment;
no new regularity hypothesis is supplied for the physical source.
Consequently the proved identity is for the same original finite part:

```
M = 2*a^2*(A*I_2+B*I_4).
```

Integration by parts with the primitive
`x^(w+1)*(1-x)^n*(2-x)^(2*s+1)` retains its upper boundary:

```
n*I_(n-1) + d*I_n - (n+e)*I_(n+1) = -0^n.
e*(e+1)*I_2 = (e+d^2)*I_0+d,
e*(e+1)*(e+2)*(e+3)*I_4 =
  (d^4+(6*e+8)*d^2+3*e*(e+2))*I_0+d*(d^2+5*e+8).
```

In particular, the zeroth recurrence has right side -1. The exact physical
source evaluation is the denominator-cleared identity

```
D*M = 2*a^2*(P*I_0+Q),
D = e*(e+1)*(e+2)*(e+3),
P = A*(e+d^2)*(e+2)*(e+3)
    + B*(d^4+(6*e+8)*d^2+3*e*(e+2)),
Q = d*(A*(e+2)*(e+3)+B*(d^2+5*e+8)).
```

`ThetaCuspHawkingBMFundamentalMomentPolynomial` proves the exact original
source substitution. `ThetaCuspHawkingBMFundamentalMomentCounterterm`
provides the endpoint limit mechanism.
`ThetaCuspHawkingBMFundamentalJacobiMoment` derives moment admission from
its actual core. `ThetaCuspHawkingBMFundamentalJacobiRecurrence` proves
the recurrence and second/fourth reductions.
`ThetaCuspHawkingBMFundamentalSourceMomentTransport` proves
`physicalFundamentalSourceMoment_polynomial` and
`physicalFundamentalSourceMoment_base_period`, for every actual Xi copy,
branch, side and amplitude, without extra physical hypotheses.

All five leaves passed `lake env lean` scratch checks and exact
`lake build <module>` audits. Audit times were 71, 75, 25, 78 and 134
seconds, respectively; each built only its requested leaf against cached
dependencies (two Lake jobs). All five are installed and wired into
RHTower. No heartbeat or other resource limit was raised; no umbrella,
full or dependency build, axiom check or mathematical computation was
run by this work.

`scripts/formal_tools.py lint` passed with existing large-file warnings.

The remaining source problem is nonvanishing or joint survival of the
specific physical family `P*I_0+Q`, together with the actual angular
source factors in K. The base period is a half-interval finite part;
complete-beta nonvanishing does not evaluate it. A concrete next candidate
uses the physical relations `s=2*w+1` or `s=2*w+2`: the common phase then
comes from `x*(2-x)^4`, whose interior stationary point is `x=2/5`.
The corpus theorem `norm_sqrt_mul_besselPhaseIntegral_sub_le` in
`BesselJZeroConstant.lean` supplies an inspected proof mechanism for a
Fresnel main term with an explicit remainder after a quadratic change of
variables. Transferring that mechanism requires bounds for this original
subtracted source, and a range covering the physical frequencies. No
such dominance or source nonvanishing theorem is claimed here. Full
angular/action comparison, Hawking-clock extinction and RH remain open.

Broad incomplete and saddle retrieval and deep endpoint, stationary-phase
and period-nonvanishing requests inspected candidate lemmas, source
arguments and ingredient sets. First-endpoint subtraction and compact
primitive continuity supplied the endpoint proof. The last period search
completed with snapshot coverage (57,084 files, 735,656 declarations),
mostly pending compiler metadata and unmeasured semantic coverage. Its
continued-fraction and Suzuki beta candidates supply no applicable
nonvanishing theorem for this complex half-period. Earlier deep requests
returned partial auxiliary queries. Broad monodromy/holonomic searches
reached the September 2026
[line-arrangement monodromy paper](https://arxiv.org/abs/2609.06416) and
the August 2026 [multivariable monodromy paper](https://arxiv.org/abs/2608.26087).
Their abstracts were inspected; neither is used as a proof premise.

### Intermediate-height source and retained horizon contact

Two analytical conjectures now have Lean proofs: boundary recovery from
the original moments, and all-height survival of the original intrinsic
horizon contact. Both retain the prescribed endpoint subtraction.

Write `I_n=fundamentalJacobiMoment n w s`, `d=2*s-w`, and
`e=w+2*s+2`. The admitted first, second and third recurrences give

```
2*I_0 = (d^2+5*e+8)*I_2 - (e+2)*(e+3)*I_4,
(e+d^2)*(e+2)*(e+3)*I_4
  - (d^4+(6*e+8)*d^2+3*e*(e+2))*I_2 = 2*d.
```

The second identity holds whenever `Re(w)>-2` and `w+1!=0`, without
dividing by `e` or `e+1`. Its norm gives a lower bound for a weighted
sum of the two moment norms. At each of the four physical branch/side
choices, `d!=0`, so `I_2!=0` or `I_4!=0`. The mathematical work still
needed for this survivor is identification of independent retained
physical projections detecting those moments: the identity alone does
not exclude cancellation in the specified combination `A*I_2+B*I_4`.

For the actual true/true choice, set `v=w+1`, so
`-1/2<Re(v)<0`. The original endpoint polynomial is

```
E(v)=30*v^4+81*v^3+80*v^2+19*v-6=4*(A+B),
fundamentalSourceCore(w,s,a,0)=2^(2*s-w)*a^2*E(v)/4.
```

Lean proves `E(v)!=0` on the entire closed strip
`-1/2<=Re(v)<=0`, with no restriction on `Im(v)`. Put `t=-Re(v)`
and `y=Im(v)`. When `y!=0`, the imaginary zero equation gives
`(81-120*t)*y^2=19-160*t+243*t^2-120*t^3`.
The right side is at most `19-(137/2)*t`; its nonnegativity gives
`t<=1/3`, then `y^2<=1/2`. On that interval
`-180*t^2+243*t-80<=-19`. Thus the imaginary correction to the real
polynomial, `y^2*(30*y^2-180*t^2+243*t-80)`, is nonpositive,
whereas the existing real coefficient bounds give `E(-t)<=-15/4`.
The case `y=0` follows from the same real bound. The proof uses factored
polynomial inequalities and restricted `nlinarith only` inputs.

With the unchanged angular-gradient prescription
`K=reducedGreenGradient(physicalRadialFrequency(q),s,1)`, Lean identifies
the original `sourceRemainder` at the horizon with this endpoint core.
Consequently, for every physical copy and every nonzero amplitude,

```
intrinsicContact = fundamentalSourceCore(w,s,a,0)/(2*(w+1)) != 0,
incomingResponseSlope(s,a,1,K,w)
  = intrinsicContact * continuedOnset(s,w),
incomingResponseSlope(s,a,1,K,w)=0 iff continuedOnset(s,w)=0,
(eventually as b tends to 0 from above,
  incomingSourceTransport(s,chi,a,1,K,w,b)!=0)
  iff continuedOnset(s,w)!=0.
```

The last equivalence concerns the existing analytic continuation of the
original Green-quotient derivative and remains valid at the target
connection zero. Its reverse direction uses the admitted horizon limit
and the nonzero slope; its forward direction retains the exact onset
factor in the transport formula. All-height intrinsic contact
cancellation is therefore closed. The unchanged onset, identification
with the full retained physical action, and intermediate-height total
source-moment cancellation remain open. Contact survival does not by
itself prove nonvanishing of the total moment or its QNM residue.

Three leaves passed scratch checks and exact leaf audits, then were
installed with their audited artifacts and wired into the umbrella:
`ThetaCuspHawkingBMSourceEndpointPolynomial` (31 seconds),
`ThetaCuspHawkingBMFundamentalBoundaryRecovery` (9.6 seconds), and
`ThetaCuspHawkingBMPhysicalSourceContactSurvival` (269 seconds).
Each audit built only its named leaf and reported two jobs. No heartbeat
or other resource limit was raised; no umbrella build, dependency rebuild,
axiom check or mathematical computation was run. The frontier map and
universal STATUS remain unchanged.

Broad contiguous and exact OR Casoratian/Wronskian searches, followed by
deep moment-system and source-contact method requests, inspected
candidate lemmas, source arguments and ingredient sets. All four
requests returned `partial=false`; the latest snapshot covered 57,158
files and 737,205 declarations. Most compiler metadata was pending and
semantic coverage was unmeasured. Second-kind moment Wronskians suggested
boundary recovery; their positivity assumptions were not transferred to
these complex moments. The exact original recurrences supplied the
proof above.

A broad arXiv biorthogonality search reached September 2026 papers on
[radial potential-density bases](https://arxiv.org/abs/2609.04012),
[boundary control of damped beams](https://arxiv.org/abs/2609.07806), and
[non-Hermitian Hawking analogues](https://arxiv.org/abs/2609.05632).
Their abstracts were inspected. Boundary-adapted combinations and
retained modal projections are candidate mechanisms to investigate;
none of these papers supplies a proof premise here.

The next onset conjecture can be stated for the exact existing pulse
transform: `onsetPulseTransform(-lambda)!=0` at
`lambda=3-(5/2)*q`, whose real part lies in `(1/2,3)`.
The existing integration-by-parts theorem identifies this transform with
`lambda*continuedOnset(s,w)`. Broad Laguerre/Hurwitz retrieval and a
single-term `smoothTransition` search recovered the original pulse
identity, real-exponent positivity and isolated-zero theorems, but no
applicable zero-free theorem on this complex curve. A possible stronger
target is a real-zero theorem for the centered Fourier transform of the
specified transition derivative; that target is an unproved conjecture.
No adjustable onset duration or new kernel is substituted.
These two additional searches returned `partial=false` with a snapshot
covering 57,202 files; semantic coverage remained unmeasured.

The formal lint run reported one error outside these three leaves:
`GaloisForLFunctions.HTGeometry.InversePowerCancellation` was unreachable
from its theorem-area umbrella. It also reported existing large-file
warnings. No error was reported in the new HB leaves; the unrelated
module was not edited or rebuilt.

### Fixed onset on the actual overtone ladder

The current analytical attack retains the prescribed unit-duration
onset and varies only the original physical QNM overtone. The exact
formula gives `w_n=w_0-2*n`, hence
`clearedOnset(s,w_n)=onsetPulseTransform(2*s-w_0+2*n)`.
`ThetaCuspHawkingBMFixedOnsetRealTilt` proves that, for every fixed
complex `z`, this original pulse transform at `z+2*n` is nonzero for
all sufficiently large `n`. Its scratch check and exact module audit
passed with default heartbeats; the exact audit took 24 seconds.
`ThetaCuspHawkingBMFixedOnsetOvertoneSurvival` proves the physical
corollary: for every original Xi copy there is one `N` such that, for
every `n>=N` and both source-rate and QNM-side choices, the original
`clearedOnset` and `continuedOnset` are nonzero. Its scratch check and
exact module audit passed; the latter took 21 seconds. Both leaves
are installed with their audited artifacts and wired into `RHTower`.
No dependency or umbrella build, heartbeat increase, or axiom query
was used. The formal lint gate passed, with existing large-file
warnings. Integral measures and integrand forms are explicit, and
the phase estimates use restricted arithmetic hypotheses. A slow
scratch initialization was traced to import loading, before tactics;
the physical leaf imports 4,328 cached project dependencies in its
isolated audit.

The paper mechanism is endpoint concentration. Write
`p(u)=deriv Real.smoothTransition u`, so `p>=0`, its total integral is
one, and every interval ending at one has positive mass. For fixed
imaginary part, choose a terminal interval where the phase, rotated by
its endpoint value, has real part at least one half. A smaller terminal
interval gives a positive lower bound with a strictly larger exponential
rate than the entire possibly negative earlier contribution. This yields
strict positivity of a rotated real part at all sufficiently large real
tilts. It changes no onset profile, clock duration or Xi copy.

The remaining physical obligation is to establish nonzero original
radial/left-QNM coupling on a compatible high-overtone subsequence and
retain all endpoint subtractions there. Fundamental-mode contact
survival alone does not identify that higher-overtone coupling.

The current radial conjecture uses the terminating polynomial of the
original plus branch. Put `w_n=w_0-2*n`, `w_0=-3/2-I*chi`,
`t=1-z`, `A=fundamentalMomentConstant s`, and
`B=fundamentalMomentQuadratic w_0 s`. The source coefficients `A,B`
remain fixed when `n` changes. Direct substitution of the actual outer
Gauss parameters gives
`P_n(t)=₂F₁(-n,n+w_n+3/2;3/2;t)`.
The radial source density is therefore proportional to
`t^(1/2)*(1-t)^w_n*(1+sqrt(t))^(2*s-w_n)*(A+B*t)*P_n(t)`.

The verified Rodrigues identity is
`(3/2)_n*t^(1/2)*(1-t)^w_n*P_n(t)
 = D_t^n[t^(n+1/2)*(1-t)^(n+w_n)]`.
`ThetaCuspHawkingBMJacobiRodrigues` proves the general weighted derivative
and its iterated identity from the actual Gauss ODE. Its scratch check
and exact leaf audit passed (182 seconds). The proof isolates power
derivative values before polynomial normalization and uses default
resource limits. `ThetaCuspHawkingBMOvertoneSourceRodrigues` identifies
both original QNM ladders with that terminating factor and proves the
exact original source density identity, retaining the fixed angular
gradient, amplitude and arbitrary original onset factor. Its scratch
check and exact leaf audit passed (105 seconds). Both leaves are
installed with audited artifacts and wired into `RHTower`; dependency
sources and umbrella builds were excluded from the audits.

The identities hold at every interior radius. Higher-order endpoint
restoration and overtone-tail nonvanishing are not yet Lean theorems.
Neither generic polynomial completeness nor a positive moment measure
has been identified with this pairing.

### Unproved auxiliary overtone-tail survival approach

The recurrence attack keeps the original source coordinate `u=sqrt(t)`.
With `mu=(1-u)^w0*(1+u)^(2*s)`, set
`L p=(1-u^2)*p'+(2*s-w0-(w0+2*s+2)*u)*p`.
Then `(mu*(1-u^2)*p)'=mu*L p`. For `p_k=(1-u)^(-k)`,

```
L p_k=2*(k-w0-1)*p_k+(w0+2*s+2-k)*p_(k-1).
```

The cutoff integral has the upper primitive minus `1`; its canonical
finite part therefore predicts the affine pole-moment recurrence
`2*(k-w0-1)*J_k+(w0+2*s+2-k)*J_(k-1)=-1`.
The primitive's endpoint powers have nonzero imaginary exponent, so
none contributes a constant term. The missing part of this approach is
an actual overtone block recovering that nonzero boundary: an abstract
moment recurrence does not prove source-pairing survival. No such block
determinant has been established.

The alternative overtone argument sums the Rodrigues kernels. Strip only
the external amplitude and onset from the original source pairing:

```
R_n=FP integral_0^1 t^(1/2)*(1-t)^(w0-2*n)
      *(1+sqrt(t))^(2*s-w0+2*n)*(A+B*t)*P_n(t) dt,
S(lambda)=sum_n (3/2)_n/n! * R_n * lambda^n.
H(t)=t^(1/2)*(1-t)^w0, g(t)=t/(1-t).
```

For each interior t, Cauchy's coefficient formula at the nearby root
`T=t+x*g(T)` gives the local analytic identity
`sum_n x^n/n!*D^n[H*g^n](t)=H(T)/(1-x*g'(T))`.
Set `x=lambda*(1+sqrt(t))^2`. Then

```
T^2-(1+t-lambda*(1+sqrt(t))^2)*T+t=0,
Delta=(1+sqrt(t))^4*(1-lambda)*(((1-sqrt(t))/(1+sqrt(t)))^2-lambda),
H(T)/(1-x*g'(T))=sqrt(T)*(1-T)^(w0+1)/sqrt(Delta).
```

This local identity alone does not justify integrating the infinite sum
through the horizon. The proposed identification uses one fixed keyhole
contour around `u=1`, based at `u=0`. Every overtone has the same horizon
monodromy `exp(2*pi*I*w0)`, because its exponent differs by `-2*n`.
On a fixed contour away from the horizon the kernel series can be summed
uniformly. Proving its normalized contour integral equals the original
canonical finite parts is a required step, not an assumed interchange.

The exact algebraic substitution is particularly restrictive. Put
`beta=sqrt(1-lambda)` and `v=sqrt(T)`. The chosen local branch gives

```
u=v*(beta-v)/(1-beta*v),
1+u=(1-v^2)/(1-beta*v),
sqrt(Delta)=beta*(1-v^2)*du/dv.
```

The transformed generating integrand is therefore

```
F_beta(v)=(2/beta)*v^2*(beta-v)*(1-v^2)^(2*s)
           *(1-beta*v)^(w0-2*s-1)
           *[A+B*v^2*(beta-v)^2/(1-beta*v)^2].
```

The lifted contour surrounds `v=1` and `v=1/beta`, excluding `v=-1`.
An endpoint-preserving decomposition into `0..1` and `1..1/beta` periods
is the next exact identity to establish. With one consistent side of
the cuts, its second-period multiplier is predicted to be

```
kappa=exp(-2*pi*I*s)
       *(1-exp(2*pi*I*(w0-2*s-1)))/(1-exp(2*pi*I*w0)).
```

The orientation and normalization must be checked against the original
contour before this is treated as a proved physical formula.

For the original `branch=true, side=true` choice,
`s=q-2`, `w0=-s/2-2`, and direct algebra gives
`B=3*s*(s-1)*(s+2)*(5*s+8)/32`, which is nonzero because s is nonreal.
Scaling `y=beta*v` in the second period predicts the concrete limit

```
beta^(4*s+9)*S(1-beta^2)
  -> -2*kappa*B*Gamma(4*s+8)*Gamma(w0-2*s-2)
                   /Gamma(w0+2*s+6).
```

All three Gamma arguments are nonreal on this physical channel; the
two monodromy denominators/numerators are also nonzero. Thus the proposed
limit is explicitly nonzero. Moreover `0<Re(4*s+8)<4`. A polynomial S
would give limit zero, so this exact limit would directly disprove an
eventually zero source-pairing tail and meet the previously established
cofinite onset-survival tail.

The analytical estimate to prove keeps both endpoint subtractions.
After scaling, the B term tends to
`-2*B*y^(4*s+7)*(1-y)^(w0-2*s-3)`. The moving lower-endpoint contribution
is of order `beta^(4*s+8)` after normalization, and the fixed-endpoint
period is of the same vanishing order. The A term is lower order.
At `y=1`, two Taylor subtractions suffice throughout the physical strip;
at the moving `y=beta` endpoint, four suffice for the exponent `2*s`.
Uniform bounds for those subtracted remainders and the contour identity
remain to be proved. The limit, tail survival, complete retained action,
fixed-clock extinction and RH are not yet established in Lean.

Current corpus retrieval also used single-word Gegenbauer, Bürmann and
contiguous searches, broad Bernstein/Bessel, holonomic/telescoping and
finite-part searches, and deep derivative-transfer, recurrence-recovery
and Abel-jump mechanism requests. Returned candidate lemmas, source
arguments and proposed ingredient sets were inspected. Some broad and
deep requests were partial; the completed recurrence snapshots covered
57,228 files and 738,760 declarations with mostly pending compiler
metadata. The lexical contiguous search exposed the finite Pfaff and
Jacobi coefficient proofs in `SemilocalDiagonalPfaffTransformation` and
`SemilocalBoostContiguousRelations`. They do not yet supply this physical
generating period or its endpoint limit.

A broad resurgence search reached the June 2026
[Weak-Strong Resurgence Duality](https://arxiv.org/html/2606.26637v1#S8)
Mellin-transform section, which relates different asymptotic expansions
through explicit Gamma factors, and the April 2026
[Resurgence of high-energy string amplitudes](https://arxiv.org/html/2604.07444v1#S3),
whose period difference systems are obtained by integration by parts.
These supply comparison methods; no theorem from either paper has been
substituted for the required physical contour identity or uniform limit.

Broad and deep corpus searches covered Hermite–Biehler, Lee–Yang,
Sturm, oscillation, overtones, endpoint concentration, Rodrigues,
moment recurrences, Mellin subtraction and contiguity. Candidate
statements and source arguments were checked for matching premises.
The moment-tail request was partial (unfinished asymptotic query and
reranking); the later subtraction and contiguity requests completed.
The latter snapshots covered 57,213 files and 738,617 declarations,
with most compiler records pending. Suggested ingredient sets remain
unverified. In particular, the Hurwitz order-independence proof and
the BM Gauss coefficient coboundaries supply methods, not the missing
physical endpoint or coupling theorem.

### Monotone-phase source survival

The source-survival proof uses the actual `branch=true, side=true`
choice: `w=-1-q/2`, `s=q-2=-2*w-4`, hence `-3/2<Re(w)<-1`.
The original polynomial moments become

```
I_n = FP integral_0^1 [x/(2-x)^4]^w * (1-x)^n/(2-x)^8 dx.
phi=x/(2-x)^4, p=phi/phi'=x*(2-x)/(2+3*x).
T f=(p*f)'-f
   =x*((2-x)/(2+3*x)*f'-4*(4+3*x)/(2+3*x)^2*f).
```

The proved integration-by-parts identity keeps the original endpoint
subtraction and has a remainder with an explicit factor x:
`(w+1)J(f)=f(1)/5-J(T f)`. On the physical strip, the remainder is
uniformly integrable against `x^(-1/2)`. For
`f_n=(1-x)^n/(2-x)^8`, the first n upper endpoint terms vanish, and
`T^n f_n(1)=(-1)^n*n!/5^n`. This gives

```
(w+1)^(n+1)*I_n = n!/5^(n+1) + O(1/abs(w+1)).
```

With `v=w+1`, exact source coefficients simplify to
`A=5*v^2+(5/2)*v-3/2` and
`B=(15/2)*v^4+(81/4)*v^3+15*v^2+(9/4)*v`.
For unit amplitude, the complete source now has a Lean-proved bound
`norm(v*(v*M-172/625)) <= K`, with one nonnegative K uniform on the strip
when `norm(v)>=1`. The exact physical identification retains the original
endpoint subtraction. The installed source-survival theorem proves

```
exists H>0, forall q:XiZeroCopy, H<=abs(Im(q)) -> forall a:Complex,
  (86/625)*norm(a)^2 <= norm((w+1)*fundamentalSourceMoment(w,s,a)).
```

Consequently every nonzero original amplitude has a nonzero source moment
in this channel above H. The proof chooses
`H=2*(1+2*K/(172/625))`; no numerical evaluation is needed. Bounded-height survival,
angular factors and affine Xi collisions, fixed onset survival, the full
retained action and Hawking-clock extinction remain open; RH is unproved.

To avoid expanding high rational derivatives, the exact weights
are `T^j f_n=P_j(x)/((2-x)^8*(2+3*x)^(2*j))`, with

```
P_0=(1-X)^n,
P_(j+1)=X*((2-X)*(2+3*X)*P_j' +(6*(j+2)*X-12*j)*P_j).
```

Every positive-order numerator has the required factor X. Seven new leaves
are installed and wired after scratch checks and exact leaf audits:
`ThetaCuspHawkingBMNonstationaryWeight` (60 seconds),
`ThetaCuspHawkingBMNonstationaryMoment` (22 seconds),
`ThetaCuspHawkingBMNonstationaryIntegrationByParts` (24 seconds), and
`ThetaCuspHawkingBMNonstationaryPolynomial` (7 seconds),
`ThetaCuspHawkingBMNonstationaryAsymptotic` (31 seconds),
`ThetaCuspHawkingBMPhysicalNonstationarySource` (143 seconds), and
`ThetaCuspHawkingBMFundamentalSourceSurvival` (18 seconds). They prove the
rational derivative recurrence, original finite-part recurrence, uniform
remainder admission and bound, exact upper endpoint coefficients, uniform
leading-term error bounds, identification with the original source, and
the uniform high-height lower bound and nonvanishing theorem.
The first isolated audit visited cached dependency jobs and printed one
built module; subsequent audits reported two jobs each. No umbrella or
full build was run. No heartbeat or other resource limit was raised.
No axiom checks or mathematical computations were run. The frontier map
and universal STATUS remain unchanged.

Formal lint passed with existing large-file warnings after restoring the
missing umbrella import for the already compiled
`ThetaCuspHawkingBMScalarJetQuadraticEinstein`. Its source was unchanged;
no re-audit or umbrella build was run.

Broad Wronskian retrieval and deep Stieltjes and endpoint-asymptotic
requests inspected candidate lemmas, source arguments, proof ideas and
ingredient sets. The finite-interval integration-by-parts mechanism led
to the retained-boundary recurrence above. The later inverse-density
request returned partial results with reranking unfinished; snapshot
coverage was 57,113 files and 735,918 declarations, mostly pending compiler
metadata and unmeasured semantic coverage. Exact phrase retrieval for
"Lagrange inversion" found no hits. Broad Pick/univalence arXiv searches
reached July 2026 papers on
[harmonic-map Landau bounds](https://arxiv.org/abs/2607.04377) and
[directed univalence](https://arxiv.org/abs/2607.02420); their abstracts
were inspected and neither is used as a premise.

For the remaining bounded-height problem, an analytical candidate moves
the frequency polynomials onto one density. In the phase coordinate
`z=x/(2-x)^4`, set

```
rho_n(z)=(1-x(z))^n/((2-x(z))^3*(2+3*x(z))),
theta=z*d/dz,
R=(5*theta^2-(5/2)*theta-3/2)rho_2
  +((15/2)*theta^4-(81/4)*theta^3+15*theta^2-(9/4)*theta)rho_4.
```

The endpoint values are `R(0)=-3/32` and `R(1)=86/625`.
The phase-coordinate form of the reduction is
`v*M/(2*a^2)=86/625-integral_0^1 z^v*R'(z) dz` for nonzero a.
It follows on paper by retaining the phase-change counterterm and using
the second/fourth endpoint vanishing when moving the polynomials across
the Mellin integral. The equivalent fixed-weight reduction in the original
x coordinate is now formalised below; no inverse phase coordinate is
needed in Lean. The global target is excluding the value `86/625` from that
integral for `-1/2<Re(v)<0`, `Im(v)!=0`; no density sign or Stieltjes
representation is assumed. The deep inverse-density search returned
Lagrange interpolation rather than inversion candidates, so it supplies
no proof of this target.

The current analytical attack removes every frequency polynomial before
applying a nonvanishing argument. Write `P_nk=nonstationaryPolynomial n k`
and `D=2+3*X`, and define the single fixed polynomial

```
N=5*D^4*P_22-(5/2)*D^6*P_21-(3/2)*D^8*P_20
  +(15/2)*P_44-(81/4)*D^2*P_43+15*D^4*P_42-(9/4)*D^6*P_41.
```

The identities `M=2*a^2*J(W(N,8))` and
`v*M=2*a^2*(86/625-Dsource(w))` now pass Lean for the original physical
source, where `Dsource(w)=J(W(Step(N,8),10))`. The last pairing is an
ordinary absolutely convergent integral for `Re(w)>-2`, with one
frequency-independent rational weight. The fixed polynomial satisfies
`N(0)=-384`, `N(1)=268750`, and `W(N,8,1)/5=86/625`.
The exact endpoint identity is `Dsource(-1)=86/625+3/32`.
One common `x^(-1/2)` majorant proves continuity of Dsource on the closed
physical strip, including its subtracted-pole endpoint.

### Complete-source real coercivity and a uniform complex band

Transferring the frequency polynomials gives the fixed-weight reduction
above, but a sign for its single density has not been established.
The successful positive replacement compares the admitted second and
fourth remainder kernels. For real `-3/2<=u<=-1`, put

```
kappa=x^u*(2-x)^(-4*u),
g2=x*(1-x)*(8-4*x+6*x^2)/((2-x)^8*(2+3*x)^2),
g4=4*x*(1-x)^3*(4+x)/((2-x)^8*(2+3*x)^2),
U2=integral_0^1 kappa*g2, U4=integral_0^1 kappa*g4.
```

Both integrals are admitted for every `u>-2`. Lean proves `U2>0` and
`0<=U4<=2*U2`; the comparison follows from the positive numerator
`4*x^2*(1-x)*(5+x-x^2)` of `2*g2-g4`. For the complete source
coefficients, Lean proves `A<=-3/2`, `B<=9/16`, hence

```
A*U2+B*U4 <= -(3/8)*U2 < 0.
```

The coefficient proof factors B as
`(3/4)*t*(1-t)*(5*t-1)*(3-2*t)`, with `t=-(u+1)` in `[0,1/2]`.
The original endpoint recurrence identifies this combination with
`(u+1)*J(W(N,8))` for `u<-1`. Consequently
`Re(Dsource(u))>86/625` throughout the closed real interval; the exact
endpoint value handles `u=-1` separately.

Applying the corpus's `CompactPatchGenericity` theorem to this strict gap
and the admitted integral's continuity gives a Lean-proved `delta>0`:

```
-3/2<=Re(w)<=-1, abs(Im(w))<=delta  ->  Dsource(w)!=86/625.
```

The physical identification uses `w=-1-q/2` and proves

```
exists h>0, forall q:XiZeroCopy, abs(Im(q))<=h -> forall a:Complex,
  a!=0 -> fundamentalSourceMoment(w,physicalRate(q,true),a)!=0.
```

Here `h=2*delta`. Together with the existing high-height source theorem,
this supplies uniform low-height and high-height survival ranges. No
comparison making these ranges cover all heights has been proved.
Intermediate-height cancellation, the full angular/retained-action
identification, fixed onset survival, Hawking-clock extinction and RH
remain open. Ordinary polynomial-moment completeness still lacks an
identification with the actual higher-QNM pairings.

The proof uses factored weight recurrences and separate algebra,
integrability, coercivity and compactness leaves. No heartbeat or other
resource limit was raised. All seven new leaves passed scratch checks
and exact audits, and are installed with audited artifacts and wired:
`ThetaCuspHawkingBMNonstationaryMomentAlgebra` (37 seconds),
`ThetaCuspHawkingBMFixedSourcePolynomial` (127 seconds),
`ThetaCuspHawkingBMRealSourceWeights` (40 seconds),
`ThetaCuspHawkingBMFixedSourceDefect` (52 seconds),
`ThetaCuspHawkingBMRealSourceCoercivity` (71 seconds),
`ThetaCuspHawkingBMSourceRealBand` (17 seconds), and
`ThetaCuspHawkingBMPhysicalFixedSource` (23 seconds).
Only the requested leaf was reported built in each audit; the defect
audit visited cached dependency jobs, while the others reported two jobs.
No full or umbrella build, axiom check, or mathematical computation ran.
The frontier map and universal STATUS remain unchanged.

The final lint run reports no error for the seven new leaves. It still
reports unreachable concurrently added modules `MaassCircleKernel`,
`MaassCircleTransfer`, and `CompactSmoothParameterIntegral`, alongside
existing large-file warnings. Missing imports for the already compiled
`ThetaCuspHawkingBMScalarJetEntries`, `SmoothCylinderKernel`, and
`SmoothCylinderIntegral` were restored without changing their sources or
rebuilding them. No umbrella build was run.

Broad Hurwitz, contiguous and overtone retrieval and deep density,
completeness, Xi-height, compactness and moment-ratio searches inspected
candidate lemmas, source arguments and proposed ingredient sets.
`CompactPatchGenericity` supplied the applicable uniform-band mechanism.
The final moment-ratio request completed with snapshot coverage of
57,137 files and 736,578 declarations; compiler metadata remains mostly
pending and semantic coverage unmeasured. Its proposed differential-adjoin
ingredient set concerns field generation, not a differential adjoint
identity. The inspected `PositiveSourceQuadraticStability` theorem requires
a transverse sector inequality; that inequality has not been established
for this original source, so it supplies no middle-band conclusion yet.
Broad passivity and total-positivity arXiv retrieval reached the July 2026
[impedance-passive stability paper](https://arxiv.org/abs/2607.01861) and
August 2026 [reciprocity paper](https://arxiv.org/abs/2608.30778).
Their abstracts were inspected; neither is used as a proof premise.

## Original action cyclicity with its boundary divergence

**Status:** paper proof closed; both leaves passed scratch Lean and exact
leaf audits with default limits. Only the new geometry leaf (84 seconds)
and new physical leaf (65 seconds) were built; dependencies were reused
from cache. Both are wired into their umbrellas; no umbrella build ran.
The formal lint gate passed; it reported existing large-file warnings.

Formal statements:
- `HTGeometry/CoordinateEinsteinCyclicAction.lean`:
  `paired_cyclicity_defect`, `cubicAction_eq_density_third`,
  `cubicAction_cyclic` in `HTGeometry.EinsteinCyclicVariation`.
- `RHTower/ThetaCuspHawkingBMCyclicActionBoundary.lean`:
  `metricFamily_jet`, `physical_cubicAction_cyclic`,
  `physical_cubicAction_eq_density_third` in `RHTower.D4BMCyclicAction`.
  The physical theorems have no supplied regularity, symmetry,
  nondegeneracy, field-equation or boundary-cancellation premises.

For the complete metric jets put `G(a)=J+sum_k a_k U_k` in jet
coordinates, `w(a)=exp(log(det(G(a))/det(J))/2)`, and

```
L(a)   = w(a) * (R(G(a))-2 Lambda)
P_k(a) = w(a) * sum_ij (G(a)^(-1) U_k G(a)^(-T))_ij
                         * (Einstein(G(a))+Lambda G(a))_ij
D_k(a) = w(a) * EinsteinActionBoundary.divergence(G(a),U_k).
```

The original Einstein--Hilbert first variation gives
`partial_k L=-P_k+D_k` near zero. Nondegeneracy puts the determinant
ratio near `1` in one fixed logarithm branch. Rational curvature and
this density are smooth there. Differentiating twice and commuting
mixed derivatives proves

```
partial_i partial_j P_k - partial_i partial_k P_j
  = partial_i partial_j D_k - partial_i partial_k D_j,
C_ijk := partial_i partial_j P_k - partial_i partial_j D_k
       = -partial_i partial_j partial_k L.
```

All values here are at zero. Consequently `C_ijk=C_ikj`; the retained
action has cubic symmetry without assuming a vanishing boundary flux.
This is a positive identity from the original action, not a proof that
the bulk source alone has the required cyclic pairing. No route is
retired by this result.

For the physical specialization, `J` is the actual BM background jet and
`U_k` is the actual complete spatial jet of
`physicalPerturbation(q_k,b_k,aS_k,aV_k)`. All three Xi occurrences,
branches, and scalar/vector amplitudes are independent. Background
nondegeneracy follows from the explicit exterior metric; symmetry of
every mode and its first derivatives follows from the original
covariant metric expression. The actual metric family is formed
before spatial differentiation; its field-to-jet identity retains
every ordered second coordinate derivative.

**Consequences for the full proof chain:** this supplies a local
variational identity for the retained source, before projection onto
radial or left-QNM channels. It does not yet supply the abstract
Peierls receiver's `hcyclic`: that receiver needs one common source
map, pairing and causal propagator, including sourced response fields.
Identifying the second variation of `P` with a frozen pairing of the
quadratic residual still requires discharging the background and
linearized residual terms. Integrating `D` requires the original
volume measure, all boundary components and the common-cutoff limit.
The formal divergence has not been replaced by a bare radial endpoint.

Two closing possibilities remain in view. If the complete physical
incidence equals the original normalized BM candidate, the existing
source-reflection/Peierls receiver can force the critical line. If the
boundary contribution survives in that incidence, its value also
belongs in the proposed fixed-clock observable; extinction must be
proved for that same observable. Neither incidence identification,
causal reciprocity, channel nonvanishing, extinction nor RH is proved
by the local cubic identity.

Broad/deep/method corpus retrieval found the original EH variation and
actual Einstein Hessian symmetry. Some deep requests returned partial
coverage; source statements were inspected and candidate use was
checked in Lean. Broad arXiv searches for `variational` and
`transgression` found [Monroy, arXiv:2606.08659](https://arxiv.org/abs/2606.08659)
and [Bildhauer--Fuchs, arXiv:2608.01105](https://arxiv.org/abs/2608.01105).
Their abstracts did not provide the missing gravitational pairing or
extinction theorem; no mathematical claim from them enters the proof.

## Original on-shell quadratic pairing and boundary assembly

**Status:** both geometric and physical source reductions are paper-proved,
scratch-checked and leaf-audited with default Lean limits. Exact audits built
only the new geometry leaf (13 seconds) and physical leaf (54 seconds),
reusing cached dependencies. Both umbrella imports are wired; no umbrella
build ran. Formal lint passed with existing large-file warnings. RH and
global physical incidence remain open.

For the same complete family `G(a)`, let `E_rs(a)` be its original
cosmological Einstein residual and let `W_k,rs(a)` be its original
volume-weighted raised test coefficient. The exact derivative identities are

```
partial_k E_rs(a) = DEinstein_rs(G(a))[U_k] + Lambda*(U_k)_rs,
partial_i partial_j E_rs(0) = D²Einstein_rs(J)[U_i,U_j],
partial_i partial_j sum_rs W_k,rs(a)*E_rs(a) at 0
  = sum_rs W_k,rs(0)*D²Einstein_rs(J)[U_i,U_j]
```

when the actual background residual and first residuals vanish. The proof
retains all four Leibniz terms. The extra three terms vanish because they
multiply `E(0)`, `partial_i E(0)` or `partial_j E(0)`, rather than because
the volume or inverse metric is held constant during variation. The
cosmological term contributes at first order and vanishes at second order
because the metric family is affine.

`HTGeometry/CoordinateEinsteinOnShellPairing.lean` contains
`residual_first`, `residual_second` and `bulk_second_eq_hessian` in
`HTGeometry.EinsteinOnShellPairing`. Its scalar product lemma records the
precise residual conditions that permit freezing a varying coefficient.
The geometric statement applies to arbitrary complete jet directions;
it does not restrict future source, test or response directions to one
angular parameter.

The concrete application uses the actual BM vacuum and the previously
proved full physical mode equations to discharge every residual premise.
The source convention matters: the original quadratic Taylor source is
one half the Einstein Hessian. Thus, writing `B_ijk` for its paired
coefficient, the target identity is

```
B_ijk - B_ikj
  = (partial_i partial_j D_k - partial_i partial_k D_j)/2.
```

The diagonal is also compared with the actual field-source coefficient
`iteratedDeriv 2 (D4BMActualMetricSource.source ...) 0 / 2`, fixing this
normalization independently. This Taylor factor is distinct from a
causal half-jump convention.

`RHTower/ThetaCuspHawkingBMOnShellCyclicSource.lean` proves
`physical_bulk_second_eq_hessian`,
`quadraticPairing_diag_eq_sourceCoefficient`,
`physical_quadratic_cyclicity_defect` and
`physical_quadratic_with_boundary_cyclic` in
`RHTower.D4BMOnShellCyclicSource`. These physical statements supply their
own background and linearized equation proofs, using three independent
Xi occurrences, branches and scalar/vector amplitudes.

For the causal construction, a forced response is not itself covered by
the homogeneous first-residual condition. The needed producer is the
original homogeneous equation for the retarded--advanced difference,
with the same full source and every contact retained. Terms involving a
first residual must remain until that producer is proved; the on-shell
identity is not permission to discard them on each forced branch.

The concrete hard producer is a pair of full metric corrections satisfying
the original component equations `L(k_ret)=L(k_adv)=-B(h,h)`, including
the source contacts and all independent scalar/vector channels. A solved
projected scalar wave equation alone does not establish those equations.
Their proved common source would give `L(k_ret-k_adv)=0`, placing the
actual causal difference within the reduction above. The scalar-stream
master-row identities are ingredients for constructing that producer,
not a substitute for constructing the corrections.

**Boundary assembly and whole-chain consequences:** broad Green and
method searches found exact paired modular side/arc cancellation in
`ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation.lean`. Its
parameters explicitly require `Re(s)>1`; it is not yet a producer for
the physical Xi parameters. A continuation or direct full-field
identification must be proved before using that cancellation.

A different, physically specialized result is available in
`ThetaCuspHawkingBMQuarticTestedNativeCurrent.lean`: the full scalar-tested
centered response current has zero upper trace under every complex height
power. Its exact improper integral retains the negative lower current.
The candidate assembly therefore keeps the original lower endpoint,
mean terms and contacts while comparing the tested native current with
the Einstein boundary quantity above. Neither scalar identity alone
identifies the full nine-channel action, its physical left reader, or
the causal inverse.

The next decisive test is equality with the original global
causal/left-QNM pairing, with those terms retained on one common cut.
A surviving boundary term changes both the candidate incidence and the
observable whose fixed-clock extinction is required. Source reflection,
local cubic symmetry and local Hessian reduction do not imply that
incidence or extinction.

Broad arXiv searches for `corner`, `interface`, `gluing` and `cobordism`
were also used. The August papers
[Jia--Tan, arXiv:2608.05071](https://arxiv.org/abs/2608.05071) and
[Bais--Kjuchukova, arXiv:2608.07788](https://arxiv.org/abs/2608.07788)
concern boundary-defect algebras and branched-cover cobordism respectively.
Their inspected abstracts supply no theorem about this Einstein pairing;
no claim from them is used in the formal proof. Corpus deep requests
returned partial coverage; applicable source statements and method
arguments were inspected and their uses checked in Lean.

### Sourced scalar-stream reconstruction

The current target is a converse to the original master-row identity:
recover full metric amplitudes from a sourced master solution and prove
every original Einstein row, before imposing retarded/advanced domains.
Writing `f=r²−1`, the code's master is
`M=r F0/f−f F1/s−rf F2+4rH`. Its `F1` term has no extra factor `r`.
For original row values `T=E_TF`, `B=E_TR`, `D=E_T`, direct elimination gives

```
(2−μ)H = fD/s +(μ/2−f)T−frT' +fM'/2 +frB/(2s)−μM/(4r).
```

The formal first derivative `H'` is recovered by differentiating this
expression with all source derivatives retained. The other values are

```
F1 = s(4rH+2rT−M)/f
F2 = rB/(2sf)+μF1/(4srf)−2H/f²+2rH'/f
F0 = f²F2+2fT.
```

These identities and all three original harmonic Bianchi row identities
are formalized in `ThetaCuspHawkingBMScalarStreamReconstruction.lean`
and have passed the isolated leaf audit. The angular convention is
the **trace-free** Hessian: its divergence coefficient is `μ/2−1`, and
its angular trace is zero. For residual rows
`A=TT, B=TR, C=RR, D=T, E=R, F=TF, G=L`, the exact defects are

```
Wt = fB' +(4r−2/r)B−2sA/f+μD/r²
Wa = fE' +(4r−2/r)E−2sD/f+((μ/2−1)F+G)/r²
Wr = fC' +(5r−2/r)C−2sB/f+rA/f²+μE/r²−2G/r³.
Q  = 2rC+4E
Q' = 2C+2rC'+4E'

(μ−2)(E+F/r)/r²
  = Wr+2Wa/r−fQ'/(2r)−(2−1/(2r²))Q−rA/f²+2sB/f+4sD/(rf).
```

The last identity is verified without a compatibility premise. If the
three defects, `B,B',D,F,Q,Q'` vanish and `s,r,f,μ−2` are nonzero,
the verified conclusion is `A=C=E=0` and `G=−r²fE'`. A pointwise claim
that `G=0` would be too strong: a value `E=0` does not force its separate
first-jet slot to vanish. The positive replacement is exact: once these
relations hold for genuine differentiable residual functions on a
neighborhood, `E` vanishes there, hence `E'=G=0`. This differential
closure must be constructed for the original forced source.

The parameter `μ` here is the angular eigenvalue of `Delta`, not the
shifted physical angular resolvent parameter. The latter's proved
nonrealness cannot discharge `μ≠2` for a general source. A broader
construction replaces division by `2−μ` with the actual modular form
of `2−Delta`: on the existing value-plus-gradient energy domain, its
bounded form operator is `I+J*J`, where `J` is the original embedding
into modular L². Its form is the sum of both gradient terms plus twice
the scalar mass. The corpus coercive-operator inverse theorem supplies
the full-domain inverse. The concrete application in
`ThetaCuspHawkingBMAngularReconstruction.lean` has passed its foreground
scratch check and isolated final leaf audit: for every modular L² forcing `F`,
there is exactly one `h` in the original energy domain such that

```
sum_i <D_i v,D_i h> + 2<Jv,Jh> = <Jv,F>     for every energy test v,
||h||_energy <= ||F||_L2 / 2.
```

The estimate controls both gradient components and scalar mass. It
follows from `||h||²+||Jh||² <= ||Jh|| ||F||`, retaining all terms,
and supplies quantitative control for differentiating the reconstructed
response once the original forcing is admitted.

The joint next conjecture is to extend the literal residual identity
from a separated angular harmonic to the original angular scalar
potentials, replacing `μ−2` by `Delta−2`. The newly constructed inverse
then eliminates that residual in the actual energy domain without a
spectral-expansion premise. Its principal cusp part requires a separate
exact reconstruction. The nonreal physical resolvent theorem and the
existing native-response cusp-flux reconstruction have different
parameters and do not by themselves establish this extension.

**Whole-chain consequence:** reconstruction now has explicit source
terms and a precise completeness test. The two attacks, radial
elimination and modular coercivity, address different parts of the
same full metric producer. Still required are genuine derivative
realization, compatibility of the original quadratic source in all
channels, admission of the reconstruction forcing with every cusp
principal part and cutoff contact, and the common causal boundary
domain. Only those producers can place the actual causal difference
in the earlier on-shell cyclic pairing. Its global left reader,
nonzero coupling and fixed-clock extinction remain open; the local
identities alone establish none of those conclusions.

**Formal verification:** both new leaves passed `lake env lean` scratch
checks and their exact `lake build` audits at default limits. Each audit
built only its new Lean leaf (plus configuration), using cached
dependencies. Both are wired into the RHTower umbrella; no umbrella or
full build was run. The frontier map and universal-law ledger are
unchanged, since these new statements concern this route's reconstruction.
The formal lint gate passed, with existing large-file warnings.

### Original source compatibility by contraction

The next target is conservation of the original full quadratic Einstein
source, needed to discharge the reconstruction's Bianchi conditions in
every channel. The existing actual metric Bianchi identity is uncontracted.
The contraction is now formalized using the metric and inverse
compatibility identities. Commuting two actual metric derivatives gives
`R_ij.transpose * g + g * R_ij = 0` for the original connection's
curvature matrices. Together with their proved alternation in `i,j`, this
provides the two skew symmetries needed for the contraction, without
requiring a separate general pair-exchange theorem first.

The contracted expression has been identified with the literal covariant
divergence of the original cosmological Einstein tensor, including actual
spatial derivatives through a neighborhood identity. The next step is
to differentiate twice in amplitude. The proved background and first-order
equations remove lower-order coefficient terms; the original quadratic
source and its spatial derivatives remain. This conservation producer,
combined with genuine radial derivative realization and full angular
source admission, is intended to connect reconstruction to the common
retarded/advanced metric equations. It does not itself supply the causal
boundary domain, the global left reader or fixed-clock extinction.

For the contraction, write `T k i j u v = (nabla_k R_ij)^u_v`, retaining
connection action on both curvature-form slots. The proved algebraic
step uses `T k i j = -T k j i`, symmetric `gInv`, and
`T k i j * gInv + gInv * (T k i j).transpose = 0`.
Let `P k v j = sum_u T k u j u v`. Contracting differential Bianchi with
`gInv b k`, then using these skew identities, gives

```
2 * sum_(k,b) gInv b k * P k b j
  = sum_(b,k) gInv b k * P j b k.
```

The right side is proved equal to the actual scalar-curvature derivative;
the left side is twice the actual Ricci divergence. The inverse metric
is differentiated in this identification. Metric compatibility also
supplies the cosmological metric term's zero divergence. For the derivative-level skew law, differentiate
`R.transpose*g+g*R=0` on a genuine neighborhood. Substituting
`g'=A.transpose*g+g*A` shows that `R'+A*R-R*A` is again metric-skew;
the remaining connection actions are scalar combinations of metric-skew
curvature matrices. All these steps pass Lean in the new leaf modules
`ComplexMetricCurvatureSymmetry`, `ComplexMetricCovariantCurvature`,
`ComplexMetricBianchiContraction`, `ComplexMetricContractedDerivative`,
and `ComplexMetricEinsteinConservation`. Their exact leaf audits passed;
only new leaves were built, with cached dependencies. The geometry umbrella
imports them without an umbrella build.


#### Consequence for the whole proof chain

The original full Einstein source has a proved local conservation producer.
This moves source compatibility upstream of scalar/vector/tensor separation:
the retained source must inherit it through the actual coefficient extraction,
and reconstruction must preserve it. It does not produce a retarded or advanced
inverse, common boundary domain, nonzero left-QNM coupling, or fixed-clock
extinction. The previously proved cyclic action identity leaves its original
boundary defect explicit. Those boundary terms must remain attached when the
conserved source is used in the causal action; dropping them would lose the
connection to the later extinction problem.

The next conjecture is conservation of the original quadratic source under the
background covariant derivative. Write `E(e,x)` for the original full source
and `D(e)` for its metric-dependent divergence. The new theorem gives
`D(e)E(e)=0` on a genuine amplitude neighborhood. The existing physical
background and first-order equations give `E(0)=0` and `E_e(0)=0` on the
exterior. Twice differentiating, including every operator coefficient, gives
`D(0)E_ee(0)=0`: terms involving `D_e` and `D_ee` multiply those vanishing
lower-order fields. Spatial derivatives of the zero fields also vanish locally.

The unclosed Lean identification is the full mixed spatial/amplitude
interchange and its physical field-jet specialization. The spatial side
is now proved for actual real jet paths. For complete jet fields `q(x), p(x)` and Einstein component `F`, the
spatial derivative of the Hessian is

```
∂x [F''(q)[p,p]]
  = F'''(q)[q_x,p,p] + F''(q)[p_x,p] + F''(q)[p,p_x].
```

The second amplitude derivative of
`F'(q+e*p)[q_x+e*p_x]` gives the same expression, using the corpus's proved
`thirdVariation_symm_left`, `thirdVariation_symm_right` and
`secondVariation_symm`. Real-coordinate differentiation must be connected to
these complex derivatives by restriction of scalars and actual field-jet
regularity; a supplied derivative array is insufficient. Corpus search also
found the Fokas–Lenells mixed-derivative workflow: identify each iterated actual
derivative with its produced expression before comparing them. Its scattering
operators are different, so only that proof mechanism transfers here.

Analytical status: the coefficient argument above is derived from the proved
full identity and existing Hessian symmetry. Formal status: the full identity
is proved; the quadratic coefficient's spatial/amplitude interchange and its
physical specialization still need Lean closure. This remaining work is
necessary before claiming that reconstruction's quadratic Bianchi defects
have been discharged.

The full identity is also specialized to the actual literal theta-cusp field
in `RHTower/ThetaCuspHawkingBMLiteralConservation.lean`.
`sourceField_apply` identifies every exterior component with the existing
`D4BMActualMetricSource.source`. The theorem
`literal_source_conservation_near_zero` supplies conservation on an actual
complex amplitude neighborhood, with regularity, symmetry and nondegeneracy
proved from the literal field and background. Its scratch check and isolated
exact leaf audit passed (new leaf only, cached dependencies); the RHTower
umbrella is wired without building it. This is full nonlinear source
conservation, not yet the separate quadratic coefficient conservation theorem.


The spatial Hessian identity is formalized in
`HTGeometry/CoordinateEinsteinQuadraticSpatialDerivative.lean`.
`secondVariation_hasDerivAt_real` differentiates the original Einstein Hessian
along actual real jet paths, retaining all three terms.
`secondVariation_hasDerivAt_real_symmetric` uses the proved second/third
variation symmetries to give
`F'''(q)[p,p,q_x] + 2*F''(q)[p,p_x]`, the expression needed for the amplitude
comparison. These statements require the actual path derivatives; the next
specialization must produce them from the physical field's complete spatial
jets. Both the scratch check and exact leaf audit passed at the default
heartbeat limit; only the new leaf was built, with cached dependencies.

The remaining conservation target is still the background covariant divergence
of the original quadratic source. The real Hessian derivative theorem closes
one side of the mixed-derivative comparison. The amplitude side, actual
spatial-jet realization, and cancellation using the physical zero/first-order
equations must be connected before this target is declared closed. Even after
that closure, source conservation alone will not establish global causal
solvability or left-QNM incidence. Those questions must be tested against the
same retained boundary/contact functional that survives in the original
cyclic action and would have to enter fixed-clock extinction.

Validation: all seven new leaf modules passed scratch checks and isolated exact
leaf audits. `scripts/formal_tools.py lint` passed; it reported existing large-file
warnings. Both umbrellas are wired but were not built. No mathematical computations,
axiom-printing, heartbeat increases, frontier-map edits or STATUS edits were used.

All owned scratch/search/log/staging paths for this turn were removed after
validation. All owned Lean/Lake and search processes completed; none were left
running. Other agents' temporary files and processes were left untouched.

### Quadratic conservation: actual derivative interchange

Current conjecture: the original physical quadratic source has zero background
covariant divergence. The full nonlinear conservation theorem and real Hessian
path derivative are proved. The next producer must identify actual spatial
jet paths, compare the amplitude derivative of the full spatial Einstein
variation, and cancel the lower-order fields on an exterior neighborhood.

The corpus's `ScalarJetSpatial3ConnectionTable` uses coordinate index `3`, not
third-order regularity; it cannot supply the required third spatial jet.
`EisensteinActualThirdJet` concerns the actual Eisenstein Poincare field in its
convergence chamber, rather than the literal scalar/vector metric here. The
literal metric's already proved all-order exterior regularity provides the
proper starting point: differentiate its complete two-jet along the actual
real coordinate line, retaining ordered derivatives in every slot. Boundary
and contact currents remain attached to the later causal and left-QNM action.

The amplitude side is now proved in
`HTGeometry/CoordinateEinsteinAffineSpatialVariation.lean`:
`affineSpatialEinstein_second` differentiates the original spatial Einstein
variation `F'(q+e*p)[qx+e*px]` twice and gives
`F'''(q)[p,p,qx]+2*F''(q)[p,px]`. Both varying factors are retained;
nondegeneracy is used on a genuine amplitude neighborhood. Scratch checking
and the isolated exact new-leaf audit passed at default heartbeats, with
cached dependencies. Its umbrella import is wired without an umbrella build.

A broad `transgression` paper search found Anghel,
[AKSZ Descent on Manifolds with Ordinary Corners](https://arxiv.org/abs/2608.02928)
(August 2026). The paper organizes defects using signed incidences of boundary
faces under explicit mapping-space hypotheses. No AKSZ or gravity reduction
hypothesis has been supplied for HB. The proposed transfer is only a method:
assemble the actual finite radial, temporal and cusp faces together with shared
corner/contact terms before taking their respective limits. The claimed HB
cancellation or extinction is not a consequence of that paper.

The actual-field side is now verified in `ComplexMetricJetDerivative`:
`jetSpace_coordinateLine_hasDerivAt` produces the derivative of every ordered
slot from C3 field regularity, and `jetSpacePartial_add_smul` proves affine
variation of that genuine spatial derivative. `ComplexMetricMixedEinsteinDerivative`
then proves `einstein_mixed_derivatives`: the two amplitude derivatives of the
actual spatial Einstein field equal the actual spatial derivative of its Hessian.
`ComplexMetricEinsteinSourceVariation` retains the cosmological term and proves
actual first and second amplitude coefficients, amplitude regularity, and the
spatial derivative of the first variation. All three new leaves passed scratch
checks and isolated exact leaf audits (15s, 12s, 29s respectively); their umbrella
imports are wired without umbrella builds.

Whole-chain consequence: these results make coefficient conservation derivable
from the original field identity, instead of adding a divergence assumption to
a projected source. The remaining coefficient step is to use the original zero
and first-order equations on a spatial neighborhood and contract the resulting
second coefficient with the background connection and inverse metric. This does
not yet supply the full causal inverse, common boundary domain, physical left-mode
incidence, or fixed-clock extinction. The same original boundary/contact defect
continues to constrain all those later steps.

Broad/deep searches for matrix smoothness found a public real-matrix inverse
lemma, while the needed complex local inverse lemmas in the metric modules are
private. Searches for `Peano` and then `Taylor remainder` found the exact
`AnalyticSlopeFactor.eq_taylor_two_add_sq_mul` decomposition. It exposes a useful
stronger possibility: after the source's first two coefficients vanish, dividing
out amplitude squared can extract conservation using only continuity of the
metric weights. This is an alternative analytical proof mechanism, not a proved
HB specialization or a new extinction claim. The current finite Leibniz argument
already has the stronger regularity available and remains the direct closure.

`ComplexMetricEinsteinSpatialSource` now proves actual spatial-source amplitude
regularity and identifies its first and second amplitude derivatives with the
spatial derivatives of the original linear source and Einstein Hessian. Its
scratch check and exact leaf audit passed; the audit built only this new leaf
(9.1s), with existing dependencies cached.

`ComplexMetricQuadraticConservation.hessian_conservation` is now proved and
leaf-audited (11s). For actual C3 symmetric complex metric and perturbation
fields, background nondegeneracy, and the original background and linearized
equations on a spatial neighborhood, it produces zero background covariant
divergence of the full Einstein Hessian. The proof derives the actual inverse
metric and connection's amplitude regularity, expands both tensor-index actions,
uses finite Leibniz at the original source's double zero, and differentiates the
already proved nonlinear Bianchi identity. The output is the original Hessian
tensor, with no prescribed source derivative arrays. Constant-scalar divergence
linearity is also verified, to retain the Taylor factor one half.

The physical Xi-labelled specialization is the remaining local conservation
check. Full causal solvability and original boundary-domain matching remain
separate producers; the scalar stream's residual identities alone cannot stand
in for those fields and their genuine radial derivatives.

Two full-field construction mechanisms remain under comparison after this
conservation result. The radial route must transport the original conserved
source into the actual harmonic source rows, realize all reconstructed radial
jets, and solve the common physical boundary problem. A second candidate is to
identify the original linearized Einstein operator with a gauge-fixed tensor
wave operator plus its gauge term, solve that tensor equation, and prove that
the gauge constraint propagates from admissible data. Either route must produce
the same original causal solution and retained boundary action before claiming
physical left-QNM coupling or any clock law.

Broad/deep `Lichnerowicz` and `gauge propagation` corpus searches did not identify
an applicable producer for the second mechanism. Both searches reported partial
filter/judge and decomposition coverage; this is not a claim that the corpus
lacks one. The returned Fokas–Lenells Hardy propagation statements concern their
own analytic slices and boundary corrections, and do not identify the metric's
tensor operator or boundary domain. No such identification has been assumed.

The physical specialization now passes scratch checking in
`ThetaCuspHawkingBMQuadraticConservation`.
`physical_hessian_conservation` discharges regularity, symmetry, background
nondegeneracy, and the original background and linearized equations for every
physical Xi-labelled theta-cusp perturbation on the actual exterior chart.
`physicalQuadraticSource_eq` identifies the resulting tensor, divided by two,
with the original source's actual second Taylor coefficient.
`physical_quadratic_source_conservation` proves its zero background covariant
divergence with no supplied conservation, derivative-jet, or reconstruction
certificate. The physical leaf's isolated final audit passed (56s); it built only the new leaf with cached dependencies.

Analytical proof: write the original cosmological tensor as E(e) and its actual
covariant divergence as D(e). Nonlinear Bianchi gives D(e)E(e)=0 on an amplitude
neighborhood. Both E(0) and its first amplitude derivative vanish on an exterior
spatial neighborhood. The verified mixed derivative identities therefore kill
their spatial derivatives as well. Finite Leibniz retains only D(0)E''(0), which
is zero. E''(0)/2 is the original quadratic coefficient Q, hence D(0)Q=0.
The inverse metric and both covariant tensor-index actions are included in D.

This closes the local quadratic-conservation conjecture. The hard remaining
producer is a full causal field solving the original sourced linearized tensor
equations in the physical domain. Transport to harmonic constraints, actual
radial reconstruction, common retarded/advanced boundary data, and the original
left-mode boundary action must still be supplied. Conservation does not prove
that field exists, select a physical left-mode coupling, or establish extinction.

Validation for this producer: all seven new leaf modules passed `lake env lean`
scratch checking and exact isolated `lake build <module>` audits. The authoritative
formal lint passed, reporting existing large-file warnings. Both umbrellas are
wired without being built. No mathematical computations, heartbeat increases,
axiom printing, Git commands, frontier-map edits, or STATUS edits were used.

All owned scratch, search, audit, log and staging paths for this producer were
removed after validation. No owned Lean/Lake, search or lint processes remain;
other agents’ files and processes were left untouched.


### Independent harmonic rate and a finite Laurent source inverse (0912x)

Fresh corpus inspection changes the construction problem. The cached
`ThetaCuspHawkingBMScalarStreamReconstructionField` already derives all seven
sourced harmonic equations from genuine twisted radial derivatives, and
`ThetaCuspHawkingBMScalarStreamGreenSourced` supplies a smooth interior Green
solution. Its current dictionary ties the source rate and output angular
parameter to the same `chi`; its integration cutoffs are interior. Neither
interface yet identifies the full original source with a physical endpoint
solution. `ThetaCuspHawkingBMForcedMetricField.forcedMetricField_einstein`
already solves all sixteen components for its specified scalar-vector mixed
source. These are usable producers, not gaps to rebuild.

New analytical conjecture: the explicit scalar-scalar master source admits a
particular solution y(r)=r+A/r+B/r^3 at independent complex rate s and angular
eigenvalue mu. Clearing the twisted master operator gives

    r^2(r^2-1)y'' + (2r^3+4sr)y' + (mu-2s-4s^2)y.

On r^k this equals k(k+1)r^(k+2) +
[mu-(k-2s)(k-2s-1)]r^k. The source's two highest Laurent coefficients match
this operator applied to r exactly. The remaining two coefficients determine
B and A by triangular elimination. The apparent B denominator
mu-(2s+3)(2s+4) cancels against an exact factor of the source numerator;
that cancellation must be checked in Lean. The remaining possible denominator
is mu-(2s+1)(2s+2), besides the existing angular factor 2-mu.

Whole-chain test: if proved, this is a source-specific particular inverse
without tying parent rate to output angular eigenvalue. The original source
transport and the homogeneous correction enforcing causal horizon/AdS data
still need to be derived. Any correction or resonance must be carried into
the original left-mode pairing and fixed-clock question; a particular solution
alone supplies no extinction. Next test: prove the actual derivative identity,
exact source cancellation, and smooth sourced reconstruction with this field.

The next conjecture concerns boundary admission, not a vanishing source:
for the finite Laurent particular field, subtracting the forced r term gives
A/r+B/r^3. In reciprocal radius x=1/r, the scaled full field is the polynomial
1+A*x^2+B*x^4; the subtracted remainder is A*x+B*x^3. Thus its boundary germ
can be retained exactly before reconstruction and pairing. Whether the original
metric boundary conditions select this affine master boundary datum must be
proved from the reconstruction; it is not assumed here.

Broad/deep searches used reconstruction, hyperbolic, endpoint extension, and
rational/Laurent mechanisms, including candidate lemmas, proof-method source
arguments and ingredient sets. Results were partial (source/compiler and
retrieval coverage reported), so missing hits are not absence claims. The
Laurent search returned rational-function/Laurent-series operator transport,
but no matching particular solution among its reported candidates. Exhaustive
source references to `ssMasterSource` and `SSMasterEquation` identify the
existing interior Green construction described above.

A broad renormalization paper search found Rogers and Whitehill,
[What are the consequences of independent factorization and renormalization
scales?](https://arxiv.org/abs/2608.01489) (August 2026). Its QCD discussion
relates subtraction choices through conservation constraints. The transferable
question here is whether source and boundary subtractions preserve the same
original Einstein identity. Its QCD hypotheses do not prove any HB identity;
the proposed Laurent decomposition is being derived directly from the corpus
source instead. The separate broad resonance search returned no useful recent
paper in its reported results.

The finite Laurent conjecture now passes `lake env lean` in scratch, including
actual first/second radial derivatives and the twisted sourced equation. The
original lower source coefficient factors exactly as predicted. No numerical
or symbolic external computation was used.

The analytic coefficients simplify further. With d=(2s+1)(2s+2),

    A = s(5s+2)/2 + s^2(s+1)(s+2)/(2-mu)
        + 3s(s+1)^2(3s+4)/(2(mu-d)),
    B = -s^2(s+1)^2/8 - s^2(s+1)^3(s+2)/(4(2-mu)).

These simplifications are under Lean verification. The parameter d is exactly
the existing mixed-source angular parameter, as seen in
`D4BMModularCore.parameter_physicalRate`. Moreover,
`fullAngularField_equation` already supplies
Delta H=d H+(d/2)S^2 for the original literal scalar S. This suggests lifting the
Laurent coefficients to actual angular fields using the existing inverse at d
and the inverse at 2, instead of decomposing the entire quadratic source into
individual spectral harmonics. That is a new full-field construction candidate
exposed by the radial solution. It still requires the original source identity,
matching the inverse-at-2 domain, and proving the reconstructed metric's physical
boundary and time-onset conditions. Those conditions determine whether this
particular field can enter the causal action and the extinction argument.
