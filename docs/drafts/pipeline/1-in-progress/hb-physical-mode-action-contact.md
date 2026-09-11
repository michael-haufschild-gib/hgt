# HB: actual projected Einstein current and QNM pairing

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source →
physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
RH remains unproved. The frontier map is read-only.

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

This identifies a projected mixed sector. Full angular reconstruction,
independent SS/VV sectors, retarded/advanced Peierls identification and
residue extraction through the full current's horizon limit remain open.

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
`ThetaCuspHawkingBMTemporalContactHorizonFactor`. Uniform endpoint estimates
for F_hor and the restored full-current integral are still required.

## Active residue/interchange target

Construct the full temporal current's two power counterterms and its
possible logarithmic counterterm from the now controlled Green blocks.
The exact original homogeneous horizon decomposition is already in
`ThetaCuspHawkingBMOriginalHorizonBasis`; the normalizable left mode's
opposite coefficient is connection/(2w), proved in
`ThetaCuspHawkingBMOriginalNormalizableHorizonDomain`. This supplies a
specific cancellation to establish for the logarithmic channel.

The next estimates are uniform second-order Gauss and elementary lift
remainders, followed by their propagation through the full four-channel
source and both Einstein contacts. After clearing the frequency pole,
the restored incoming integrand must be dominated by z^(beta+1), beta>-2;
the opposite channel must retain its exact logarithmic subtraction.
Then exchange frequency residue with the original restored integral.
The completed radial-norm theorem identifies the value this exchange must
recover. Full-current residue interchange is not yet proved.

Broad/deep searches inspected candidate statements and method/source
arguments. The Cauchy-dominated integral mechanism was used and checked
in Lean. Taylor searches also located geometric-series remainder methods
in `RiemannGaussian/FiniteToEntireExpandingTaylor` and Banach-valued Taylor
bounds in `BourgainQuadraticTaylorControl`; applicability to the remaining
Gauss estimate has not yet been checked. Retrieval was partial, including
incomplete semantic coverage and largely pending compiler metadata.
