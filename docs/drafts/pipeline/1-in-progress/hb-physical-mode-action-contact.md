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

Construct the full temporal current's two power counterterms and its
possible logarithmic counterterm from the now controlled Green blocks.
The exact original homogeneous horizon decomposition is already in
`ThetaCuspHawkingBMOriginalHorizonBasis`; the normalizable left mode's
opposite coefficient is connection/(2w), proved in
`ThetaCuspHawkingBMOriginalNormalizableHorizonDomain`. This supplies a
specific cancellation to establish for the logarithmic channel.

The original Gauss family now has a proved uniform second-order endpoint
bound; the elementary Jacobian bound is also proved. Their propagation to
the original incoming pairing core also passes its Lean scratch check. Assembly
must still retain the explicit gradient lift, the full four-channel source,
both Einstein contacts, and the opposite-mode logarithmic subtraction.
Full-current residue interchange is not yet proved.

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
The native opposite-mode application must first derive a common nonzero
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
The native logarithmic-restoration scratch combines the Gauss nonzero
neighborhood with the source primitive's neighborhood, proves A_b is
preserved at their common smaller cutoff, and derives the original
c_minus*G*h(-w)/[2z sqrt(1-z)] logarithmic cutoff limit. That native
application is prepared but not yet verified.
 This proves the paper mechanism for regularity while
retaining the logarithmic finite part. Lean still needs the
native logarithmic cutoff theorem and extension identity; no
analytic extension is inferred from totalized point values at the pole.

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

Latest repository lint reports three unreachable modules outside these edits:
`ThetaCuspHawkingBMClearedOnsetPulseTransform`,
`ThetaCuspHawkingBMOnsetPulseTransform`, and `XiAffineCollisionControl`.
No lint errors name the new incoming-restoration leaves; their umbrella
imports are present and their exact audits passed. The global lint gate
is not claimed passed for this state.
