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

### Source-moment reduction target

The explicit source amplitude leaves the original `fundamentalSourceMoment`
to be evaluated. A new reduction candidate uses `r = sqrt(1-z)`. Write

```
A = (5*s^2+15*s+4)/4,
B = s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4,
W(r) = (1-r)^w * (1+r)^(2*s),
I_n = FP integral(0..1, r^n * W(r)),
d = 2*s-w,  e = w+2*s+2.
```

The pointwise substitution predicts `M = 2*a^2*(A*I_2+B*I_4)`.
Differentiating `r^n*(1-r)^(w+1)*(1+r)^(2*s+1)` predicts the recurrence

```
d*I_0-e*I_1 = -1,
n*I_(n-1) + d*I_n - (n+e)*I_(n+1) = 0  (n >= 1).
I_2 = ((e+d^2)*I_0+d)/(e*(e+1)),
I_4 = ((d^4+(6*e+8)*d^2+3*e*(e+2))*I_0
       +d*(d^2+5*e+8))/(e*(e+1)*(e+2)*(e+3)).
```

This reduces the candidate evaluation to one incomplete beta integral:
`I_0 = 2^(w+2*s+1) * FP integral(0..1/2, t^w*(1-t)^(2*s))`.
The integration-by-parts boundary term is essential. These identities
are not yet Lean theorems: the immediate obligation is transporting the
original fixed endpoint subtraction through the change of variables and
proving its limit. On the physical strip the discarded comparison term
should be of order `epsilon^(Re(w)+2)`, which tends to zero. This must be
proved for the same finite part already present in the source, before
using the recurrence to address nonvanishing or joint survival of the
physical branch/side family.

Broad OR retrieval for quintic, Catalan, Raney and period terms returned
no applicable source evaluation. Deep Mellin/incomplete-beta retrieval
found `ThetaCuspHawkingSelfDualGeneralMellinVertex`: its source was read,
and its shifted-beta recurrence mechanism motivates the reduction above.
Its complete-beta, positive-real-part hypotheses do not evaluate this
half-interval physical finite part. Candidate lemmas, source arguments
and the proposed tail-splitting ingredient set were inspected. The deep
request returned partial results with unfinished auxiliary queries;
compiler coverage remained mostly pending and semantic coverage was
unmeasured. No numerical computation or nonvanishing premise is used.
