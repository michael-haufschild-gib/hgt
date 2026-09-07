# HB actual Einstein metric-jet source

- **Stage:** 1-in-progress
- **Goal:** unconditional closed Lean proof/falsification of RH through HB; not achieved.

## Full chain and missing input

Literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal
radial/left-QNM action → fixed Hawking-clock extinction → RH.

The real and complex local Einstein Hessians B and third variations C are constructed from
the literal complete metric two-jet. They are symmetric multilinear forms, and finite polarization recovers
every mixed slot from the explicit diagonal coefficients. Reduced BM inversion and its boundary
moment are constructed and uniquely characterized. The complex forms are proved to be the unique
extensions of the real forms. The full covariant KI reconstruction now has a complete metric
two-jet proved equal to its actual coordinate derivatives. The upper-half-plane BM background
and its vacuum equation are proved. Actual affine variation of a C2 tensor field realizes the
quadratic and direct cubic Einstein coefficients, including the full KI reconstruction.
The fundamental radial profiles and literal scalar/coexact-vector cusp fields are instantiated.
The complete first Einstein variation now equals the actual field-source amplitude derivative.
The scalar metric has an exact generally nonzero normalized boundary coefficient despite its
vanishing master. The literal scalar sector now satisfies all sixteen first-order Einstein
components at both fundamental QNM branches, with all angular assumptions discharged.
The vector-sector equation, nonlinear field/gauge corrections, complete source reduction,
physical causal action, and final left-QNM projection remain to be derived.

Corpus searches `einstein variation`, `metric perturbation`, `ricci coordinate`, `inverse series
matrix`, and `christoffel derivative` locate the coordinate curvature definitions, smooth metric
inverse, and the entrywise inverse-curve derivative. They do not locate an actual Einstein
second/third-variation bridge. The restricted Plebanski spin-two jet cannot supply one: full
two-coordinate reconstruction and nonlinear mixed sectors remain required.

## Source-derived construction

For a smooth nondegenerate metric g at x, retain its value, all first coordinate partials H_k,
and all second partials K_kl. Set G=g(x)^(-1). Differentiating Gg=1 forces
`partial_k G = -G H_k G`. Thus Christoffel symbols and their first derivatives are explicit
finite contractions of (G,H,K). Substitute them into the corpus's coordinate Riemann/Ricci
definitions and contract to obtain the exact Einstein tensor from the complete metric two-jet.
This must be proved equal to the actual differential expression, rather than declared to be it.

For perturbation h, the inverse identity has a fixed cubic expansion, obtained from
`(1+X)(1-X+X^2-X^3)=1-X^4` with `X=G h`. This fixes the inverse-metric contributions to B,C
before any Xi-copy selection. Combined with the actual curvature two-jet formula, finite
polarization and coefficient extraction can derive the full local nonlinear source.

## Closed metric carrier

`HTGeometry.CoordinateCurvatureTwoJet` defines the complete algebraic metric two-jet over any
field and proves its actual real smooth-metric realization. Seven public theorems identify the
inverse-metric coordinate derivative, Christoffel symbols, complete Christoffel derivative,
Riemann tensor, Ricci tensor, scalar curvature, and Einstein tensor. The central result is
`coordinateEinsteinTensor_eq_twoJet`. No higher spatial jet or fitted source is supplied.

`HTGeometry.MatrixAffineInverseCubicRemainder` proves the explicit cubic coefficients, quartic
product defect, and exact inverse remainder over a field. For real matrices it verifies the
actual derivative chain with first, second, and third derivatives

`-F H F`, `2 F H F H F`, `-6 F H F H F H F`, where `F=(A+tH)^(-1)`.

The seventh public theorem proves the sharp classification
`matrixAffineInverseThirdDerivative A H 0 = 0 iff (A^(-1)H)^3 = 0` for invertible A.
Thus affine primitive data do not justify deleting the inverse's cubic contribution. This
classifies that contribution only; other terms in the complete Einstein source may interact.

## Closed diagonal Einstein coefficients

`HTGeometry.CubicDerivativeCurve` carries a value function and three successive derivative
functions, certified on a parameter domain. Its constant, affine, sum, difference, product,
and finite-contraction constructors retain every binomial product term. Eight public theorems
identify values and prove that the second/third components are the actual iterated derivatives
on an open domain. Certificates are proved symbolically, with no computational result used as
an axiom or proof certificate.

`HTGeometry.CoordinateEinsteinAffineCoefficients` forms the literal affine two-jet J+tK and
uses the actual inverse entries and their proved derivatives. It propagates these curves through
spatial inverse differentiation, Christoffel symbols and their spatial derivatives, Riemann,
Ricci, scalar curvature, and the Einstein tensor. Fourteen public theorems identify the complete
value expression and its diagonal coefficients:

`affineEinsteinQuadraticCoefficient J K = (actual second parameter derivative)/2`,
`affineEinsteinCubicCoefficient J K = (actual third parameter derivative)/6`.

Both definitions evaluate explicit finite contractions of J,K; they are not defined by the
iterated derivative used in the verification theorem. The only parameter-domain requirement
is nondegeneracy of the background metric value. Its open affine nondegenerate domain is
proved from the determinant. The same coefficients apply to `Einstein + Lambda*metric` for
any fixed real cosmological constant; that affine additive term has no second/third component.
No arbitrary nonlinear map, helicity projection, or clock defect enters the coefficient definition.

## Closed actual mixed Einstein variations

`HTGeometry.CoordinateEinsteinMixedVariations` uses the normed product of metric, first-partial,
and ordered second-partial arrays. Encoding/decoding preserves the entire jet and its affine
perturbations. Cramer's formula proves local smoothness of the actual inverse at each
nondegenerate background; all finite curvature contractions preserve that smoothness.
`contDiffAt_einsteinComponent` proves local smoothness of the literal Einstein component to every
order. No globally nondegenerate extension is assumed.

The actual second and third Fréchet derivatives define the bilinear `secondVariation` and
trilinear `thirdVariation`. Local Hessian symmetry proves symmetry of B and the first two slots
of C. Differentiating the locally valid Hessian symmetry proves symmetry of the final two slots.
These adjacent swaps supply all permutations. An affine-line derivative certificate and
uniqueness identify their diagonals with the previously constructed finite coefficients:
`B(K,K)/2 = quadratic(J,K)` and `C(K,K,K)/6 = cubic(J,K)`.

Finite polarization then gives every actual mixed slot, with no arbitrary multilinear input:

- `B(p,m) = Q(p+m)-Q(p)-Q(m)`.
- `C(u,v,w) = T(u+v+w)-T(u+v)-T(u+w)-T(v+w)+T(u)+T(v)+T(w)`.
- The `x^2*y` coefficient of `T(x*p+y*m)` is first extracted as the sum of three permutations
  divided by six. Proved symmetry identifies it with `C(p,p,m)/2`.
- That direct `++-` source is also `(T(p+m)-T(p-m)-2*T(m))/2`.

Here Q,T are the explicit finite diagonal Einstein coefficients at the fixed background J;
all perturbations retain the full spatial two-jet. Sixteen public theorems close the real local
mixed-source calculation, including the full two-mode cubic expansion and both polarizations.
This identifies the actual differential Einstein operator through its previously proved two-jet
realization. It does not yet identify the physical gauge-fixed complex BM source.

## Closed complex source identification

`HTGeometry.CoordinateEinsteinComplexVariations` constructs the complex derivatives of the same
literal Einstein contraction. `mapScalars_einstein` proves that every scalar field homomorphism
commutes with the entire contraction, including the adjugate-defined inverse. On complete complex
jet coordinates, local smoothness holds at every nondegenerate metric to every order. The actual
complex Hessian and third variation are complex multilinear and have all slot symmetries.

The real inclusion is an explicit continuous real linear map on every jet component. Restricting
complex derivatives to real scalars and applying derivative uniqueness proves exact equality
with the real first, second, and third variations. For the higher derivatives, the preceding
compatibility identity holds locally on the open real nondegenerate domain and is differentiated
with fixed real slot directions. No identification of higher derivatives is assumed.

Every complex jet splits into the inclusions of its real and imaginary parts. This proves that
the constructed complex B,C are the unique complex multilinear extensions of the actual real
forms. Explicit formulas reduce B to four real mixed evaluations and C to eight. Combined with
the prior finite polarization identities, arbitrary complex source inputs are determined by the
explicit real diagonal contraction coefficients. The complex direct `++-` source also obeys the
proved three-permutation/6 identity `C(p,p,m)/2`.

Seventeen public theorems close this local complex extension. They supply neither a choice of
physical gauge nor the response-domain and left-QNM identifications.

## Closed full covariant reconstruction

The corpus entry points are `ThetaCuspHawkingBMKIScalarMetricReconstruction` and
`ThetaCuspHawkingBMKIVectorChiralReconstruction`. They construct the scalar/vector gauge-invariant
metric orbits and a chiral carrier whose first two radial jets recover the master. That carrier
is a particular combination, not the full perturbation tensor consumed by the Einstein forms.
The separate reconstructed components involve the master first derivative, so deriving their
complete metric second jet must retain the required higher master derivatives and all angular
channels before any cancellation is used.

The covariant reconstruction conventions are verified against KI Eqs. (2.4), (2.7), (2.21),
and (5.9)--(5.10) in [hep-th/0305147](https://arxiv.org/pdf/hep-th/0305147). In the representative
with scalar `f_a=H_T=0` and vector `H_T=0`, scalar `f_ab=F_ab`, `H_L=F`, and vector `f_a=F_a`.
For `f=r^2-1`, lower the existing mixed scalar orbit to
`h_tt=-f*FttMixed*S`, `h_rr=FrrMixed*S/f`, `h_tr=FrtMixed*S/f`, and
`h_AB=2*r^2*angularTrace*gamma_AB*S`. The vector entries are
`h_tA=-r*f*FtContravariant*V_A`, `h_rA=r*FrContravariant*V_A/f`; retain symmetric partners.
The time mode multiplies all components. `ThetaCuspHawkingBMFullMetricTwoJet` implements this
full symmetric tensor. `covariantMetricExpression_eval` identifies its expression with the
existing typed scalar/vector KI orbit constructors; their unused second-master-jet argument
does not enter this value-level reconstruction.

`HTGeometry.ScalarTwoJetCalculus` extends the existing `ScalarTwoJet` carrier with constants,
addition, negation, inversion, and scalar composition. Each operation is proved equal to the
actual first and ordered second derivatives of complex-valued fields on real coordinates.
An expression calculus assembles these proofs: `Expression.eval_jet_correct` identifies every
rational reconstruction with its actual complete scalar two-jet wherever its denominators are
nonzero. The construction retains all derivatives of radial factors and coordinate changes,
time modes, horizon harmonics, and horizon metric entries.

`metricJet_correct` assembles these scalar jets into the complete four-coordinate metric jet.
`metricJet_of_masters` realizes it on literal separated fields with
`z=1-r^(-2)` and time mode `exp(-i*omega*t)`. Its exact local conditions are complex C3 scalar
and vector masters, real C2 horizon fields, `r != 0`, and `r^2-1 != 0`. Both parity sectors and
every angular derivative are retained. These regularity and chart conditions are explicit;
their physical profile instantiation is not assumed to be proved.

`scalarZDerivative_jet` identifies the actual jet of the master's first derivative composed
with z. Its second coordinate derivative contains both the third master derivative times
the two first coordinate derivatives of z and the second master derivative times the second
coordinate derivative of z. An on-shell ODE may reduce the higher master derivatives, but such
a reduction must be proved before substitution. The chiral carrier's special cancellation
does not establish cancellation in the full reconstructed tensor.

Eight public theorems close the scalar calculus and eight close the full metric reconstruction.
This supplies the complete local input tensor for the actual Einstein variations; it does not
solve the nonlinear gauge-fixed boundary problem.

## Closed BM background and actual affine source

The background construction uses the upper-half-plane horizon chart already present
in the corpus's actual Eisenstein derivative equations. In coordinates `(t,r,x,y)` its metric is
`diag(-(r^2-1), (r^2-1)^(-1), r^2/y^2, r^2/y^2)`. The massless `d=4`, unit-radius metric and
cosmological convention are fixed by BM Eqs. (1)--(4) in
[hep-th/0609028](https://arxiv.org/pdf/hep-th/0609028).

`ThetaCuspHawkingBMBackgroundMetricTwoJet` identifies the explicit complete background jet
with actual derivatives, including its mixed radial/horizon entries. Its determinant is
`-r^4/y^4` wherever the blackening factor is nonzero. The exact inverse and full curvature
contractions prove `Ricci=-3*g`, scalar curvature `-12`, and Einstein tensor `3*g`. On the
exterior chart `r>1, y>0`, nondegeneracy and all local coordinate smoothness follow from the
metric formula. `exterior_vacuum` proves the cosmological equation with `Lambda=-3` for the
actual field jet. The background equation and admissibility are conclusions, not hypotheses.
Eleven public theorems close this local background construction.

`ThetaCuspHawkingBMActualAffineMetricSource` defines the literal perturbation `g+epsilon*h`
for a complex tensor field h on the real coordinate chart. `perturbedMetric_jet` proves that
taking its complete coordinate jet commutes with this variation whenever h is locally C2.
`source_eq` identifies its actual cosmological source with the derived Einstein function on
the corresponding affine jet line; `source_zero` follows from the proved background vacuum.

The admissible amplitude domain is defined by the actual perturbed metric determinant and
proved open with zero inside. A three-step complex derivative certificate on this domain
identifies the quadratic coefficient with `B(hJet,hJet)/2` and the direct cubic coefficient
with `C(hJet,hJet,hJet)/6`. The fixed cosmological term is retained through this calculation;
its higher derivatives vanish by the proved chain. `reconstructed_source_coefficients` connects
both identities to the full covariant KI reconstruction through `metricJet_correct`. Six public
theorems close this affine field-to-source bridge. No independent source tensor is supplied.

These are direct affine coefficients. Contributions from second- and third-order field
corrections, nonlinear gauge conditions, and physical boundary projection remain separate.
Global horizon quotient and causal boundary completion are not consequences of a local chart
vacuum calculation.

## Closed dressed physical mixed master

`ThetaCuspHawkingBMPhysicalMonodromyMaster` distinguishes the reduced hypergeometric
function F from the physical master `Phi=z^alpha*F`, with `alpha=-i*omega/2` and `beta=0`.
These scalar/vector conventions and the physical equation are fixed by BM Eqs. (24)--(33)
in [hep-th/0609028](https://arxiv.org/pdf/hep-th/0609028). The general KI reconstruction
accepts a physical master function; its reduced-monodromy recovery identity is an algebraic
identity and does not identify F with Phi.

The master restores the principal-log factor, proves its actual first and second
product-rule derivatives, and proves local complex smoothness to every order from the literal
regular Gauss series. Exact differential conjugation gives the physical equation

`z*(1-z)*Phi''+(1-3*z/2)*Phi'+(omega^2/(4*z)-(1/4+chi^2)/4)*Phi=0`.

Here the derivatives are actual complex derivatives, not supplied jet values. Every static
exterior point has `0<z<1`, so convergence, logarithm regularity, the equation, and all required
radial smoothness follow unconditionally there. Differentiating the equation retains
`-omega^2*Phi/(4*z^2)` and yields

`z*(1-z)*Phi'''+(2-7*z/2)*Phi''+(-3/2+omega^2/(4*z)-(1/4+chi^2)/4)*Phi'-omega^2*Phi/(4*z^2)=0`.

`exterior_master_higher_jets` reduces both Phi'' and Phi''' exactly to Phi and Phi' through
`onShellSecond` and `onShellThird`. This supplies the radial third-jet reduction required by
the full metric reconstruction; no selected-carrier cancellation is used.

The same literal mode has a proved outgoing factorization. Its reduced power is `z^(N+1)`
with `N+1=1-c`, so dressing changes the full exponent to `-alpha`. On the positive radial ray,
its Fourier phase depends on `tau-log(z)/2`. Thus this homogeneous monodromy branch cannot
be silently identified with an ingoing retarded mode merely because it solves the physical
radial equation. No causal admissibility or global boundary completion is asserted.
Nineteen public theorems close this dressed radial construction.

## Closed fundamental radial profiles and metric instantiation

The unresolved cubic incidence uses the fundamental plus/minus pair
(`ThetaCuspHawkingAIMECrossBranchTeukolskyResidue`).
`ThetaCuspHawkingBMFundamentalMetricSource` constructs the full profile
`Phi_omega(z)=z^(-i*omega/2)*(1-z)^(1/2)`, with the complex power's zero value retained
at the Dirichlet endpoint. BM Eqs. (31)--(36) fix the boundary and frequency conventions.

Its actual physical radial residual is exactly
`(omega-omega_plus)*(omega-omega_minus)*Phi_omega/4`, where
`omega_plus=chi-3*i/2` and `omega_minus=-chi-3*i/2` are the corpus's fundamental
frequencies. The profile has no interior zeros, so `radial_equation_iff` proves these
are exactly the frequencies at which this profile solves the physical equation.
`exterior_fundamental_equations` specializes this conclusion to every exterior point.
Actual first and second derivatives and all-order local smoothness are proved, including
both the horizon-factor and Dirichlet-factor derivatives.

Boundary conditions are established separately: dividing by the incoming horizon factor
has limit one at zero; the Fourier phase has the incoming horizon coordinate; and the
master has actual zero limit at the Dirichlet endpoint. These facts provide the fundamental
ingoing/Dirichlet radial profiles. They do not identify a time-retarded nonlinear response.

The fixed horizon metric is `y^(-2)*diag(1,1)`. Its angular block agrees identically with the
proved background metric, and its required coordinate smoothness follows from `y>0`.
The full KI recipe now substitutes the fundamental master with independent scalar/vector
amplitudes and this fixed geometry. `fullJet_correct` proves its complete metric jet agrees
with actual derivatives. `source_coefficients` identifies the resulting direct quadratic
and cubic coefficients with actual B/2 and C/6 evaluations on that jet.

Only scalar/vector angular C2 regularity remains explicit in this field-to-source
instantiation. The identity holds for arbitrary such angular fields; it does not assert
that they obey the required harmonic equations or that the reconstructed perturbation
solves the linearized Einstein equation. Seventeen radial and five metric/source public
theorems close this construction.

## Closed joint angular regularity

For fixed arithmetic parameter u, Bessel order nu, real height power a, index degree d
and Fourier sign, the full infinite family is
`F(u,nu,a,d,sign)(x,Y)=sum_(n>=1) a_u(n)*n^d*exp(sign*2*pi*i*n*x)*Y^a*K_nu(2*pi*n*Y)`.
The polynomial arithmetic envelope and positive-argument Bessel envelope give a locally
uniform summable majorant on every compact positive-height interval, for arbitrary fixed
complex parameters. All degree-shifted families converge absolutely there.

The actual joint Frechet derivative is proved by differentiating each summand, bounding
both coordinate derivatives by a common summable sequence on a positive-height ball,
and applying the infinite-series derivative theorem. Its horizontal coefficient is
`sign*2*pi*i*F(u,nu,a,d+1,sign)`. Its vertical coefficient is exactly
`a*F(u,nu,a-1,d,sign)-pi*(F(u,nu+1,a,d+1,sign)+F(u,nu-1,a,d+1,sign))`.
The summed derivative is identified with these four shifted full families. Induction on
finite derivative order proves joint C-infinity regularity on `Y>0`.

The pre-existing signed square-root Whittaker tail is identically this family at
`a=m+1/2`. Both two-step Maass words are finite combinations of these exact tails.
Both Weyl constant terms are smooth through their literal complex height powers.
Consequently the scalar, raised, and lowered full cusp legs and the complete balanced
boundary current `Y^(-1)*raised(u)*lowered(u)*scalar(v)` have all finite joint spatial
jets at every positive height. No finite Fourier replacement or spectral half-plane
assumption enters these theorems.

This closes spatial regularity of the literal fixed-parameter cusp functions. It does
not yet identify the required KI scalar/vector harmonic types, commute spectral jets
with spatial differentiation, or prove the reconstructed first-order Einstein equation.
The generic field-to-source theorem above still states its angular C2 hypotheses;
these new cusp-regularity theorems are available for the correctly matched profiles.

## Closed actual scalar cusp equation

`ThetaCuspHawkingBMAngularScalarEquation` identifies actual `ScalarTwoJet.coordDeriv`
first derivatives and both pure second derivatives of the full infinite family.
Three Schlaefli order recurrences give
`s^2/4*(K_(nu+2)-2*K_nu+K_(nu-2))-s/2*(K_(nu+1)+K_(nu-1))=nu^2*K_nu`.
The real half-power shifts then yield the exact equation of every weighted signed
summand at every positive height. Absolute convergence of all shifted families
passes this identity to their complete infinite sum. Both literal Weyl monomials
satisfy the same actual differential equation, and the operator respects their
local germs and linear combination.

Thus the pre-existing literal scalar cusp leg E_u satisfies
`Y^2*(partial_x partial_x E_u + partial_Y partial_Y E_u)=(u^2-1/4)*E_u`
for every complex u and every Y>0. The derivatives are taken from the actual field;
no supplied second-jet hypothesis or Y>=1 restriction remains. This theorem closes
the scalar chart equation. It does not by itself identify the coexact vector,
the reconstructed Einstein perturbation, or a selection law for u.

## Closed actual horizon covector geometry [BRIDGE]

`ThetaCuspHawkingBMHorizonCovectorEquation` derives the literal horizon metric
`g=Y^(-2)*diag(1,1)` and every connection entry from actual coordinate derivatives.
The nonzero entries are `Gamma^x_xy=Gamma^x_yx=-1/Y`, `Gamma^y_xx=1/Y`, and
`Gamma^y_yy=-1/Y`. The inverse in every contraction is the actual matrix inverse.
Both lower-index connection terms remain in the second covariant derivative:

- `nabla^2 V_x = Y^2*(V_x,xx+V_x,YY)+2Y*(V_x,Y-V_Y,x)-V_x`;
- `nabla^2 V_Y = Y^2*(V_Y,xx+V_Y,YY)+2Y*(V_Y,Y+V_x,x)-V_Y`;
- `div V = Y^2*(partial_x V_x+partial_Y V_Y)`.

The actual area-form/inverse-metric contraction gives
`V=(partial_Y S,-partial_x S)`. Actual second/third derivative symmetry proves
`div V=0` and `nabla^2 V=coexact(Delta S)-V`. Hence `Delta S=-q*S` implies
`nabla^2 V=-(q+1)*V`, retaining the curvature contribution. These are sixteen
kernel-checked public geometric theorems. They supply a bridge to the literal cusp
field, not a new independent selection conjecture or a spectral restriction.

## Closed literal cusp metric-source insertion [BRIDGE]

`ThetaCuspHawkingBMLiteralCuspMetricSource` uses the complete scalar cusp leg
`S_u=E_u` and its actual coexact covector `V_u`. Their scalar and rough vector
field equations have eigenvalues `q=1/4-u^2` and `q+1`; the vector is covariantly
divergence-free. The matched radial momentum `chi=-i*u` obeys `1/4+chi^2=q`.
All finite scalar/vector spatial derivatives follow from the literal infinite series.
No harmonic equation or angular regularity certificate is supplied as a premise.

Substitution into the fundamental reconstruction proves that its explicit full jet
equals the actual coordinate metric jet. The direct second and third derivatives of
the actual affine cosmological Einstein source are respectively the constructed
B and C forms evaluated on that literal full jet, with factors 1/2 and 1/6. Nine
public theorems close this insertion. These field identities hold for every complex
u and do not establish nonvanishing, global quotient admission, the reconstructed
first-order Einstein equation, or retained spin-two source identification.

## Closed first Einstein variation

`HTGeometry.CoordinateEinsteinComplexLinearization` differentiates the literal complete
jet. For background J, perturbation K, and G=J.metric^-1, its inverse variation is
D=-G*K.metric*G. The spatial inverse derivative varies as
`-(D*J.first[k]*G + G*K.first[k]*G + G*J.first[k]*D)`.
All connection, spatial connection, Riemann, Ricci and scalar product-rule terms are retained.
The final finite contraction is
`deltaEinstein = deltaRicci - (deltaScalar*J.metric + J.scalar*K.metric)/2`.

Twelve public theorems establish actual complex derivative identities, including
`einstein_eq_fderiv` on the complete metric-jet space and the fixed cosmological term.
`RHTower.ThetaCuspHawkingBMLinearizedEinsteinSource` then identifies
`deltaEinstein-3*K.metric` with the actual amplitude derivative of
`D4BMActualMetricSource.source`. Four public theorems include the full covariant
reconstruction and the literal fundamental profiles with fixed horizon geometry.
The first-order zero equation is exactly vanishing of this displayed finite contraction;
its vanishing for the literal cusp tensor is not established by these identities.
This is a proved bridge to the fixed tensor target, with no added selection conjecture.

## Exact reconstructed boundary metric

The boundary question is resolved directly from the corpus KI reconstruction, without a
numerical experiment. Let A=z^(-i*omega/2), b=(1-z)^(1/2), and Phi=A*b. The actual
fundamental derivative is `Phi'=Phi*(-i*omega/(2*z)-1/(2*(1-z)))`.
The original scalar orbit therefore obeys
`2*angularTrace = A*((q/2-i*omega)*(1-z)-z)`.
For positive physical radius, b at z=1-r^-2 is exactly r^-1. The normalized coefficient
tends to -1 at r→∞, while Phi tends to zero.

`RHTower.ThetaCuspHawkingBMFundamentalMetricBoundary` proves this exact identity,
the radius branch, and its insertion into the original full covariant tensor. Along
fixed time tau and horizon point u, the actual component has limit
`r^-2*h_22 → -aS*gamma_00(u)*S(u)*exp(-i*omega*tau)`.
On the physical upper half-plane its zero-limit condition is exactly
`aS=0 or S(u)=0`. Neither q nor omega nor vector amplitude aV cancels this leading
scalar coefficient. Ten public theorems include both the nonzero-limit obstruction
and its sharp positive vanishing classification.

This does not impose metric Dirichlet data, establish a gravitational boundary domain,
or retire HB. The surviving obligation is to derive the metric boundary observable and
admission condition used by the physical causal response; a vanishing master alone
cannot supply it. The scalar reconstruction agrees with equations 2.20–2.21 and
3.9–3.10 of [Kodama–Ishibashi](https://arxiv.org/pdf/hep-th/0305147).
The fundamental master equation and master Dirichlet convention are those in
[Birmingham–Mokhtari](https://arxiv.org/pdf/hep-th/0609028), equations 24–36.
These source checks support the formula identification; the boundary statements above
are proved by Lean from the corpus definitions.

## Closed literal scalar first-order Einstein equation

The full scalar tensor equation is closed through three source-identified leaves.
Write s=-i*omega, q=-(s+1)*(s+2), f=r^2-1, and
B=aS*exp(s*t)*z^(s/2), with z=1-r^-2 on the exterior. The original KI reconstruction equals
B*S times the symmetric matrix with entries

- tt: s*(s-3)/2+s*(s+1)/(2*r^2);
- tr and rt: -s*(r^2-s)/(r*f);
- rr: the tt entry divided by f^2;
- xx and yy: (-r^2-s*(s+1)/2)/y^2;
- all other entries: zero.

`D4BMFundamentalScalarMetric.reconstruction_eq` proves equality with the
original covariant recipe, including its actual master derivative. `envelope_jet` proves
the actual full B jet by the coordinate and logarithm chain rules. In particular,
B_r=s*B/(r*f) and B_rr=B*(s^2-s*(3*r^2-1))/(r^2*f^2); the temporal/radial mixed derivative
is retained. The rational matrix entries also receive their actual complete jets.

`ThetaCuspHawkingBMScalarLinearizedRicciJet` proves deltaRicci+3*h=0 in all sixteen
components of the separated jet. Angular first derivatives and the traceless angular
Hessian remain arbitrary; only the scalar Laplacian relation eliminates S_yy. The
background Ricci identity derives deltaScalar=0 and hence the complete cosmological
Einstein equation. This finite calculation is a `[BRIDGE]` to the fixed tensor target.

`D4BMScalarLinearEquation.field_jet` in `ThetaCuspHawkingBMScalarLinearEinsteinEquation` closes that bridge: the solved
jet is the actual complete coordinate jet of the scalar field. Its angular pullback
retains both ordered mixed derivatives, with their equality proved from C2 regularity.
Local equality of the reconstructed and separated fields identifies their full jets.
`reconstructed_source_first_zero` therefore gives the actual zero amplitude derivative
of `D4BMActualMetricSource.source`, rather than an independently assigned residual.

Finally, `literal_plus_source_first_zero` and `literal_minus_source_first_zero` substitute
the complete literal cusp scalar, using its proved regularity and scalar equation.
The rates s=-u-3/2 and s=u-3/2 both give q=1/4-u^2 and exactly the existing fundamental
QNM branches at radial momentum -i*u. Both theorems hold for every complex u, scalar
amplitude, exterior point and component, with vector amplitude zero and no supplied
field-equation premise. All Fourier modes and Weyl terms remain. These local equations
do not select spectral parameters or establish physical boundary admission.

## Next physical source evaluation

The scalar-sector first-order target is proved. The next exact target is the analogous
zero amplitude derivative for the literal coexact-vector sector, retaining its full
angular covector jet and actual rough-Laplacian/divergence equations. The source formula
reduces to h_tA=-s*B*V_A/r and h_rA=-s*B*V_A/(r^2-1). Its complete angular
jet must also retain both differentiated divergence equations. The separated vector
jet and its actual-field identification are `[BRIDGE]` targets to the same fixed tensor
equation; no response or spectral selection law is introduced. Then combine the
sectors through the actual linearized operator. Derive the physical metric boundary
condition with the nonzero scalar boundary coefficient retained. Any required
spectral/spatial derivative interchange for retained angular jets remains explicit.

The fundamental ingoing/Dirichlet radial inputs and matching horizon geometry are proved;
the mixed dressed monodromy's outgoing incidence remains explicit in the scattering basis.
Reduce the complete B,C source evaluations, identify second- and third-order field corrections,
nonlinear gauge completion and exceptional mixed-sector constraints, and retain causal
turn-on and boundary terms. Then prove the complete source belongs to the physical causal
response domain, identify the final left-QNM projection, and prove fixed Hawking-clock
extinction. No route retired; RH remains open in the corpus.

## Foundation validation

Scratch `lake env lean` checks passed without warnings. Normal main-workspace preflights found
only the new leaves out of date. Sequential final targeted builds passed:

- `lake build GaloisForLFunctions.HTGeometry.CoordinateCurvatureTwoJet`: 1.5 seconds, only new leaf compiled.
- `lake build GaloisForLFunctions.HTGeometry.MatrixAffineInverseCubicRemainder`: 1.9 seconds, only new leaf compiled.

Both leaves are wired into `HTGeometry.lean`. No umbrella or full build ran. A single scratch
axiom audit checked all 14 new public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
Existing theorem axioms were not re-audited. The source bytes matched the checked scratch
files and each foundation leaf has exactly one umbrella import. Foundation scratch/process
cleanup completed. The full Einstein source objective remains in progress; current global
validation is recorded below.

## Current diagonal coefficient validation

Scratch `lake env lean` checks passed without warnings. Sequential normal main-workspace
preflights found only each new leaf out of date, and targeted final builds passed:

- `lake build GaloisForLFunctions.HTGeometry.CubicDerivativeCurve`: 1.5 seconds, only this leaf compiled.
- `lake build GaloisForLFunctions.HTGeometry.CoordinateEinsteinAffineCoefficients`: 1.9 seconds, only this leaf compiled.

Both new leaves are wired once in `HTGeometry.lean`. The checked source bytes match the canonical
files. One scratch axiom audit checked all 22 new public theorems: only `propext`,
`Classical.choice`, and `Quot.sound`. Earlier axioms were not re-audited. Index generation and
`scripts/formal_tools.py lint --check-generated` passed. Scratch files were removed and no
owned Lean/Lake process remains. No full, umbrella, or dependency rebuild ran.

## Current mixed-variation validation

`lake env lean` scratch checks passed without warnings. The normal main-workspace preflight
reported only the new leaf out of date. Final targeted
`lake build GaloisForLFunctions.HTGeometry.CoordinateEinsteinMixedVariations` passed in
19 seconds, compiling only that leaf. No full, umbrella, or dependency rebuild ran.

The 347-line checked source matches the canonical file byte for byte and is imported once in
`HTGeometry.lean`. One scratch axiom audit checked all 16 new public theorems: only `propext`,
`Classical.choice`, and `Quot.sound`. No existing theorem axioms were re-audited.

Index generation passed. The global `scripts/formal_tools.py lint --check-generated` gate reports
one module outside this work as unreachable from its theorem-area umbrella:
`RHTower.HarmonicGeometricBounds`. The new Einstein leaf is reachable. An observed concurrent
umbrella change justified one index refresh and lint retry; the remaining error is recorded here.
Other modules were not modified. Owned scratch and process cleanup completed.

## Current complex-variation validation

The scratch proof check passed. Two tactic-style warnings were corrected before the final audit;
the final targeted build passed with no warnings. The normal preflight found only the new leaf
out of date. `lake build GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexVariations`
compiled only that leaf in 5.1 seconds. No full, umbrella, or dependency rebuild ran.

The 439-line source matches the scratch bytes and is wired exactly once in `HTGeometry.lean`.
One scratch axiom audit checked all 17 new public theorems: only `propext`, `Classical.choice`,
and `Quot.sound`. Existing theorem axioms were not re-audited. Mathlib-name scratch checks and
`git diff --check` for the touched scopes passed.

Index generation passed. The global `scripts/formal_tools.py lint --check-generated` gate reports
one unrelated module unreachable from its theorem-area umbrella:
`RHTower.ThetaCuspNativeSixthRankBoundary`. The new complex Einstein leaf is reachable; the other
module was not modified. Owned scratch/process cleanup completed.

## Current full-metric reconstruction validation

Both `lake env lean` scratch checks passed without warnings. The 294-line scalar calculus
and 287-line full metric reconstruction match their checked scratch sources byte for byte;
each is imported exactly once by its theorem-area umbrella.

- `lake build GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus` passed in 2.1 seconds in
  the main workspace, compiling only that leaf.
- The full-metric main-workspace no-build preflight requested eight older dependency rebuilds.
  An isolated local audit package used the exact new source and absolute cached dependency
  libraries. Its preflight required only the new leaf. Final
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullMetricTwoJet` passed in
  9.3 seconds, compiling only that leaf. Only its `.olean` and `.ilean` were installed into
  the main cache; no dependency or trace metadata was changed.

One scratch axiom audit checked all 16 new public theorems: only `propext`, `Classical.choice`,
and `Quot.sound`. Existing theorem axioms were not re-audited. No computational certificate,
full build, umbrella build, or dependency rebuild was used.

Index generation and scoped `git diff --check` passed. The global
`scripts/formal_tools.py lint --check-generated` gate reports three unrelated concurrent
modules unreachable from their theorem-area umbrellas: `RHTower.ThetaCuspCenterCompensationFlux`,
`RHTower.ThetaCuspCenterMixedAllOrderIntegration`, and `HTGeometry.AlternatingPairJetIntegral`.
Both new leaves are reachable; those other modules were not modified.
The owned scratch directory and isolated audit package were removed; no owned Lean/Lake
process remains.

## Current background and affine-source validation

Both new proof bodies passed `lake env lean` scratch checks without warnings. The final sources
are 257 lines (`ThetaCuspHawkingBMBackgroundMetricTwoJet`) and 227 lines
(`ThetaCuspHawkingBMActualAffineMetricSource`); both match the scratch and audit-package bytes
and each is imported exactly once by `RHTower.lean`.

The imports include the previously audited full metric reconstruction, whose leaf artifacts
were installed without main-workspace rebuild metadata. An isolated local audit package used
the exact new sources and absolute cached dependency libraries. Sequential no-build preflights
required only the respective new leaf. Final targeted builds passed without warnings:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBackgroundMetricTwoJet`: 19 seconds.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMActualAffineMetricSource`: 5.4 seconds.

Only these new leaves compiled; the second build reused the finished background leaf. Only
their `.olean` and `.ilean` artifacts were installed in the main cache. No dependency or trace
metadata was modified, and no full, umbrella, or dependency rebuild ran. All symbolic curvature
and derivative identities are Lean proofs, with no computational certificate supplied.

One scratch axiom audit checked all 17 new public theorems: only `propext`, `Classical.choice`,
and `Quot.sound`. Previously audited theorem axioms were not rechecked. Index generation and
scoped `git diff --check` passed. Global `scripts/formal_tools.py lint --check-generated` reports
three unrelated concurrent modules unreachable from their theorem-area umbrella:
`RHTower.ThetaCuspAllOrderLikelihoodCooling`, `RHTower.ThetaCuspFirstAtomAllOrderApproximation`,
and `RHTower.ThetaCuspFirstAtomReflectionJets`. Both new leaves are reachable; the other modules
were not modified.
The owned scratch directory and isolated audit package were removed; no owned Lean/Lake
process remains.


## Current dressed radial master validation

The 368-line `ThetaCuspHawkingBMPhysicalMonodromyMaster` passed scratch `lake env lean`
without warnings. An isolated package reused the existing dependency oleans and checked exact
source bytes. Its preflight requested only the new leaf; final
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalMonodromyMaster`
passed in 46 seconds, with only that leaf compiled. Only its olean/ilean were installed in the
main cache; no dependency trace metadata was copied. The leaf is wired exactly once into
`RHTower.lean`, which was not built. No full build ran.

One scratch axiom audit checked all 19 new public theorems. Every result uses only
`propext`, `Classical.choice`, and `Quot.sound`; existing theorem axioms were not rechecked.
Corpus index generation and scoped whitespace checks passed. Global
`scripts/formal_tools.py lint` reports one unrelated concurrent unwired module,
`RHTower.MobiusDivisorPositivePrimeSupply`, and 132 existing large-file warnings. It reports
no error in the new leaf. All owned process handles completed and the owned scratch directory
was removed. The RH goal remains active; causal profile and angular completion, complete
physical source/projection, and fixed-clock extinction remain open.


## Current fundamental profile validation

The 314-line `ThetaCuspHawkingBMFundamentalMetricSource` passed scratch `lake env lean`
without warnings. An isolated exact-source package reused cached dependencies. Its preflight
required only the new leaf, and final
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalMetricSource`
passed in 5.0 seconds; only that leaf compiled. Its olean/ilean were installed without copying
dependency trace metadata. The leaf is wired exactly once into `RHTower.lean`; no umbrella
or full build ran.

One scratch axiom audit covered the 22 new public theorems and no existing theorem. All use
only `propext`, `Classical.choice`, and `Quot.sound`. Corpus index generation, scoped whitespace
checks, and `scripts/formal_tools.py lint` passed; lint retains 132 existing large-file warnings.
All owned processes completed and the owned scratch directory was removed. No numerical
experiment ran. The full RH objective remains active with the analytical and physical
obligations listed above.

## Current joint angular validation

Three exact-source leaves passed scratch `lake env lean` without warnings:
`ThetaCuspHawkingBMAngularSeriesBounds` (126 lines, four public theorems),
`ThetaCuspHawkingBMAngularSeriesSmooth` (192 lines, six), and
`ThetaCuspHawkingBMEisensteinCuspJointSmooth` (140 lines, fourteen).
Their isolated final `lake build GaloisForLFunctions.RHTower.<leaf>` audits reused
cached dependencies and compiled only the requested new leaves, in 6.8, 8.0, and
8.6 seconds respectively. Source copies were byte-checked; only the new olean/ilean
files were installed, without dependency trace metadata. All three leaves are wired
once into `RHTower.lean`; no umbrella or full build ran.

One scratch axiom audit covered these 24 new public theorems only. Every result uses
only `propext`, `Classical.choice`, and `Quot.sound`; no computation certificate or
added axiom occurs. Corpus index generation, scoped whitespace checks, and formal
lint passed; lint retains 132 existing large-file warnings. Owned Lean processes
completed, and the owned scratch directory was removed. No numerical experiment ran.
The full RH objective remains active; the next physical obligations are stated above.

## Current actual scalar equation validation

The 301-line `ThetaCuspHawkingBMAngularScalarEquation` passed scratch `lake env lean`
without warnings. Its isolated exact-source final
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularScalarEquation`
passed in 5.2 seconds, compiling only this new leaf against existing cached dependencies.
The source copies were byte-checked and only the new olean/ilean were installed;
no dependency trace metadata was copied. The leaf is wired once into `RHTower.lean`.
No full or umbrella build ran.

One scratch axiom audit covered the 16 new public theorems only. All depend solely on
`propext`, `Classical.choice`, and `Quot.sound`. Index generation, scoped whitespace
checks and formal lint passed; lint retains 132 existing large-file warnings. Every
owned Lean/Lake process completed, and the owned scratch directory was removed.
No numerical experiment ran. The complete physical-source obligations above remain open;
the RH objective remains active.


## Current horizon and literal-source validation

The 364-line `ThetaCuspHawkingBMHorizonCovectorEquation` and 110-line
`ThetaCuspHawkingBMLiteralCuspMetricSource` passed scratch `lake env lean` checks.
Their final exact-source, cache-only audits passed without proof warnings:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonCovectorEquation`: 8.9 seconds.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCuspMetricSource`: 203 seconds.

Each build compiled only its requested new leaf. Scratch, canonical and audit source
bytes were compared; only new olean/ilean artifacts were installed. Both leaves are
wired exactly once into `RHTower.lean`. No full or umbrella build ran.

A concurrent workspace build left five needed dependency oleans unavailable. Exact
unchanged copies of those five sources were checked sequentially with foreground
`lake env lean`, restoring only their missing oleans. No dependency source or trace
metadata was changed, and no existing theorem axiom audit was repeated.

One audit per new leaf checked its 16 and 9 public theorems, respectively. All 25
use only `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or numerical
certificate occurs. Corpus index generation passed. Global formal lint reports two
unrelated concurrent modules missing their theorem-area umbrella imports:
`RHTower.PartialSubsetEnergyOrder` and `RHTower.ThreePlaneSourceMargin`, plus large-file
warnings. Both new HB leaves are reachable. Those other modules were not modified.

All owned Lean/Lake processes completed. The 119 owned scratch entries, including
both isolated audit packages and the required dependency-repair copies, were removed.
No numerical experiment ran: the geometric identities were derived symbolically, so
an experiment would not distinguish unresolved possibilities. The reconstructed
first-order Einstein equation and the full causal-source/extinction chain remain open;
the RH goal remains active.

## Current linearization and boundary validation

The new leaves passed scratch `lake env lean` without warnings. Exact-source,
cache-only final audits each compiled only the requested new leaf:

- `lake build GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexLinearization`: 5.0 seconds; 250 lines, 12 new public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLinearizedEinsteinSource`: 4.3 seconds; 89 lines, 4 new public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalMetricBoundary`: 5.1 seconds; 205 lines, 10 new public theorems.

Scratch, canonical and audit source bytes were compared. Only the new olean/ilean
artifacts were installed; dependency sources and trace metadata were not changed.
All three leaves are wired exactly once into their respective umbrellas. No full or
umbrella build ran. One foreground Lean/Lake process ran at a time.

Only the 26 new public theorems received axiom audits, once each. All use solely
`propext`, `Classical.choice`, and `Quot.sound`. Corpus index generation, scoped
whitespace checks, and global formal lint passed; lint retains existing large-file
warnings. All owned Lean/Lake processes completed, and the owned scratch directory
was removed after an exact inventory. Other agents' processes were left untouched.
No numerical experiment ran. The exact tensor zero equation, physical metric boundary
admission, retained-source identification and causal extinction remain open; RH remains
unproved in the corpus.


## Current literal scalar tensor validation

All three new leaves passed foreground scratch `lake env lean` checks without warnings.
Final exact-source cache-only builds compiled only the requested leaf:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearizedRicciJet`: 198 seconds; 156 lines, 4 new public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalScalarMetric`: 18 seconds; 254 lines, 6 new public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearEinsteinEquation`: 10 seconds; 320 lines, 6 new public theorems.

Scratch, canonical and audit bytes match. Each leaf has exactly one `RHTower.lean`
import. Only the new olean/ilean artifacts were installed; dependency sources and trace
metadata were untouched. No full or umbrella build ran. Only one owned Lean/Lake
process ran at a time. All sixteen new public theorems received one axiom audit each;
all use only `propext`, `Classical.choice`, and `Quot.sound`.

Corpus index generation and scoped whitespace checks passed. Global formal lint finds
five unrelated concurrent modules missing their theorem-area umbrella imports:
`ConstrainedWeilWeightedRayBounds`, `RetainedPrimeDivisorConvolution`,
`RetainedPrimeMobiusEulerIdentity`, `RetainedPrimeSourceMellin`, and
`SquareRootSummatoryMellin`, all in `RHTower`. The new HB leaves are reachable;
those unrelated modules were not modified. Existing large-file warnings remain.

The scalar tensor equation is proved at both fundamental branches. Vector-sector
first-order compatibility, metric boundary admission, retained spin-two/AIME source
identification, nonlinear/gauge completion and physical causal extinction remain open.
No numerical experiment ran: the remaining checks here were symbolic identities.

All owned Lean/Lake processes completed. The exact 77-entry owned scratch tree was
removed after checking for symlinks; other tasks' processes and files were preserved.
