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
The remaining source task is to instantiate the physical profiles, derive the nonlinear
field/gauge corrections, and connect the complete source to the physical causal action and
final left-QNM projection.

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

## Next physical source evaluation

Joint angular regularity is being derived from the literal signed Fourier--Bessel family,
not from separate partial derivatives alone. For fixed arithmetic parameter u, Bessel order nu,
real height power a, index degree d and Fourier sign, retain the full infinite sum of
`a_u(n)*n^d*exp(sign*2*pi*i*n*x)*Y^a*K_nu(2*pi*n*Y)`.
Horizontal differentiation increases d by one. Vertical differentiation is the sum of
`a` times the family at `(a-1,d,nu)` and `-pi` times the two families at
`(a,d+1,nu+1)` and `(a,d+1,nu-1)`. The corpus's polynomial arithmetic envelope and
positive-argument Bessel envelope provide locally uniform summable bounds on every
positive-height neighborhood. Prove the actual joint Frechet derivative, then induct on
smoothness using this derivative-stable family. Finally identify the existing scalar and
finite Maass-word cusp legs with these literal sums and their constant terms. No stronger
spectral convergence chamber or finite-mode replacement is intended.

Instantiate the literal scalar/vector horizon profiles with multivariate regularity and the
correct harmonic equations, and verify the reconstructed first-order Einstein equation.
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
