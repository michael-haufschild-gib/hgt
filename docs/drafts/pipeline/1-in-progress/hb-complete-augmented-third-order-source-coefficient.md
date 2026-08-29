# HC94 — Complete augmented third-order Einstein–Teukolsky source coefficient

Status: in progress

Route: HB, with shared FZZ-P / PW-B / RBH Ward receiver

## Hard frontier question

Evaluate the coefficient-normalized, gauge/constraint/corner-completed third-order `++-`
Einstein–Teukolsky source before Xi-divisor selection. This is the explicit open core in the
read-only RH frontier map and is strictly upstream of all already-formalized darkness, Ward,
Evans, Cayley, and full-cokernel RH receivers.

## Corpus basis

Mandatory corpus searches:

- `scripts/formal_tools.py research "complete third-order ++- Einstein Teukolsky source coefficient invariant on-shell class B p Rpm B p m Rpp C projected resonant amplitude"`
- `scripts/formal_tools.py research "actual gauge-fixed Einstein bilinear Hessian trilinear third variation BM mode explicit B C Teukolsky source projection"`
- `scripts/formal_tools.py research "self-dual quadratic source retarded plus plus response mixed stationary response mass memory explicit coefficient third order cascade BM"`

Corpus facts:

- The full augmented residual has exact Schur form
  `B(p,Rpm(B(p,m))) + B(m,Rpp(B(p,p)/2)) + C(p,p,m)/2`.
- Causal time convolution and the simple negative-branch BM Jost pole are already exact and cannot
  create or erase the total angular cokernel.
- The physical AIME numerator is explicit and nonzero at every Xi divisor for nonzero seed.
- Second-order sources, passive stationary absorption, finite local pump packets, and finite-energy
  continuum returns cannot supply the required third-order counterterm.
- Field redefinitions redistribute the three non-AIME channels but preserve their aggregate
  on-shell class.
- What is absent is concrete Einstein data for `C` and the complete augmented response maps
  `Rpp`, `Rpm`; lower-order data alone allow an arbitrary third-jet cokernel correction.

## Frozen conjecture HC94-A

After constructing the literal d=4 massless topological-AdS Einstein residual, its BM gravitational
linear branches, complete retarded `++` and stationary `+-` augmented responses, and the conserved
left QNM projection, the complete source section factors as

`S_full(q) = T_full(q) * D_clock(q)`,

where `D_clock` is the existing centered source-FE/QNM clock defect and `T_full(q)` is nonzero on
every Xi copy. Consequently the complete coefficient vanishes exactly on the critical line, and
universal complete-source extinction is equivalent to `RiemannHypothesis`.

No factor or map may be defined by the desired equality. `B`, `C`, `Rpp`, `Rpm`, the augmented
boundary traces, and the left projection must be constructed from the Einstein–Teukolsky equations
and existing BM mode data before the factorization is proved.

## Conjecturing loop

1. Construct the smallest source-faithful explicit Einstein jet carrier supporting the actual BM
   branches and augmented horizon/AdS traces.
2. Derive `B`, `C`, `Rpp`, and `Rpm` from the residual; do not insert a target coefficient.
3. Compute the closed Schur section and test HC94-A.
4. If factorization fails, retain the exact computed coefficient, classify its zero/reflection
   locus, and freeze the strongest source-derived replacement conjecture.
5. If the coefficient admits unconditional tilted cancellation, extract the exact positive
   survivor and retire that HB producer only after formalizing the survivor.

## Loop result HC94-A.1 — universal Mellin kernel proved; single-mode shortcut rejected

The new module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingSelfDualGeneralMellinVertex` proves the exact
Gamma-normalized curvature-corrected Plebanski kernel

`V(c,a,b,h,k) = ((a*k-b*h)^2 + a*k^2 + b*h^2
  - c*(h-k)*(a+b+1)*(a*k-b*h))/2`

for arbitrary unequal exponents and transverse charges in its convergence chamber. The
equal-charge specialization is `h^2*((a-b)^2+a+b)/2`, recovering the prior diagonal result when
`a=b`. Targeted build passed `11214/11214`; axiom audit returned only `propext`,
`Classical.choice`, and `Quot.sound`; formal lint reported no finding in the new module.

**Failed conjecture HC94-A.1-F.** Cusp-grade addition alone does not permit evaluating the
second-harmonic cascade by substituting one doubled Mellin exponent into this kernel. Corpus audit
shows the actual `Rpp` object is the BM hypergeometric Green response. Its radial profile is not
proved to be one Mellin monomial, and the self-dual chiral restriction does not by itself construct
the full `++-` Einstein source containing a negative-helicity branch. Treating it as such would
insert the desired source data rather than derive it.

**Pivot HC94-A.2.** Evaluate the Plebanski vertex convolved with the exact BM `++`
hypergeometric Green response and the reflected linear branch. Only after this integral and its
augmented boundary terms are closed may it be combined with the stationary `+-` cascade and the
direct third variation.

## Literature audit through 2026-08-28

- Birmingham–Mokhtari, arXiv:hep-th/0609028, provides exact d=4 massless topological-black-hole
  gravitational master modes and boundary coefficients.
- Green–Hollands–Sberna–Toomani–Zimmerman, arXiv:2210.15935, provides conserved QNM bilinear
  currents and left/right resonance normalization.
- Spiers–Pound–Moxon, arXiv:2305.19332 (revised 2026), provides an explicit nonlinear source for a
  reduced second-order Teukolsky equation, not this third-order topological-AdS `++-` section.
- Lestingi–Sberna–Green, arXiv:2607.19492, provides QNM perturbation theory and source projection,
  not the coefficient above.
- Targeted primary-source searches found no evaluation or clock-defect factorization of this
  complete coefficient. This is a bounded novelty audit, not an exhaustive literature claim.

## Lean audit checklist

- [ ] Explicit source data constructed independently of desired factorization
- [ ] Foreground scratch proof with `lake env lean /tmp/hc94.lean`
- [ ] No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [ ] Closed theorem and `#print axioms` audit
- [ ] Add module and wire `GaloisForLFunctions.RHTower`
- [ ] Targeted module build only
- [ ] Formal lint has no HC94 finding
- [ ] Promote proven result or record failed conjecture and positive survivor

## Loop result HC94-A.2 — exact second-jet corner law and nonzero finite part

Corpus-led endpoint analysis falsified the unrenormalized radial-source shortcut. The module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicSecondDerivativeEdge` proves

`(1-z)*sqrt(1-z)*Rpp''(z) → (sqrt(pi)/2)*Gamma(c)/(Gamma(a)*Gamma(b))`,

with nonzero coefficient on every Xi fibre, and proves that `Rpp''` has no finite unrenormalized
AdS endpoint. Thus a third-order radial source using the bare second derivative is not defined;
an explicit corner counterterm is mathematically forced. Targeted build passed `11171/11171`;
axiom audit returned only `propext`, `Classical.choice`, and `Quot.sound`; formal lint reported no
finding in the module.

**Failed conjecture HC94-A.2-F.** Subtracting only the leading square-root singularity is not a
source-faithful renormalization. Exact Gauss connection data show that all subleading terms of the
normalizable AdS branch remain part of the singular corner jet. A leading-asymptotic subtraction
would leave a scheme-dependent finite part and cannot feed the coefficient-normalized cubic
source.

**Positive survivor HC94-A.2-P.** The new module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicCornerRenormalizedSecondDerivative`
proves the exact second-jet connection

`Rpp'' = A_forbidden*S_forbidden'' + A_normalizable*S_normalizable''`

on the radial interior. Subtracting the *full* normalizable branch leaves a finite endpoint

`FP = A_forbidden * a*(a+1)*b*(b+1)/(c*(c+1))`.

This finite part is nonzero for every admissible angular parameter and, premise-free, for every
mode and Xi zero copy. Therefore the corner-completed radial cascade contains an unavoidable,
explicit nonzero source coefficient; it cannot be extinguished by regularity or corner
renormalization alone. Targeted build passed `11173/11173`; both premise-free Xi theorems have
axioms exactly `propext`, `Classical.choice`, and `Quot.sound`; formal lint reported no finding in
the module. Both new modules are wired into `GaloisForLFunctions.RHTower`.

**Pivot HC94-A.3.** Apply the actual coefficient-normalized Plebanski/Einstein radial differential
vertex to the corner-renormalized BM response. The exact nonzero finite part above fixes the radial
boundary datum; remaining work is to derive the interior projected radial integral and combine it
with stationary `+-` response plus direct third variation before testing HC94-A.

## Loop result HC94-A.3 — constant-curvature convolution proxy retired

`[FALSIFIED]` The abstract `curvature : ℂ` Mellin kernel cannot be specialized to one constant and
used as the physical AdS4 radial vertex. Lipstein–Nagy's exact plane-wave factor is

`X(k1,k2) * (X(k1,k2) - 2i*(k1-k2)_w/(u-v))/2`,

with `u-v=2z`. Chowdhury–Doran–Lipstein–Monteiro–Nagy–Singh's arbitrary-propagator vertex instead
contains left/right `z` derivatives and acts on `P/z` and `Q/z`. Thus the curvature deformation is
radial and operator-valued; the constant-curvature convolution omits source data essential to
HC94. This is an exact parent-theory obstruction, not a numerical inference.

Exploratory RunPod work on the retired proxy is recorded at
`docs/drafts/pipeline/2-fully-proven/computations/2026-08-28-hc94-plebanski-bm-convolution/REPORT.md`.
At 90 digits all 135 sampled `c=1` cases were nonzero; direct quadrature agreed with beta–`3F2`
evaluation to `1.25e-95`. Exact symbolic elimination inside the proxy found a unique
profile-independent annihilator `k=-h, c=-1/2`. This is not a physical cancellation because the
physical coefficient is proportional to `1/z`. Computation is route-selection evidence only and
is forbidden as a Lean dependency.

`[BRIDGE]` The surviving representation is the radial deformed-kinematic operator itself, not a
scalar Mellin moment. Further special-function scans of the constant-curvature proxy are retired.

**Pivot HC94-A.4 / `[OPEN CORE]`.** Pull the physical Poincaré light-cone operator through the exact
massless topological-black-hole/BM radial chart, apply its left/right derivatives to the fully
corner-renormalized `Rpp` response and negative-helicity branch, and include the negative leg,
gravity boundary/corner completion, and conserved left-QNM projection. Only this derived operator
may be combined with stationary `+-` response and direct third variation to attack HC94-A.

## Loop result HC94-A.4 — scalar BM-radial physical vertex is impossible

Jevicki--Suzuki's exact massless-topological-black-hole chart has `rho=r⁻¹`,
`z_BM=1-rho²`, and Poincare radial coordinate `Z=rho*sigma`. Hence one BM radial fibre contains
the full positive `Z` ray. The module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalPoincareRadialNoGo` proves the sharp
classification: a scalar Poincare-radial profile factors through `z_BM` on the exterior iff it is
constant on `Z>0`. Therefore `1/Z` does not descend. After inserting the physical self-dual
coefficient `2i/(u-v)=i/Z`, an explicit unequal-charge plane-wave probe also has two distinct
values at the same BM radius. This is a theorem-level retirement of every scalar BM-radial
specialization of the physical Plebanski curvature term, not numerical evidence.

The inverse-Jacobian module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPoincareRadialDerivativePullback` proves from actual
chart derivatives that

`partial_Z = rho*partial_sigma + (1-rho²)/sigma*partial_rho`.

It annihilates the pulled-back Poincare `T,Y` coordinates and sends `Z` to one. Acting on a BM
first radial jet whose BM derivative is `J` gives

`-2*rho*(1-rho²)*J/sigma`.

The existing nonzero corner finite part and its proved endpoint convergence imply, premise-free
for every mode and Xi zero copy, an actual interior BM radius where the corner-renormalized second
derivative is nonzero. At that radius the physical `partial_Z` action differs between
`sigma=1` and `sigma=2`. Consequently even the actual corner-renormalized derivative carrier
cannot factor through BM radius alone. The proof does not extend an endpoint value as a constant
bulk jet.

Targeted builds passed `11250/11250` and `11253/11253`. Headline theorem axiom audits returned only
`propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into
`GaloisForLFunctions.RHTower`. Global formal lint reported no finding in either module but remains
red because unrelated concurrently present modules are not wired into their theorem-area
umbrellas.

**Positive survivor HC94-A.4-P.** The physical source is necessarily a two-coordinate
Rindler/hyperbolic differential source. Exact one-variable BM Green data remain valid inputs, but
only after tensor/harmonic reconstruction and the full inverse-Jacobian light-cone operator are
retained.

**Pivot HC94-A.5 / `[OPEN CORE]`.** Pull the remaining Poincare light-cone derivatives and the
complete unequal-helicity deformed kinematic bracket through the exact chart; reconstruct the
Birmingham--Mokhtari master modes to gauge-invariant metric components; then perform the
hyperbolic-harmonic product, negative leg, boundary/corner completion, and conserved left-QNM
projection. Scalar radial convolution is now formally excluded and must not be revisited.

## Loop result HC94-A.5 — full radial two-jet vertex and KI chiral reconstruction

The module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSelfDualDeformedTwoJetVertex` implements the literal
two-leg bidifferential vertex of Chowdhury--Doran--Lipstein--Monteiro--Nagy--Singh Eq. (100), with
the fixed `1/Z` denominator outside the left/right derivatives. The second pullback of a pure BM
profile is

`partial_Z^2 Phi = 2(1-rho^2)(4rho^2-1) sigma^-2 Phi'
  + 4rho^2(1-rho^2)^2 sigma^-2 Phi''`.

Thus the naive squared chain rule misses a forced first-jet connection term. After exact pullback,
the complete vertex is an explicit Laurent polynomial of degree at most two in `sigma^-1`; the
zeroth, first, and second coefficients retain separately the flat bracket, radial determinant,
connection, genuine second-jet, and AdS-curvature contributions. Exchange symmetry and recovery
of the existing bulk-to-boundary plane-wave vertex are proved. Direct `lake env lean` passed, and
the targeted module build passed `11254/11254`.

The scalar reconstruction module specializes Kodama--Ishibashi Eqs. (33)--(34) to the d=4
massless `K=-1` background and converts to BM jets. It proves

`2 rho Ztilde - (X+Y) = rho (k^2+2) Phi`,

so all BM first-derivative terms cancel from the recovered master field. On every actual Xi fibre,
`k^2+2` is nonzero, proved from the already-formalized nonzero real part of the analytically
continued BM momentum. Hence the exact Xi hypergeometric monodromy mode is recovered from its
gauge-invariant scalar metric orbit with no hypothesis. Direct Lean passed; targeted build passed
`11259/11259`.

The vector/chiral reconstruction module then specializes the source-free vector identity
`epsilon^{ab} D_b OmegaTilde = r F^a`. For matched scalar and vector master jets it proves the
unit-coefficient cancellation

`rho^2 Ztilde_scalar - rho F_t_vector = Phi`.

The stronger mismatch law shows the only derivative obstruction is the difference of the scalar
and vector first jets. Differentiating reconstructed metric components twice introduces an
arbitrary third BM derivative in each parity sector, but it cancels exactly: the chiral carrier
recovers `(Phi,Phi',Phi'')` independently of every third-jet extension. Substitution into the full
Eq. (100) pulled-back vertex is therefore identical to direct substitution of the BM master
two-jets. The actual Xi carrier equals the corpus's exact monodromy mode, not a fitted amplitude.
Direct `lake env lean` passed.
Targeted build passed `11260/11260`.

**Novelty status.** Primary sources provide the KI scalar coefficients, vector master identity,
and Plebanski vertex separately. Targeted corpus and literature searches found no prior statement
of the scalar--vector unit-coefficient cancellation, its third-jet-independence, or the resulting
exact BM-to-Eq.-(100) two-jet bridge. This is a bounded novelty audit, not an exhaustive claim.

**Positive survivor HC94-A.5-P.** The missing master-to-metric radial bridge is closed. The
surviving obstruction is now geometric rather than radial: a BM separated mode is not a Poincare
plane wave. Therefore fixed transverse momenta cannot yet be attached to the reconstructed
carrier. The actual remaining source must use the full inverse-Jacobian Poincare boundary
derivatives on BM time/hyperbolic harmonics, followed by the harmonic product, negative leg,
gravity corner completion, and conserved left-QNM projection.

**Pivot HC94-A.6 / `[OPEN CORE]`.** Construct the full `partial_T`, `partial_Y`, `partial_Z`, and
`partial_X` pullback on separated BM time/hyperbolic jets; lift the coordinate-space Plebanski
bidifferential operator through that chart; then apply it to the exact chiral carrier two-jets.
Do not reuse fixed Poincare plane-wave charges for a BM separated mode.

## Loop result HC94-A.6 — full first Jacobian and fixed-momentum route killed

The rapidity substitution `rho=sech(xi)`, `sqrt(1-rho^2)=tanh(xi)` removes square-root edge
premises. The module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullPoincareDerivativePullback` constructs the three
globally defined scaled coordinate fields

`sigma*tanh(xi)*partial_T`, `sigma*tanh(xi)*partial_Y`,
`sigma*sech(xi)*partial_Z`

and proves unconditionally that they diagonalize the complete `(tau,xi,sigma)` chart Jacobian.
Together with `partial_X`, algebraic inverse-scale variables give the exact Poincare `T,X,Y,Z`
first jet, light-cone `u,w` derivatives, and their alternating kinematic bracket on arbitrary BM
first jets.

The sharp classification

`a normalized BM time eigenjet has one fixed Poincare-T charge on every hyperbolic scale
  iff its BM frequency is zero`

is Lean-proved. Existing corpus damping then specializes it premise-free: no positive-branch Xi
QNM admits a single fixed Poincare momentum throughout a BM hyperbolic fibre. This formally kills
the remaining plane-wave-charge shortcut, rather than merely warning against it.

The module
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPlebanskiCoordinateJacobiVertex` implements the
literal position-space Jacobi double bracket from Chowdhury et al. Eq. (63):

`(f_uu*g_ww+g_uu*f_ww)/2 - f_uw*g_uw
 + (u-v)^-1*(f_uw*g_w+f_w*g_uw-f_ww*g_u-f_u*g_ww)`.

On Poincare plane-wave eigenjets, Lean proves the curvature term factors as
`-i*(u-v)^-1*X*(h-k)` and the full operator equals the existing vertex
`X*(X-2i*(u-v)^-1*(h-k))/2`. Thus momentum-space Eq. (100) is now proved to be an eigenjet
specialization of the coordinate-space operator. Both new modules pass direct `lake env lean`.

**Positive survivor HC94-A.6-P.** Full first-order light-cone transport is closed, and fixed
Poincare momenta are excluded for actual Xi QNMs. The exact finite remaining chart burden is the
second inverse-Jacobian transport of `partial_u^2`, `partial_u partial_w`, and `partial_w^2` on BM
time/hyperbolic/radial two-jets. Those three components feed Eq. (63) directly; no additional
guess about a Plebanski radial vertex is needed.

**Pivot HC94-A.7 / `[OPEN CORE]`.** Construct the three coordinate-space light-cone second jets,
apply Eq. (63) to the exact scalar--vector chiral carrier and corner-renormalized `++` response,
then perform harmonic product, negative-leg contraction, gravity corner completion, and conserved
left-QNM projection.

**HC94-A.6 formal audit.** The full-Jacobian target passed `11262/11262`; the coordinate Eq. (63)
target passed `11263/11263`. Axiom audits for all three Jacobian diagonalization theorems, the
fixed-charge classification, Xi-QNM nonvanishing and route-killer, and coordinate-to-plane-wave
Eq. (63) compatibility report only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint
reports no finding in any HC94-A.5/A.6 module; its remaining red entries are unrelated unwired
modules already present in the shared worktree.

## Loop HC94-A.7 — full Hessian closed; scalar angular sufficiency under hostile attack

`[CORPUS]` The exact pure-radial second pullback, full first inverse Jacobian, scalar--vector
chiral radial two-jet, Xi QNM frequency, angular eigenvalue, and scalar completed triple-Eisenstein
vertex exist. Corpus research finds no full horizon-polarized `(u,w,uu,uw,ww)` transport and no
Eisenstein first/traceless-second derivative vertex.

`[PAPER-PROVED] [LEAN-PROVED]` The full variable-coefficient chain rule
`V(Wf)=V^iW^jf_ij+V^i(partial_i W^j)f_j` and the complete rapidity-chart transport to
`u,w,uu,uw,ww` are formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPoincareLightConeSecondJetPullback`.
The map agrees with the earlier first Jacobian and feeds coordinate Eq. (63) directly. A physical
sigma-affine witness has zero principal Hessian term but exact `partial_Z^2=tanh(xi)^2`, proving
that the first-jet connection cannot be deleted. Direct Lean and targeted build pass
`11264/11264`; headline axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

`[CONJECTURE]` The scalar angular data already in the corpus--value, first scalar data, Laplacian
eigenvalue, and completed scalar triple-Eisenstein vertex--determine the pulled-back Eq. (63)
source. Hostile test: compare equal scalar signatures with opposite traceless horizon Hessian.
If Eq. (63) separates them, retire scalar-only angular contraction and replace it by a polarized
spin-two Eisenstein derivative vertex before negative-leg/left-QNM projection.

`[FALSIFIED] [PAPER-PROVED] [LEAN-PROVED]` Scalar angular sufficiency fails.  The zero BM two-jet
and the unit traceless horizon Hessian `f_xx=-1`, `f_sigmasigma=1` have identical value, complete
first horizon jet, and Laplacian trace.  At the physical rapidity-chart point
`(tau,xi,sigma)=(0,1,1)`, however, their diagonal pulled Eq. (63) sources are respectively zero and
exactly `-sech(1)^2/16`.  Since `sech(1)` is nonzero, no universal scalar-signature factorization
can determine the source.  This kills the scalar completed triple-Eisenstein-vertex shortcut
before it contaminates the negative-leg projection.

**Positive survivor HC94-A.7-P.** The missing angular datum is now sharply localized: any complete
source carrier must retain the spin-two/traceless horizon Hessian polarization, or an equivalent
polarized derivative Eisenstein vertex.  The witness and universal no-factorization theorem are
formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPlebanskiAngularPolarizationNoGo`, wired into the
RHTower umbrella.  Direct Lean and targeted build pass `11265/11265`; all three headline axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`.

**Pivot HC94-A.8 / `[OPEN CORE]`.** Classify the minimal polarized horizon two-jet quotient through
which the pulled Eq. (63) source factors, then identify the corresponding completed Eisenstein
derivative vertex for the actual Xi chiral carrier.  Only after that exact angular carrier is
closed should the negative leg and conserved left-QNM projection be composed into HC94.

## Loop HC94-A.8 — actual Xi radial carrier activates the spin-two source

`[CORPUS]` The exact Xi monodromy mode has a nonzero punctured-complex Frobenius limit, but the
corpus previously proved nonvanishing only at an unspecified complex BM radius.  It also contains
the exact surjectivity `tanh '' (0,infinity)=(0,1)`.  No theorem placed the monodromy carrier on a
positive real BM radius or coupled it to the pulled spin-two Eq. (63) source.

`[PAPER-PROVED] [LEAN-PROVED]` The punctured limit pulls back along the real embedding, so every Xi
fibre has `z in (0,1)` where its exact monodromy mode is nonzero.  Writing `z=tanh(xi)^2`, `xi>0`,
and scaling the traceless horizon Hessian by that actual mode gives the exact local source

`-sech(xi)^2 * mode(tanh(xi)^2)^2 / 16`.

It is nonzero for every Xi copy, all overtone labels, and every Eq. (63) curvature coefficient.
Thus radial darkness cannot make the missing polarized angular channel vacuous.  This is
formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMXiPlebanskiPolarizedSourceExistence`, wired into the
RHTower umbrella.  Direct Lean and targeted build pass `12046/12046`; headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

`[LITERATURE ATTACK]` Bonifacio, arXiv:2107.09674, treats spin-two/holomorphic-differential triple
overlaps on hyperbolic surfaces as independent tensor data; therefore a universal reduction of
polarized Hessian overlaps to scalar Laplace eigenvalues is false.  Kim, arXiv:2608.07774, confirms
that a Plebański scalar enters the metric through its fibrewise Hessian and that reconstructing it
is a light-cone gauge/inverse-Hessian problem.  Neither result supplies the topological-AdS BM/KI
lift or a Maass-raised Eisenstein triple vertex.

`[CONJECTURE HC94-A.9]` For the modular Eisenstein principal-series legs used by the existing
completed cubic vertex--not for arbitrary hyperbolic eigenfunctions--the precise spin-two
derivative contraction selected by the separated pulled Eq. (63) source equals the completed
scalar triple-Eisenstein vertex times the Maass raising/lowering coefficient fixed by the three
spectral parameters.  Required proof chain:

`KI chiral carrier -> separated pulled Eq. (63) tensor monomials -> Maass-raised Eisenstein triple
projection -> negative-helicity leg -> conserved left-QNM coefficient -> HC94 clock-defect
factorization -> RH endpoint`.

**Pivot HC94-A.9 / `[OPEN CORE]`.** Expand the separated pulled Eq. (63) source into exact horizon
spin weights, identify the required raising/lowering word on each Eisenstein leg, and prove its
completed trilinear coefficient.  Generic integration-by-parts or scalar-eigenvalue arguments are
retired; only principal-series intertwining can close this burden.

## Loop HC94-A.9a — exact balanced spin-two word

`[CORPUS-LED CONJECTURE]` The complete second-jet pullback and scalar-polarization no-go suggest
that the pure traceless horizon-Hessian sector should factor through the product of its local
`+2` and `-2` components.  This is the first tensor word required by the separated Eq. (63) source,
and it feeds the existing HC94-A.9 chain before negative-leg and left-QNM projection.

`[PAPER-PROVED] [LEAN-PROVED]` At `sigma=1`, define

`spinPlus = f_xx-f_sigmasigma+2i*f_xsigma`,

`spinMinus = f_xx-f_sigmasigma-2i*f_xsigma`.

For the unique pure traceless Hessian with prescribed `spinPlus,spinMinus` and zero value/first
jet, Lean recovers both components exactly and proves its entire scalar two-jet signature equals
that of the zero jet.  At every positive rapidity and every inverse-UV scale, the diagonal
BM-pulled Plebanski source is exactly

`-sech(xi)^2 * spinPlus * spinMinus / 64`.

The unit balanced pair is nonzero at every positive rapidity.  Hence this sector contains exactly
one local `+2` and one local `-2` factor; it cannot be replaced by scalar Laplacian data.  This is
formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPlebanskiBalancedSpinTwoSource`, wired into the
RHTower umbrella.  Direct Lean and targeted build pass `12047/12047`.  Headline axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`.

**Scope boundary.** Vanishing first jet makes these local components coincide with covariant
traceless-Hessian components at the chart point.  A generic separated Eisenstein leg has
connection corrections; the theorem identifies its required balanced tensor word but does not
yet prove the completed Maass-raised trilinear coefficient.

**Positive survivor HC94-A.9a-P.** The first unavoidable angular projection is a balanced
spin-two triple overlap, not an arbitrary spin-two tensor and not the existing scalar completed
vertex alone.  Remaining hard burden is to derive the precise Maass raising/lowering realization
of this local word for modular Eisenstein principal-series legs and then complete its trilinear
coefficient.

## Loop HC94-A.9b — tensor-to-Maass bridge

`[CORPUS-LED CONJECTURE]` The balanced local spin word from HC94-A.9a should be the two-step Maass
word `R_2 R_0` paired with `L_(-2) L_0`.  This is forced by the corpus full second jet and by the
geometric spin `+2/-2` classification: each Maass step changes modular weight by two, so the
traceless Hessian lies at modular weights `+4/-4`.

`[PAPER-PROVED] [LEAN-PROVED]` On every complete BM second jet and arbitrary complex horizon scale,
Lean proves

`R_2 R_0 = -(connection-corrected covariant spinMinus)`,

`L_(-2) L_0 = -(connection-corrected covariant spinPlus)`.

For a pure traceless jet the connection terms vanish, the two operators recover
`-spinMinus,-spinPlus`, and the complete pulled Eq. (63) source factors exactly through their
product.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPlebanskiMaassSecondJetBridge`, wired into the
RHTower umbrella.  Direct Lean and targeted build pass `12048/12048`; headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Positive survivor HC94-A.9b-P.** The angular burden is no longer an unspecified polarized
vertex.  It is the regularized modular-weight `(4,-4,0)` triple projection of two completed Maass
steps on the diagonal positive leg against the negative leg.  Because the positive leg is
diagonal, the balanced product is twice the covariant traceless-Hessian contraction; its
antisymmetric tensor obstruction cancels.  The next hard problem is an exact regularized weighted
Bochner/Stokes reduction to the existing completed scalar triple-Eisenstein vertex, including the
cusp boundary audit.

## Loop HC94-A.9c — exact completed coefficient and exhaustive cusp defect

`[CORPUS-LED CONJECTURE]` Combine the existing completed scalar triple-Eisenstein vertex with the
diagonal Maass word from HC94-A.9b.  For repeated-leg geometric eigenvalue `lambda=u^2-1/4`,
projecting-leg eigenvalue `mu=v^2-1/4`, and `d=mu/2-lambda`, the zero-defect regularized coefficient
should be

`2*d*(d+1)-lambda^2`.

This contributes through the fixed chain

`KI chiral carrier -> pulled Eq. (63) -> balanced Maass word -> completed angular coefficient ->
negative leg -> conserved left-QNM coefficient -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` Let `V,G,H` be scalar, gradient, and full-Hessian trilinear moments.
The balanced traceless-spin moment is `2H-lambda^2 V`.  Lean proves without premises the exact
identity

`(2H-lambda^2 V) - (2d(d+1)-lambda^2)V
 = 2(H-(d+1)G) + 2(d+1)(G-dV)`.

Therefore two Stokes defects are exhaustive: no third tensor invariant can obstruct scalar-vertex
reduction in the diagonal channel.  The canonical zero-defect Stokes completion is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedBalancedSpinTwoEisensteinVertex`; it equals
the displayed polynomial times the existing diagonal completed scalar vertex, has the explicit
four-Xi factorization, and preserves Weyl reflection in both spectral parameters.  Module is
wired into RHTower.  Direct Lean and targeted build pass `12049/12049`; headline axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`.

**Scope boundary / open core.** This closes the algebraic and representation-theoretic coefficient,
not the analytic statement that Zagier cusp regularization realizes zero first and second Stokes
defects.  That boundary assertion is now the unique remaining angular obstruction.  It must be
proved from Eisenstein constant terms and analytic continuation; it cannot be inserted as a
hypothesis.
