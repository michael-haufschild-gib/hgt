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

## Loop HC94-A.9d — cusp constant terms and infinite differentiated tails

`[CORPUS]` The corpus contained an integer-exponent Hadamard finite-part theorem and a general
Tannery theorem for summably dominated complex packets, but no spectral-family cusp finite part
and no differentiated infinite Eisenstein-tail limit.

`[PAPER-PROVED] [LEAN-PROVED]` Every diagonal triple-Eisenstein boundary exponent has form

`1/2 + (epsilonOne+epsilonTwo)u + epsilonThree v`.

Encoding its doubled constant and `u,v` coefficients gives an affine exponent whose constant
coordinate is always `1`.  Hence no boundary exponent is identically zero as a spectral family.
The analytic-family finite part--coefficient extraction before spectral specialization--therefore
annihilates both Stokes boundary currents for arbitrary constant-term coefficients.  Accidental
numerical exponent zero on a resonance hyperplane creates no analytic-continuation anomaly.  This
is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspAnalyticFinitePart`; targeted build
passes `12050/12050` and headline axiom audits are kernel-only.

`[PAPER-PROVED] [LEAN-PROVED]` For the nonconstant part, a new packet subtype carries arbitrary
jet degree `m`, complex coefficients, and the exact weighted summability certificate supplied by

`Y^m exp(-(n+1)Y) <= m! (2/(n+1))^m exp(-(n+1)Y/2)`.

Lean proves the full infinite packet tends to zero by a parameter-independent Tannery majorant.
This is not a finite-mode or termwise-only statement and is stable under every fixed derivative
order needed by the two Stokes currents.  It is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspExponentialJetTail`; targeted build
passes `12055/12055`, with only `propext`, `Classical.choice`, and `Quot.sound` in the axiom audit.

**Open source-specific seam.** Construct the actual completed weight `0,+/-4` Eisenstein
Whittaker coefficient packet and prove its weighted summability, then identify the first and
second cusp currents with the constant-family plus this admitted tail.  Once that seam is closed,
both Stokes defects vanish and HC94-A.9c becomes the actual regularized polarized coefficient,
ready for negative-leg and left-QNM projection.

## Loop HC94-A.9e — arbitrary-order Bessel exterior envelope

`[CORPUS]` The corpus already defined the modified Bessel function `K_nu(s)` at arbitrary complex
order by its Schlaefli integral, but its exterior exponential estimate covered only order one.
The actual completed weight `0,+/-4` Eisenstein Whittaker modes require arbitrary spectral order
and finite order shifts produced by Maass operators.

`[CORPUS-LED CONJECTURE]` For positive real `s` and arbitrary `nu : C`, the Schlaefli integral,
`cosh(t) >= 1+t^2/2`, and a completed Gaussian square should give the uniform bound

`||K_nu(s)|| <= exp(-s) * exp(||nu||^2/(2s)) * sqrt(2*pi/s)`.

This closes the analytic decay input in the fixed chain

`KI chiral carrier -> pulled Eq. (63) -> balanced Maass word -> completed weight 0,+/-4
Eisenstein Whittaker tails -> vanishing cusp Stokes defects -> actual polarized coefficient ->
negative leg -> conserved left-QNM coefficient -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` The conjectured estimate follows directly from the corpus
Schlaefli representation and an exact shifted-Gaussian integral.  It is formalized without
premises beyond the positive-argument subtype in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBesselOrderExteriorEnvelope`, wired into RHTower,
and passes direct Lean plus targeted build `12058/12058`.  The headline axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

**Open source-specific seam.** Bound the complex divisor-sum Whittaker coefficients by a fixed
polynomial in the Fourier index and combine that bound with this envelope to construct the actual
weight `0,+/-4` differentiated tail packet.  This is source identification, not another abstract
decay surrogate.

## Loop HC94-A.9f — actual Eisenstein divisor coefficient admission

`[CORPUS]` Corpus search found exact positive-real `cpow` norm laws, divisor positivity/cardinality
bounds, and arbitrary-real polynomial--exponential summability.  It contained no definition or
summability theorem for the actual completed Eisenstein Whittaker arithmetic coefficient.

`[CORPUS-LED CONJECTURE]` At centered parameter `u=s-1/2`, define

`a_u(n) = n^u * sum_(d|n) d^(-2u)`.

For positive `n`, divisor inequalities should imply

`||a_u(n)|| <= n^(3*|Re u|+1)`,

which is enough to admit every fixed differentiated arithmetic packet into the existing infinite
cusp-tail summability class.  Its fixed proof-chain contribution is

`balanced Maass word -> actual weight 0,+/-4 Whittaker tails -> vanishing cusp Stokes defects ->
actual polarized coefficient -> negative leg -> conserved left-QNM coefficient -> HC94 clock
defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` Every positive divisor satisfies `1 <= d <= n`; exact complex-power
norms then bound the `n^u` factor by `n^|Re u|`, each `d^(-2u)` by `n^(2|Re u|)`, and divisor
cardinality by `n`.  The claimed envelope follows.  Arbitrary-real polynomial growth is summable
after the cusp exponential, yielding the exact weighted certificate for every jet degree and an
actual `D4BMCuspExponentialJetTailPacket`.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinWhittakerArithmeticEnvelope`, wired into
RHTower, and passes direct Lean plus targeted build `12059/12059`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Open source-specific seam.** Replace the abstract exponential kernel by the actual Bessel-valued
Whittaker kernel and prove the full infinite weight-zero tail tends to zero.  Then use the corpus
Bessel order recurrence to transport this statement through the two Maass steps to weights
`+4` and `-4`.

## Loop HC94-A.9g — actual infinite Bessel-valued Whittaker tails

`[CORPUS]` Corpus search exposed its Tannery theorem, polynomial--exponential zero-limit lemma,
and the new arbitrary-order Bessel envelope from HC94-A.9e.  The remaining source was the literal
Bessel kernel at `2*pi*n*Y`; replacing it by a bare exponential would not identify the Eisenstein
Whittaker expansion.

`[CORPUS-LED CONJECTURE]` At every positive index and `Y>=1`, the arbitrary-order envelope should
simplify to

`||K_nu(2*pi*n*Y)|| <= exp(||nu||^2/2) * exp(-n*Y)`.

Combined with HC94-A.9f, this should make the full infinite Bessel-valued jet tail tend to zero for
every complex arithmetic parameter, arbitrary fixed complex Bessel order, and every fixed jet
degree.  Its fixed contribution remains

`balanced Maass word -> actual weight 0,+/-4 Whittaker tails -> vanishing cusp Stokes defects ->
actual polarized coefficient -> negative leg -> conserved left-QNM coefficient -> HC94 clock
defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` Since `2*pi*n*Y>=n*Y>=1`, the leading exponential improves to
`exp(-nY)`, the spectral correction is bounded by `exp(||nu||^2/2)`, and the square-root factor is
at most one.  The actual divisor coefficient envelope supplies a single summable dominator after
absorbing every fixed `Y`-power.  Corpus Tannery then proves convergence of the entire infinite
complex series, not termwise or finite-mode convergence.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinWhittakerBesselTail`, wired into RHTower,
and passes direct Lean plus targeted build `12066/12066`.  Headline axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`.

**Open source-specific seam.** Expand the two actual Maass steps into their finite Bessel-order
shift words using the corpus recurrence, then show the weight `+4` and `-4` tails are finite linear
combinations of the just-proved arbitrary-order tails.  This will leave only identification of the
first and second Stokes currents with constant terms plus these nonconstant tails.

## Loop HC94-A.9h — real-argument derivative of arbitrary-order Bessel K

`[CORPUS]` Corpus search found the Schlaefli definition, entire dependence on complex order, and
the exact order recurrence, but no derivative theorem in the positive real argument.  This is the
derivative used by literal Maass raising/lowering of a Whittaker mode.

`[CORPUS-LED CONJECTURE]` Differentiation under the Schlaefli integral and
`cosh(t)cosh(nu*t)=(cosh((nu+1)t)+cosh((nu-1)t))/2` should give

`d/ds K_nu(s) = -(K_(nu+1)(s)+K_(nu-1)(s))/2`.

Its fixed proof-chain contribution is

`balanced Maass word -> literal two-step action on actual Bessel Whittaker modes -> weight
0,+/-4 cusp Stokes closure -> actual polarized coefficient -> negative leg -> conserved left-QNM
coefficient -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` On a neighborhood of positive base argument `s`, every nearby
argument is bounded below by `s/2`.  Positivity of `cosh` therefore dominates the derivative
integrand by the same derivative kernel at `s/2`; its integrability follows from the adjacent-order
product-to-sum identity and the corpus integrability theorem.  Dominated differentiation yields
the exact displayed formula.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBesselArgumentDerivative`, wired into RHTower, and
passes direct Lean plus targeted build `12068/12068`.  The headline axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

**Open source-specific seam.** Compose this argument derivative twice with the exact positive- and
negative-frequency Maass radial operators.  The resulting finite word contains index powers up to
two and Bessel orders shifted by at most two; extend the actual-tail Tannery theorem to those fixed
index powers and conclude both weight `+4` and `-4` nonconstant currents vanish.

## Loop HC94-A.9i — polynomial-index actual Whittaker tails

`[CORPUS]` The actual Bessel-tail theorem from HC94-A.9g handled every fixed cusp-height power,
while the literal Maass expansion necessarily creates Fourier-index powers.  Corpus search found
no source-specific theorem admitting those powers, but did expose the arithmetic polynomial
envelope and arbitrary-real polynomial--exponential summability.

`[CORPUS-LED CONJECTURE]` For arbitrary fixed natural degrees `j,m`, complex arithmetic parameter
`u`, and Bessel order `nu`, the literal series

`sum_(n>=1) a_u(n) n^j Y^m K_nu(2*pi*nY)`

should tend to zero as `Y -> infinity`.  This directly supplies every term in the two-step Maass
word and contributes through

`Bessel argument derivative -> exact weight +/-4 finite shift word -> vanishing nonconstant
Stokes currents -> actual polarized coefficient -> negative leg -> conserved left-QNM coefficient
-> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` Multiplication by `n^j` only increases the real polynomial exponent
in HC94-A.9f.  The Bessel envelope from HC94-A.9g and polynomial height absorption then give a
single summable Tannery majorant.  Lean proves the result for all fixed `j,m`, stronger than the
Maass need `j,m<=2`.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinPolynomialWhittakerTail`, wired into
RHTower, and passes direct Lean plus targeted build `12069/12069`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Open source-specific seam.** Compute and formalize the exact two positive-frequency words
`R_2 R_0` and `L_(-2) L_0` on `sqrt(Y) K_u(2*pi*nY)e(nx)`, using HC94-A.9h and the corpus order
recurrence.  Each resulting finite combination is now already admitted and vanishes at the cusp.

## Loop HC94-A.9j — literal square-root Whittaker normalization

`[CORPUS]` The completed nonconstant Eisenstein mode carries `sqrt(Y)`.  The integer-height tail
classes from HC94-A.9i therefore did not by themselves identify the literal source, despite being
strong enough for every natural jet.  Corpus search supplied the cofinal square-root limit.

`[CORPUS-LED CONJECTURE]` On the positive cusp,

`sqrt(Y) Y^m = (sqrt(Y)/Y) Y^(m+1)`

and `sqrt(Y)/Y -> 0`; hence every literal square-root-normalized polynomial-index Whittaker tail
should vanish.  This closes exact source normalization in

`two-step Maass word -> literal weight +/-4 tails -> Stokes closure -> actual polarized
coefficient -> negative leg -> left-QNM -> HC94 -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` Lean proves the exact series factorization through the next
integer-height jet and the cofinal identity `sqrt(Y)/Y=1/sqrt(Y)`.  Combining both zero limits
proves the full square-root-normalized tail vanishes for arbitrary fixed index and height degrees.
This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinSqrtWhittakerTail`, wired into RHTower,
and passes direct Lean plus targeted build `12070/12070`.  The headline axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

**Open source-specific seam.** Only the exact two-step Maass algebra remains before the
nonconstant weight `+4` and `-4` cusp currents are closed: prove each word is a finite linear
combination of the now-admitted literal square-root tails with order/index shifts at most two.

## Loop HC94-A.9k — literal two-step Maass Whittaker words

`[CORPUS]` Corpus search fixed the Maass convention and supplied the new Bessel argument derivative
from HC94-A.9h.  The remaining source calculation was the literal action on
`sqrt(Y) K_nu(cY)e(nx)`, including Fourier differentiation signs; no abstract weight label could
substitute for this calculation.

`[CORPUS-LED CONJECTURE]` For positive frequency, composing

`R_k=Y*d/dY-cY+k/2`, `L_k=Y*d/dY+cY-k/2`

should express both `R_2 R_0` and `L_(-2) L_0` as finite words in
`sqrt(Y)(cY)^j K_(nu+ell)(cY)` with `j<=2`, `|ell|<=2`.  HC94-A.9j then forces the full completed
nonconstant tails to vanish.  Its fixed chain is

`balanced local Maass word -> literal completed weight +/-4 cusp tails -> Stokes closure -> actual
polarized coefficient -> negative leg -> conserved left-QNM coefficient -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED]` Lean differentiates the square-root Bessel mode, proves both first
steps, differentiates those exact words, and verifies the two second-step coefficient tables
through orders `nu+/-2`.  Substitution `c=2*pi*n` turns the words into finite combinations of the
already admitted square-root/index tails.  Lean then proves both complete infinite nonconstant
weight `+4` and `-4` tails tend to zero.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinLiteralMaassWhittakerWord`, wired into
RHTower, and passes direct Lean plus targeted build `12071/12071`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Open analytic seam.** Stokes boundary currents contain mixed products of these exponentially
decaying tails with completed Eisenstein constant terms `Y^(1/2+/-u)`.  Prove decay survives every
such arbitrary complex-power multiplier.  Only after that may constant-family finite-part
vanishing and nonconstant tails be combined into zero first and second Stokes defects.

## Loop HC94-A.9l — active mixed constant/tail Stokes burden

`[CORPUS]` Corpus search supplies arbitrary-real polynomial--exponential summability and the exact
positive-real complex-power norm laws.  It does not yet contain the mixed completed-Eisenstein
cusp-current statement.

`[CORPUS-LED CONJECTURE] [ACTIVE]` For every spectral constant-term exponent `w : C`, multiplying
either literal two-step tail from HC94-A.9k by `Y^w` still tends to zero at the cusp.  More
generally, every finite product containing at least one nonconstant Maass tail and any fixed number
of completed constant-term powers has zero analytic-family finite part.  The proof must retain an
exponential tail rate or dominate `Y^(Re w)` by a canonical natural jet; qualitative convergence
alone is insufficient.

Fixed contribution:

`literal weight +/-4 tails + completed constant terms -> zero first/second Stokes defects ->
actual balanced polarized coefficient -> negative leg -> conserved left-QNM coefficient -> HC94
clock defect -> RH`.

**Named open core.** Formalize canonical arbitrary-complex-power absorption for the literal
Maass-tail words, then assemble all constant/nonconstant boundary sectors.  Do not claim the
Stokes defects closed before this mixed-product theorem is proved.

`[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]` Choose `M = ceil |Re w|`.  For `Y>=1`, the corpus
positive-real complex-cpow norm law gives `||Y^w/Y^M||<=1`, while increasing the literal
Whittaker height degree from `m` to `m+M` absorbs `Y^M` exactly term-by-term in the infinite
series.  A bounded multiplier therefore preserves the already-proved zero cusp limit.  Lean
proves this for every complex `w`, every index/height degree, and both complete literal
`R_2 R_0` and `L_(-2) L_0` tails.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinMixedConstantWhittakerTail`, wired into
RHTower, and passes direct Lean plus targeted build `12072/12072`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

## Loop HC94-A.9m — active full Stokes-sector assembly

`[CORPUS]` Corpus now contains two logically complementary closures: analytic-family finite part
kills every diagonal triple constant-term boundary monomial, and HC94-A.9l kills arbitrary
complex constant powers multiplying either literal nonconstant two-step Maass tail.  It does not
yet identify the complete first and second Stokes currents with an exhaustive sum of those
sectors.

`[CORPUS-LED CONJECTURE] [ACTIVE]` Expand each completed Eisenstein leg as its two Weyl constant
terms plus actual Whittaker part.  Every boundary sector is then either all-constant, hence killed
by the analytic-family finite-part theorem, or contains a nonconstant factor, hence killed by
HC94-A.9l and stability under finite products.  Consequently both actual Stokes defects vanish
under the same analytic-family regularization and the physical balanced-spin moment equals the
already formalized Bochner polynomial times the completed scalar vertex.

Fixed contribution:

`zero actual first/second Stokes defects -> actual balanced polarized coefficient -> negative BM
leg -> conserved left-QNM coefficient -> HC94 clock defect -> RH`.

**Named open core.** Formalize an exhaustive source-faithful boundary-sector decomposition,
including every Fourier-sign sector.  Do not replace it by an abstract pair whose finite-part
definition discards the nonconstant component by construction.

`[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]` Two modules close this source-faithful cusp burden.
`ThetaCuspHawkingBMEisensteinSignedMaassWhittakerTail` restores both Fourier signs with the exact
unit phases `exp(+/-2*pi*i*n*x)`, proves the signed infinite Tannery tails at every horocycle
coordinate, and proves the sign swap: negative-frequency raising is positive-frequency lowering
at reflected weight, and conversely.  Arbitrary complex powers times the full signed weight
`0,+4,-4` tails all vanish.  Targeted build passes `12073/12073`.

`ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly` then uses the canonical completed constant
coefficients `Lambda(2u)` and `Lambda(1+2u)`, the literal factor two on the signed Whittaker part,
and proves from the corpus cpow derivative that both zero-frequency two-step words act on `Y^w`
by `w(w+1)`.  The normalized current

`Y^(-1) * raised(u) * lowered(u) * scalar(v)`

has one all-constant sector plus exactly seven mixed groups.  Lean proves all seven groups tend to
zero, and proves the all-constant exponent specializes exactly to the existing affine
analytic-family exponent, whose finite part is zero.  The `Y^(-1)` normalization is essential:
it lowers the three half-powers from `3/2` to the correct Stokes constant coordinate `1/2`.
Targeted build passes `12076/12076`.  Headline axiom audits for both modules report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Loop HC94-A.9n — active Poincare/Fourier identification and truncated Stokes theorem

`[CORPUS]` Corpus now closes every cusp sector of the canonical completed-Eisenstein Fourier
model, but the completed scalar vertex remains defined directly by its four Xi factors.  Search
finds no theorem identifying the constructed Fourier model with a completed nonholomorphic
Eisenstein Poincare sum, and no truncated modular-domain Green/Stokes theorem specialized to the
two weighted Maass reductions.

`[CORPUS-LED CONJECTURE] [ACTIVE]` Construct the actual completed Eisenstein series from its
Poincare sum in a convergence chamber, prove its Fourier expansion equals the canonical cusp model,
and analytically continue the resulting truncated-domain identities.  The two boundary terms are
then exactly the current closed in HC94-A.9m, so both physical Stokes defects vanish and the actual
balanced-spin moment equals the Bochner polynomial times the regularized scalar triple vertex.

Fixed contribution:

`actual Poincare/Fourier equality + truncated Stokes -> zero physical defects -> actual balanced
polarized coefficient -> negative BM leg -> conserved left-QNM coefficient -> HC94 clock defect
-> RH`.

**Named open core.** Formalize an honest modular quotient/fundamental-domain integration theorem,
absolute convergence and termwise Fourier unfolding in a right half-plane, then meromorphic
continuation to the analytic family.  Cusp-sector closure alone is not the Stokes theorem.

`[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]` First convergence-chamber gate is now closed.  For
`z=x+i y`, `y>0`, Lean defines the honest primitive-pair denominator

`Q_z(c,d)=(c y)^2+(c x+d)^2`

and proves the explicit positive-definite coercivity law

`(1+|c|)(1+|d|) <= D_z Q_z(c,d)`

for every nonzero integer pair.  The corpus one-dimensional integer-power theorem then gives
absolute summability of `(y/Q_z(c,d))^s` over all primitive pairs whenever `Re(s)>1`.  The
completed normalization `Lambda(2s)/2` is therefore an actual absolutely convergent series, not a
formal Fourier declaration.  Lean also classifies the `c=0` primitive pairs as exactly `(0,+1)`
and `(0,-1)` and proves their total seed is `2 y^s`, so the factor `1/2` recovers the canonical
leading term.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinPoincareAbsoluteConvergence`, wired into
RHTower, and passes direct Lean plus targeted build `12086/12086`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.  Global lint still reports unrelated
concurrently-created modules missing from umbrellas; this module itself is reachable.

**Remaining A.9n core.** Split off the two first-row terms, unfold the `c != 0` primitive tail into
translation/Fourier modes, prove the Bessel--divisor coefficient formula in `Re(s)>1`, then prove
the truncated modular Green/Stokes identity there before continuation.  Convergence alone does not
identify the Poincare sum with HC94-A.9m's cusp model.

`[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]` The quotient-sensitive fixed-denominator unfolding is now
closed without a Schwartz or pointwise Poisson premise.  For each positive denominator `Q`, Lean
defines the reduced-residue sum of the genuine `L¹` integer periodization of

`K_{y,s}(t)=(y²+t²)^(-s)`.

Corpus coercivity and the integrable `(1+|t|)^(-3/2)` majorant prove `K_{y,s} ∈ L¹(ℝ)` throughout
`Re(s)>1`.  Exact L¹ periodization then gives every `m`-th Fourier coefficient as

`c_Q(m) * Fourier(K_{y,s})(m)`,

with the finite phase sum identified with the corpus Ramanujan sum.  Including the Poincare
scaling proves the exact coefficient

`y^s Q^(-2s) c_Q(m) Fourier(K_{y,s})(m)`.

This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinPoincareRamanujanUnfolding`, wired into
RHTower, and passes direct Lean plus targeted build `12210/12210`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9n analytic core.** Prove the exact complex-parameter Gamma--Bessel evaluation of
`Fourier(K_{y,s})(m)` (including the distinct zero mode), reindex the honest primitive-pair tail
onto these fixed-denominator slices, and sum the Ramanujan coefficients to the divisor/zeta
quotient.  This is the next hard gate in the fixed chain

`Poincare/Fourier equality -> truncated Stokes -> zero physical defects -> actual balanced
polarized coefficient -> negative BM leg -> conserved left-QNM coefficient -> HC94 clock defect
-> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` The geometric reindexing from the actual
primitive-pair Poincare series to the fixed-denominator Ramanujan slices is now exact.  For every
positive denominator `Q`, Lean constructs the explicit Euclidean quotient/remainder equivalence

`{unit residue mod Q} x Z ≃ {d : Z // gcd(Q,d)=1}`,

identifies the fixed slice with the honest coprime-integer primitive-pair sum, and then identifies
the denominator sum with the full positive-first-coordinate primitive subseries.  Negation gives
an exact equivalence between positive and negative first coordinates, while the two zero-first-
coordinate primitive pairs supply the constant term.  Absolute summability of the corpus
Poincare series licenses every `tsum` reindexing.  The resulting headline identity is

`rawEisensteinPoincareSeries(z,s)
   = y^s + sum_{Q>0} positivePrimitiveCuspSlice(z,s,Q,x)`.

This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinPrimitiveCuspReindexing`, wired into
RHTower, and passes direct Lean plus targeted build `12298/12298`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9n analytic assembly core.** Prove genuine Fourier integration of the actual raw
Poincare function commutes with the denominator `tsum`, using summable unit-cell `L1` norms rather
than defining the coefficient by its closed formula.  Then combine the already-proved fixed-slice
Ramanujan unfolding, Cauchy-power Fourier--Bessel transform, and Ramanujan divisor/zeta series to
identify the actual completed coefficient with the canonical Whittaker coefficient.  The fixed
route-killing chain is

`genuine raw Poincare coefficient -> completed Whittaker identity -> Fourier uniqueness ->
truncated modular Green/Stokes defects -> actual balanced polarized BM coefficient -> negative
BM leg -> conserved left-QNM projection -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Genuine positive Fourier coefficients of
the actual Poincare function are now identified with the canonical completed Whittaker modes.  A
new quantitative Tonelli theorem and the exact unit-cell contraction

`integral_(0,1] ||periodize(f)|| <= integral_R ||f||`

give the fixed-denominator estimate

`integral_(0,1] ||slice_Q|| <= C(z,s) Q^(1-2 Re(s))`.

Since `Re(s)>1`, these norms are summable.  Fourier integration therefore commutes with the actual
denominator `tsum`; no coefficient is defined by its expected formula and no pointwise Poisson or
uniform-convergence premise is inserted.  Exact Ramanujan, Bessel, Gamma, zeta, and complex-power
cancellation then proves for every positive `n`

`integral_(0,1] e(-nx) E_completed(x+iy,s) dx
   = 2 a_(s-1/2)(n) sqrt(y) K_(s-1/2)(2 pi n y)`.

This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFourierCoefficient`, wired into
RHTower, and passes direct Lean plus targeted build `12311/12311`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Remaining Fourier-uniqueness core.** Close the zero mode by the corpus-derived conjecture

`sum_{Q>=1} c_Q(0) Q^(-2s) = zeta(2s-1) / zeta(2s)`,

then close negative modes by exact sign symmetry and apply Fourier uniqueness to the actual
completed Poincare function.  This is the last coefficient gate before truncated modular
Green/Stokes, in the fixed chain

`all actual Poincare coefficients -> Fourier uniqueness -> truncated modular Green/Stokes
defects -> actual balanced polarized BM coefficient -> negative BM leg -> conserved left-QNM
projection -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived composite-modulus
Ramanujan arithmetic is now closed, including its exact denominator Dirichlet series.  The new
proof first identifies the unit-residue indicator with the corpus Möbius common-divisor kernel,
then proves arbitrary-divisor additive-character orthogonality by an explicit equivalence between
`Fin (N / d)` and the `d`-divisible stratum of `ZMod N`.  This yields, for every positive modulus
`Q` and frequency `m`,

`c_Q(m) = sum_{d | gcd(m,Q)} d * mu(Q/d)`.

For positive natural frequency `n`, the resulting coefficient is the Dirichlet convolution of a
finite divisor seed with Möbius.  Mathlib's arithmetic-function `LSeries` multiplication and the
corpus Möbius--zeta inverse therefore give the exact, premise-free identity in `Re(w)>1`,

`sum_{Q>=1} c_Q(n) / Q^w = (sum_{d|n} d^(1-w)) / zeta(w)`.

The specialization `w = 2s` is packaged using the already-certified Eisenstein absolute-
convergence chamber, so no extra summability or nonvanishing hypothesis remains.  This is
formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries`, wired into
RHTower, and passes direct Lean plus targeted build `12293/12293`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9n coefficient-assembly core.** Reindex the honest primitive-pair Poincare tail onto
the fixed-denominator slices; combine fixed-slice Ramanujan unfolding, the exact Cauchy-power
Fourier--Bessel transform, and the divisor/zeta series above; then identify every actual Poincare
Fourier coefficient with the canonical completed Eisenstein Whittaker coefficient.  Fourier
uniqueness is the next route-killing gate before any Green/Stokes work.  The full chain remains

`exact Poincare coefficient -> Fourier uniqueness -> truncated modular Green/Stokes defects ->
actual balanced polarized BM coefficient -> negative BM leg -> conserved left-QNM projection ->
HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Conjecture C-A.9s closes the noncusp
boundary obstruction for the actual completed Poincare series.  Lean proves seedwise translation
laws for both first jets and the unit-semicircle inversion law

`radialJet(Sz,p) = -radialJet(z, rotate(p))`.

Absolute summability lifts these laws through the primitive-pair `tsum`.  For any two completed
Poincare eigenfunctions, Lean also proves the exact pointwise Green--Lagrange identity; its
interior source vanishes identically for an equal-eigenvalue pair.  Consequently the paired
vertical Green currents cancel under `T`, the paired circular radial Green currents cancel under
`S`, the complete noncusp paired defect is zero, and the paired modular boundary current is
exactly the top cusp current.  These are properties of the actual infinite series, not abstract
automorphy premises.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation`, wired
into RHTower, and passes direct Lean plus targeted build `12316/12316`.  Axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9t hard core.** Prove the literal two-dimensional Green/Stokes integral on the
explicit truncated modular region and identify its surviving top-edge integral with the
already-closed completed full cusp current/analytic-family finite part.  Noncusp geometry and
interior equal-eigenvalue source are now zero before integration.  Exact chain:

`cusp-only Green/Stokes integral -> full cusp current finite part -> actual balanced BM ++-
coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` The full archimedean transform left by the
Ramanujan unfolding is now closed for the actual complex convergence chamber `Re(s)>1`.  Lean
proves absolute integrability of the two-variable Mellin--Gaussian kernel and the legal Fubini
swap, evaluates its spatial section with the corpus Gaussian Fourier theorem, and proves by the
scaled logarithmic substitution that

`integral_0^infinity t^(nu-1) exp(-a(y^2 t + xi^2/t)) dt
   = 2 (xi/y)^nu K_nu(2 a y xi)`.

Consequently every nonzero real frequency has the exact formula

`Fourier[(y^2+x^2)^(-s)](m)
   = (2 pi^s / Gamma(s)) (|m|/y)^(s-1/2) K_(s-1/2)(2 pi y |m|)`,

and the zero mode is separately identified by its exact Gamma-power formula.  No pointwise
Poisson, Schwartz, Fubini, or Bessel premise is assumed.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCauchyPowerFourierBessel`, wired into RHTower, and
passes direct Lean plus targeted build `12213/12213`.  Headline axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.

**Remaining A.9n arithmetic/geometric core.** Reindex the honest primitive-pair tail onto the
fixed-denominator slices, prove the Ramanujan Dirichlet series equals the divisor/zeta quotient,
and assemble the resulting coefficients into the canonical completed Eisenstein Fourier model.
Then prove the truncated modular Green/Stokes identity and continuation.  The fixed chain remains

`Poincare/Fourier equality -> truncated Stokes -> zero physical defects -> actual balanced
polarized coefficient -> negative BM leg -> conserved left-QNM coefficient -> HC94 clock defect
-> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]` The actual completed Poincare zero Fourier coefficient is
now the canonical two-Weyl-term constant part.  Corpus Möbius arithmetic identifies the zero
Ramanujan coefficient as the convolution `id * mu`; exact arithmetic-function L-series
multiplication therefore proves

`sum_{Q>=1} c_Q(0) Q^(-2s) = zeta(2s-1) / zeta(2s)`.

The genuine Poincare coefficient integral consequently equals its raw zeta-ratio formula.  The
corpus zero Cauchy-power transform then cancels Gamma, zeta, pi, and height powers against
`Lambda(2s)`, yielding exactly

`Lambda(2s) y^s + Lambda(2s-1) y^(1-s)`.

Lean identifies this expression definitionally with
`d4BMCompletedEisensteinCuspConstantPart .scalar (s-1/2) y`.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient`, wired into
RHTower, and passes direct Lean plus targeted build `12312/12312`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9n hard core.** Negative-frequency symmetry and Fourier uniqueness are now finite
coefficient assembly, while route survival depends on the honest modular-domain theorem.  Prove
Poincare modular invariance, the weight-zero eigen-equation, and Green's identity on an explicit
truncated fundamental domain; identify every boundary term with the already-closed full cusp
current.  The contribution chain is fixed:

`actual modular Green/Stokes defects -> actual balanced polarized BM coefficient -> negative BM
leg -> conserved left-QNM projection -> ++- source coefficient -> HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Conjecture C-A.9p closes honest modular
generator invariance for the actual primitive-pair Poincare series.  Translation is reindexed by
the primitive-pair equivalence `(c,d) -> (c,d+c)` and inversion by `(c,d) -> (d,-c)`.  Lean proves
the exact seed laws and both raw and completed `T : z -> z+1` and `S : z -> -1/z` invariance,
without a modularity premise.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinModularGeneratorInvariance`, wired into
RHTower, and passes direct Lean plus targeted build `12313/12313`.  Axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Conjecture C-A.9q proves the genuine
horizontal and vertical first and second derivatives of every primitive seed and the exact
hyperbolic eigen-equation

`y^2 (partial_x^2 + partial_y^2) (y / |cz+d|^2)^s
  = s(s-1) (y / |cz+d|^2)^s`.

At `s=1/2+u`, the eigenvalue is exactly the corpus geometric eigenvalue `u^2-1/4`.  The headline
theorem packages all four `HasDerivAt` certificates with the PDE, excluding merely formal jets.
This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinPoincareSeedEigenEquation`, wired into
RHTower, and passes direct Lean plus targeted build `12314/12314`.  Axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Conjecture C-A.9r lifts the seed equation to
the actual infinite completed primitive-pair Poincare series in the exact existing chamber
`Re(s)>1`.  New local normal-convergence laws compare horizontal seed norms with `3^Re(s)` times
the base seed and vertical seed norms with `2^Re(s) 4^Re(s)` times the base seed; all first and
second jet multipliers are uniformly seed-bounded on the corresponding half-plane
neighborhoods.  Corpus absolute convergence and `hasDerivAt_tsum_of_isPreconnected` then justify
both differentiations term by term.  Lean proves

`y^2 (partial_x^2 + partial_y^2) E*(z,s) = s(s-1) E*(z,s)`

for the actual completed Poincare series, together with the centered `u^2-1/4` form.  No stronger
convergence chamber or differentiability hypothesis is assumed.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualEigenEquation`, wired into RHTower,
and passes direct Lean plus targeted build `12315/12315`.  Headline and termwise-derivative axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9s hard core.** Combine actual `S/T` invariance and the actual completed
eigen-equation on an explicit truncated modular fundamental domain; prove Green's identity and
identify every paired vertical, circular, and cusp boundary flux with the corpus full cusp
current.  This is now the earliest route-killing gate.  Exact chain:

`truncated modular Green/Stokes identity -> zero/controlled physical boundary defects -> actual
balanced polarized BM ++- coefficient -> negative BM leg -> conserved left-QNM projection ->
HC94 clock defect -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Conjecture C-A.9s proves the exact
noncusp modular Green-boundary cancellation for actual completed Poincare eigenfunctions.  Lean
derives first-jet translation and inversion laws from primitive-pair reindexing, the radial-jet
sign reversal on the unit semicircle, the Green--Lagrange interior identity, and pointwise
cancellation of paired vertical and circular boundary currents.  The resulting truncated boundary
record reduces the whole paired boundary current exactly to the top cusp current.  This is
formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation`, wired
into RHTower, and passes direct Lean plus targeted build `12316/12316`.  Headline axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`.  Literal two-dimensional Stokes
integration was deliberately not encoded in this pointwise boundary theorem.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived conjecture C-A.9t1 closes
the actual Poincare-to-canonical signed Fourier weld.  The missing negative half is forced by the
primitive-pair reflection involution `(c,d) -> (c,-d)`, which proves horizontal evenness of the
actual sum and equality of genuine positive and negative unit-cell coefficients.  A new local
normal-convergence argument proves continuity of the actual second horizontal jet.  Corpus
pointwise `C^2` Fourier inversion then classifies every integer coefficient, reindexes the full
integer lattice into its nonnegative and negative-successor halves, and identifies the result
term-by-term with the canonical full signed Whittaker tail.  Lean proves globally, for every
horizontal coordinate and every existing absolute-convergence parameter,

`actual completed primitive-pair Poincare series
  = d4BMCompletedEisensteinCuspLeg .scalar (s-1/2)`.

This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness`, wired into
RHTower, and passes direct Lean plus targeted build `12461/12461`.  Axiom audits of negative-mode
symmetry, second-jet continuity, pointwise Fourier inversion, and global equality report only
`propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9t2 hard core.** Differentiate the global actual-to-canonical scalar equality in
both horizontal and height variables, identify actual Maass-raised/lowered top-edge legs with the
canonical `.raise`/`.lower` cusp legs, and prove the literal two-dimensional Green/Stokes theorem
on the explicit truncated modular region.  This is the earliest route-killing gate because it is
the first theorem that turns the actual modular eigenfunction into the already-closed balanced
full cusp current.  Exact chain:

`actual scalar/jet cusp weld -> literal truncated Green/Stokes -> full cusp current finite part ->
actual balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 ->
RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived conjecture C-A.9t2a
constructs the previously missing actual mixed derivative.  For every primitive Poincare seed,
Lean proves that horizontally differentiating its genuine vertical first jet gives the explicit
`partial_x partial_y` jet.  A sharp-enough unconditional estimate

`norm(partial_x partial_y seed) <= ((4 norm(s) + 6 norm(s)^2) / y^2) norm(seed)`

puts it on the same summability scale as both pure second jets.  Existing horizontal local
comparison and absolute primitive-pair convergence then justify termwise differentiation in the
exact chamber `Re(s)>1`.  The result is lifted through raw and completed sums and packaged with
the already-certified value, first jets, and pure second jets as an actual
`D4BMFullSecondJet`.  Its literal corpus `R_2 R_0` and `L_(-2) L_0` evaluations are therefore now
closed differential expressions, not formal proxies.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualMixedDerivative`, wired into
RHTower, and passes direct Lean plus targeted build `12462/12462`.  Headline axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

**Remaining A.9t2b hard core.** Prove the exact equality between these literal actual
`R_2 R_0`/`L_(-2) L_0` evaluations and
`d4BMCompletedEisensteinCuspLeg .raise/.lower (s-1/2)`.  Corpus research shows the finite
single-mode Bessel derivative identities and arbitrary polynomial-index summability already
exist, but local normal convergence for differentiating the full signed square-root Whittaker
tail has not yet been assembled.  This is now the exact earliest open core.  Full chain:

`actual full second jet -> canonical raise/lower weld -> literal truncated Green/Stokes -> full
cusp current finite part -> actual balanced BM ++- coefficient -> negative BM leg -> conserved
left-QNM projection -> HC94 -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived conjecture C-A.9t2b1
closes the mode-level route-killing test for the actual Maass weld.  Lean reconstructs the genuine
second radial derivative of `sqrt(Y) K_nu(cY)` from the differentiated first raising word, then
derives an independent lowering-word reconstruction by uniqueness of the derivative.  These
certificates produce genuine signed two-variable full second jets.  Literal full-jet evaluation
proves all four chirality/frequency laws: positive modes send `R_2 R_0` to the existing raising
word and `L_(-2) L_0` to the lowering word, while negative modes exchange those two words exactly.
Thus no sign or connection-term obstruction kills the signed `++-` route.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualMaassModeJet`, wired into RHTower,
and passes direct Lean plus targeted build `12463/12463`.  Axiom audits of both radial
reconstructions and all four signed normalization theorems report only `propext`,
`Classical.choice`, and `Quot.sound`.

**Remaining A.9t2b2 hard core.** Lift the four exact mode identities through the infinite actual
Eisenstein coefficient sum.  Required theorem is local-normal convergence of the signed
square-root Whittaker value, first-jet, and second-jet families on every positive-height
neighborhood, followed by termwise differentiation and exact identification with the canonical
phased Maass words.  Exact chain remains

`local-normal signed full-second-jet tail -> actual/canonical raise-lower weld -> literal truncated
Green/Stokes -> full cusp current finite part -> actual balanced BM ++- coefficient -> negative BM
leg -> conserved left-QNM projection -> HC94 -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived conjecture C-A.9t2b2a
removes the apparent need for a separate local-normal-convergence proof for the pure vertical
second-jet family.  Uniform exterior-cusp exponential bounds are proved for the signed modified
Bessel factor, the square-root Whittaker value, and its genuine first radial jet.  Together with
the corpus coefficient bound, they establish summability of the weighted value and first-jet
families.  Lean then differentiates the actual infinite signed tail in the vertical direction,
the horizontal direction, horizontally through the vertical first jet, and horizontally through
the horizontal first jet.  Hence the actual tail has certified value, `x`, `y`, `xx`, and `xy`
jets; its missing `yy` field can be recovered algebraically from the existing Poincare
eigen-equation, reducing the weld burden from five independently convergent derivative families
to four.  This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSignedFirstJetWeld`, wired into
RHTower, and passes direct Lean plus targeted build `12464/12464`.  Axiom audits of both uniform
majorants and all four infinite-series derivative theorems report only `propext`,
`Classical.choice`, and `Quot.sound`.

**Remaining A.9t2b2b hard core.** Construct the canonical scalar cusp second jet from those four
genuine derivatives and recover `yy` from the eigen-equation; prove that its literal
`R_2 R_0`/`L_(-2) L_0` evaluations equal the canonical `.raise`/`.lower` completed cusp legs.
The constant sector must close by the existing zero-frequency `cpow` two-step Maass identities,
and the nonzero sector by C-A.9t2b1 termwise mode normalization plus C-A.9t2b2a summability.  This
is the decisive weld: success closes A.9t2b, while any mismatch in constant-sector normalization,
tail phase, or chirality kills the proposed cusp-current route.  Exact chain:

`actual/canonical Maass weld -> literal truncated Green/Stokes -> full cusp current finite part ->
actual balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 ->
RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived conjecture C-A.9t2b2b
closes the decisive actual/canonical Maass weld.  The canonical scalar cusp model is assembled as
a genuine full second jet: zero-frequency `cpow` jets plus the two signed Whittaker tails.  The
Schlaefli order recurrence proves the nonzero-mode eigen equation, while the Weyl exponents prove
the zero-mode indicial equation.  Global actual/canonical scalar Fourier uniqueness and uniqueness
of genuine derivatives then identify the actual and canonical `x`, `y`, `xx`, and `xy` jets.
Their equal eigen equations recover `yy`, eliminating any independent radial-second convergence
burden.  Consequently the complete actual Poincare second jet equals the canonical cusp second
jet on the exterior-cusp coordinate type, and literal `R_2 R_0` and `L_(-2) L_0` evaluation equals
the canonical completed `.raise` and `.lower` cusp legs.  Exterior height is carried as coordinate
data, so the headline theorems have no logical premises.

This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualCanonicalMaassWeld`, wired into
RHTower, and passes direct Lean plus targeted build `12465/12465`.  Axiom audits of the signed-tail
and full canonical eigen equations, full second-jet weld, and both headline Maass welds report only
`propext`, `Classical.choice`, and `Quot.sound`.  Lint reports only unrelated pre-existing
umbrella-reachability debt.

**C-A.9t3 hard core (corpus-derived conjecture; active).** Construct literal compact truncated
modular-domain scalar, gradient, and full-Hessian moments from the actual Poincare jets, then prove
the two exact Green--Stokes identities whose only survivors are the paired cusp-top currents.
Transport C-A.9t2b2b through those boundary currents and identify them with
`d4BMCompletedEisensteinBalancedFullBoundaryCurrent`; combine the existing mixed-tail limit and
analytic-family constant finite-part theorem to annihilate both exhaustive Stokes defects.  Success
removes the whole analytic boundary-regularization burden and yields the actual balanced BM `++-`
coefficient.  A surviving non-cusp boundary finite part, or a mismatch between the literal
raised/lowered Hessian moment and the canonical balanced current, kills this route before QNM work.
Exact chain:

`literal actual truncated Green/Stokes -> full cusp-current finite part -> actual balanced BM ++-
coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived conjectures C-A.9t3a--b
close the pointwise first Green-current identity and its complete cusp finite part.  For actual
completed Poincare legs `F,F,G`, Lean constructs the genuine product current
`J = 2 F G grad F - F^2 grad G` and proves
`2(firstStokesDefect) = y^2 div J` from the two actual eigen equations.  Translation and unit-arc
inversion pair every non-cusp current exactly, and the C-A.9t2b2b weld identifies the survivor with
the canonical vertical cusp current.

The new source-specific analytic step differentiates the full signed square-root Whittaker tail:
each vertical first-jet summand is exactly a three-tail packet of orders `nu`, `nu+1`, and `nu-1`.
The existing arbitrary-complex-power Whittaker estimate therefore proves that the genuine vertical
first-jet tail beats every complex height power.  A new rapid-cusp-decay ideal then proves, without
enumerating twelve terms, that the full vertical product current minus its differentiated Weyl
constant sector tends to zero.  The literal constant-sector current is exactly the evaluation of
the diagonal affine-exponent family and its analytic-family finite part is zero.  Consequently the
actual paired boundary current has an exact `constant + rapidly decaying remainder` decomposition.

This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFirstStokesDefect`, wired into
RHTower, and passes direct Lean plus targeted build `12466/12466`.  Axiom audits of the pointwise
divergence, arbitrary-power vertical derivative-tail decay, rapid-decay mixed-current theorem,
literal actual boundary decomposition, and full cusp closure report only `propext`,
`Classical.choice`, and `Quot.sound`.

**Remaining C-A.9t3c hard core.** Prove the literal two-dimensional truncated-domain Green theorem,
not merely its pointwise divergence and boundary algebra.  The required compact modular domain is
the curvilinear strip `-1/2 <= x <= 1/2`, `sqrt(1-x^2) <= y <= Y`; its iterated horizontal and
vertical bulk integrals must be discharged by FTC, with the lower arc recombining into the radial
current and the vertical sides into the translated current.  Success turns the now-closed boundary
finite part into the first exact moment identity.  Failure of integrability, change-of-variable, or
arc orientation is a genuine route-killing defect.  Exact chain remains

`literal actual truncated Green/Stokes -> actual balanced BM ++- coefficient -> negative BM leg ->
conserved left-QNM projection -> HC94 -> RH`.

`[PAPER-PROVED] [LEAN-PROVED] [HARD FRONTIER CLOSED]` Corpus-derived conjecture C-A.9t3c
closes the literal two-dimensional first Green theorem.  The formal domain uses the exact standard
modular geometry: two side slivers below height one and the full strip above it.  New local normal
convergence proves continuity of the completed vertical second-jet slice, enabling vertical FTC.
Horizontal FTC, translation, and the exact substitution
`y = sqrt(1-x^2)` supply the lower-arc Jacobian.  Pairing the two half-arcs turns the oriented
horizontal and vertical flux into the radial current, which inversion annihilates pointwise.
Consequently the actual paired iterated divergence integral equals exactly the paired cusp-top
current for every truncation height `Y >= 1`; no integrability premise, proxy field, boundary
hypothesis, or regularity axiom is used.  The pointwise hyperbolic-measure identity also identifies
the actual first Stokes defect divided by `y^2` with the sum of these two genuine divergence
components.

This is formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral`, wired into
RHTower. Direct Lean and targeted build `12467/12467` pass. Axiom audits of local normal
continuity, arc substitution, oriented circular cancellation, the literal truncated Green theorem,
and the hyperbolic defect-density bridge report only `propext`, `Classical.choice`, and
`Quot.sound`. Formal lint finds only unrelated pre-existing umbrella-reachability debt.

**C-A.9t3d hard core (corpus-derived conjecture; active).** Prove joint compact-cell
measurability/integrability and Fubini for the actual value and first-jet Poincare fields, then show
the coordinate-split literal divergence integral of C-A.9t3c is the standard truncated hyperbolic
integral of the actual first Stokes defect.  This is the exact coefficient interface: success turns
the already-closed cusp finite part into the first moment reduction `G = d V`; failure of Fubini or
local normal convergence kills the analytic regularization route rather than permitting the
abstract zero-defect completion.  Exact chain:

`actual defect Fubini -> first moment reduction -> second full-Hessian Green/Stokes -> actual
balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.
