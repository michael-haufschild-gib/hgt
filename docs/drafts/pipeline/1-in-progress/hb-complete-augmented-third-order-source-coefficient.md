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
