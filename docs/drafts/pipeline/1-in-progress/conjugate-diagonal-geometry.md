# Conjugate-Diagonal Geometry

- **ID:** conjugate-diagonal-geometry
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-2610/hard-obstacles-summary.md`, §3–4.
- **Statement:** Develop arithmetic constructions computing conjugate-diagonal traces and their correspondence defects, retaining the source proposal's full scope.

## Goal

Programme-specific code belongs to `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/`,
with its own sibling umbrella. Reusable analysis stays with its existing owner,
including `HTGeometry`, and is imported here. The foundational README explains motivation, objects,
language, mechanisms, traps, questions, tools, pillars, programme interfaces and
contribution/success criteria. Full completion requires answers to all eleven
questions and all eight missing tool families in §4; several endpoints imply RH.
Infrastructure or a partial theorem cannot discharge those endpoints.

## Gates

- [x] 0 → 1: source report read in full; scope and non-circularity requirements explicit.
- [ ] 1 → 2: dependency-closed paper proofs for each proposed contribution.
- [ ] 2 → 3: exact Lean statements, individual `lake --old env lean` checks and transitive axiom audit.

## Initial research direction

Search existing collided-polarization and Hecke-law modules before adding code.
Develop a quantitative defect calculus: conjugate-diagonal Gram traces, exact
Hecke transformation laws, depth moments and tail bounds. A spectral bound is
not an arithmetic upper bound. Then investigate the source's forcing gap,
central-order reduction, successor-charge question and two-variable carriers.

## Completion matrix

| Obligation | Evidence needed | Current status |
|---|---|---|
| Foundational README | All requested conceptual sections, mathematically faithful boundaries | Initial draft written |
| Dedicated code and umbrella | New checked leaves, imports in programme and cross-area umbrellas | Checked moving-source chain wired; no umbrella builds |
| Q1 conjugation correspondence | Constructed arithmetic action, spectral identification | Open |
| Q2 arithmetic evaluation of `D` | Exact identity or substantive prime-side defect estimate | Moving positive theta formula verified; significance audit open |
| Q3 selective count | Fibre-dependent count with correct quadratic term | Open |
| Q4 rank growth | Constructed section spaces and rank theorem | Open |
| Q5 beyond-horizon localization | Odd-sector sign and required exceptional-set control | Open |
| Q6 non-archimedean charge | Selective positivity with successor margin | Open |
| Q7 capacity payment | Unconditional structural `Δ ≤ D` | Open |
| Q8 coupled ceiling | Unconditional central-order theorem | Open |
| Q9 escape completeness | Unattained-supremum and infinite-height classification | Open |
| Q10 selection | Estimates at the required zero spacing | Open |
| Q11 fixed tensor loss | Constructed base and power-independent loss | Open |

## Proof integrity and validation

No missing analytic input may be introduced as a hypothesis, interface, instance,
or imported axiom. No computations or numerical experiments. No raised Lean
limits, native evaluation, placeholders, full builds or umbrella builds. Compile
one foreground Lean process at a time. Build an olean only for a missing dependency
or a new leaf imported by another new leaf. Final checks use individual source
files. Preserve unrelated existing worktree changes.

## Research record

- Initial corpus search: `conjugate diagonal geometry mixed kernel positivity arithmetic Hodge index`.
- Existing worktree contains changes in ArithmeticPolarization, ArithmeticEffectivityTheory
  and BiarithmeticGaugeGeometry; treat their current source as authoritative and preserve it.

## Defect calculus: paper argument

Put `k(L,d) = 2 cosh(2dL) − 2 = 4 sinh(dL)^2`. The double-angle
identity gives `k(2L,d) = 4k(L,d) + k(L,d)^2`. Also
`4L²d² ≤ k(L,d)`, and `k` increases with `|dL|`.

For a finite positive weighted depth distribution, write `D=Σw`,
`E(L)=Σw k(L,d)`. Then

```
D (E(2L) − 4E(L)) − E(L)^2
  = (1/2) Σi Σj wi wj (k(L,di) − k(L,dj))^2.
```

Expand the square and interchange finite sums; the two square terms each give
`D Σw k²`, and the cross term gives `2(Σw k)²`. Thus three diagonal readings
`D,E(L),E(2L)` measure the variance of the transformed depths. Equality means
every pair of positively weighted points has equal `|dL|`; at nonzero `L`,
the seen divisor lies on one absolute-depth shell. This is a rigidity law for
the diagonal defect, not a proof that the shell is the critical line.

For the actual zeta divisor and a compact `C²` test, summability of `wρ = mρ|f̂(ρ)|²`
is already proved in `TheOscillatoryCapacity`. Since `|dρ|<1/2`,
`0≤k(L,dρ)≤k(L,1/2)`, so every fixed power of `k` is summable against `w`.
No new summability assumption is needed. This gives the infinite doubled-scale
identity and quantitative tail bounds

```
k(L,b) Σ{|dρ|≥|b|} wρ ≤ E(L),
4L² Σρ wρ dρ² ≤ E(L) ≤ k(L,1/2)D.
```

The tail and moment inequalities follow termwise; summability justifies their sums.
These are spectral density tools. They do not supply the missing arithmetic
upper bound for `E`, and are valid on impure model divisors as well.

## Forcing gap: a stronger elementary separation to check

The source's exact functions are
`N=2a cosh(δa)(a^5+δ²a^5+10δa^4+20a^3)` and
`H=w(wa)^(5/2)sinh²(δ(a−2w))`.
For `a>0`, `0≤δ≤1/2`, and `0<w≤a/4`, the elementary estimates
`w≤a`, `(wa)^(5/2)≤a^5`, and `sinh²(δ(a−2w))≤cosh²(δa)` give
`H≤(N/2)cosh(δa)≤(N/2)exp(δa)`. Consequently
`2H²≤(N²/2)exp(2δa)≤(N²/2)exp(a)`.
The conductor condition implies `4exp(a)≤log(|γ|+3)`. Its leading forcing
cost alone is `≥384 log(|γ|+3)N²`. The polar correction is nonnegative.
Thus the exact sufficient forcing inequality cannot hold anywhere in the
conductor range, including depth `δ=1/2`; no asymptotic height threshold is needed.

Positive survivor to formalize with this obstruction: the explicit detector
signal/noise bound `2H²≤(N²/2)exp(2δa)` and the resulting necessary aperture
inequality for any successful forcing certificate. This excludes the overlap
of two sufficient criteria; it does not show the actual odd detector is negative
throughout the gap or retire elliptic localization itself.

## Modular-surface candidate: primary-source check

The classical scattering coefficient is `φ(s)=Λ(2s−1)/Λ(2s)`, with meromorphic
completed `Λ`, and Maass–Selberg evaluates a truncated Eisenstein inner product.
Primary reference inspected: Goldfeld, *Arthur’s Truncated Eisenstein Series for
SL(2,Z) and the Riemann Zeta Function, a Survey*,
§4, https://www.math.columbia.edu/~goldfeld/Exploring.pdf . Further primary-source
leads (search excerpts inspected; full fetch unavailable): Garrett,
*Truncation and Maaß–Selberg Relations*,
https://www-users.cse.umn.edu/~garrett/m/v/maass_selberg.pdf ;
Zworski, *Mathematical study of scattering resonances*,
https://math.berkeley.edu/~zworski/revres.pdf .

Coordinate check: the unitary Eisenstein line `Re(s)=1/2` reads `Re(2s)=1`;
zeta zeros correspond to resonances at `s=ρ/2`, and RH places them on
`Re(s)=1/4`, not on the unitary line. The truncated positive norm therefore
requires a proved transfer to the resonance divisor before it computes `D`.
This is a candidate constraint, not a no-go or a new formalized theorem.
Existing corpus leads: `EisensteinResonantSpectralKernel`,
`EisensteinHeckeResonantMoment`; inspect before developing this branch.

The following existing modules have now been read: `EisensteinResonantStateNorm`,
`EisensteinResonantSpectralKernel`, and `EisensteinResonantPartnerAngle`.
They already prove an exact resonance norm
`|Λ(ρ−1)|² Y^(1−Reρ)/(1−Reρ)` and the normalized reflected-partner angle
`cos²(angle)=4 Reρ(1−Reρ)`. Thus this candidate already has computed positive
norms and a depth-sensitive pairing, but Cauchy–Schwarz is saturated exactly at
critical zeros. Re-proving those facts would add no new result. A new contribution
must construct and bound the transfer from these nonorthogonal resonant states
to the collided trace, with constants controlled when reflection partners merge.

## Current files and validation

Current validation supersedes the historical check notes below: the full
source chain through `UniformThetaSourceMetric` passes individual Lean checks.
The final source-only check verifies the moment, collided-norm, and Hecke-defect
endpoints; all three transitive axiom lists contain only `propext`,
`Classical.choice`, `Quot.sound`. The exact theorem and remaining significance
gate are in `../3-formalized/theta-source-moving-collided-trace.md`. The explicit regulator
remains a separate unproved conjecture. Accepted count remains 0/250.

- `DefectKernel.lean`: individual source check passed; olean built because the
  new `ZetaDepthDistribution.lean` imports it.
- Missing dependency `ArithmeticPolarization/HeckeInvarianceOfTheCollidedPolarizationIsRH.olean`
  built successfully from its existing source; source unchanged.
- `ZetaDepthDistribution.lean`: initial source check exposed two elaboration errors,
  fixed by qualifying translation and making indicator cases explicit. Olean check
  passed; needed by `TwoScaleDepthRigidity.lean`.
- `TwoScaleDepthRigidity.lean`: source check passed after explicit weight/kernel
  arguments removed costly implicit inference.
- `TheConductorForcingGap.lean`: source-only check and transitive audits passed
  for the positive signal bound, necessary aperture law, and separation.
  Closed card: `../5-failed/conductor-forcing-separation.md`. Excluded from count.
- Programme umbrella and cross-area import now include the six checked leaves.
  Transitive axiom audit and final individual source checks remain pending.

## A nonholomorphic source formula: paper construction

The corpus proves Poincaré–Lelong for the entire completed xi function, including
arbitrary multiplicities. Let `χ_n` be the canonical smooth plane bump equal to one
on `|s|≤n+1`, supported on `|s|≤n+2`, and taking values in `[0,1]`. For a compact
`C²` source test `f`, its centred transform `F` is entire. Therefore
`χ_n(s)|F(s)|²` is a compact smooth real test for the xi divisor current:

```
∫ log|xi(s)| Δ(χ_n(s)|F(s)|²) dA(s)
  = 2π Σρ mρ χ_n(ρ)|F(ρ)|².
```

The left side is defined by xi and the source test, with no zero indexing. The
right side is a finite divisor trace. Multiplicities agree with those of zeta
in the open critical strip, and xi has no other zeros. Compact support and
isolated zeros justify replacing the finite divisor pairing by the carrier sum.
Since `Σρ mρ|F(ρ)|²` converges and `0≤χ_n≤1`, dominated convergence gives

```
lim_n ∫ log|xi(s)| Δ(χ_n(s)|F(s)|²) dA(s) = 2π D(f).
```

Multiplication by the smooth positive depth kernel `k(L,Re(s)−1/2)^j` gives
the same formula for each kernel moment: summability follows from the strip
bound already proved for the actual zeta divisor. In particular the first
moment computes the Hecke defect. This is a nonholomorphic analytic source
evaluation, not a prime-side estimate: the nonlinear logarithm retains all xi
information. It does not prove capacity payment, a selective count, an arithmetic
conjugation correspondence, or RH. A meaningful further step must estimate or
decompose this source integral using arithmetic data rather than merely rename it.

Existing inputs inspected: `EntirePoincareLelong`,
`EulerShiftPairIncidenceCurrent.xi_isPoincareLelongOfSmooth`,
`EvenSectorFullPositivity.differentiable_paperFT_of_compact`,
`CompletedPrimeFluxFittingAttachment.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip`,
and `ZetaXiZeroCorrespondence`. `XiSourceCurrent.lean` now contains the construction
and passed its individual olean check.

## A faithful two-scale rigidity criterion: paper argument

The existing explicit probe `splineProbe(u)=exp(u) U_1^{*4}(u)` is compact `C²`
and its transform vanishes at no zeta zero. This is already proved in
`BiScaleUncertainty/CubicSplineUniversalProbe`; its construction must be reused.
Hence all its collided weights are strictly positive. The two-scale equality
forces every zeta zero to have the same absolute depth. Hardy's theorem supplies
a critical-line zero, so that common depth is zero. Conversely RH makes every
kernel weight vanish. Thus, for this fixed explicitly constructed test,

```
RH ↔ D(E(2)−4E(1))−E(1)^2 = 0.
```

The invariant is always nonnegative; its strict positivity is equivalent to an
off-line zero. This removes the nonzero-shell ambiguity for the actual zeta
divisor and a faithful source. It is a new finite-scale spectral rigidity
criterion, not a proof that its value vanishes and not an arithmetic upper bound.
The necessary Hardy input must be an existing analytic theorem, with its
dependencies audited; no numerical zero certificate is needed.

## Common positive source sequence: paper proof

Let `P_eta(s) = eta |xi'(s)|²/(|xi(s)|²+eta)²`, and fix
`w(s)=exp((Re s)²)/(1+(Im s)²)²`. The actual transform estimate in
`IsolatedDeepZeroWeilDetection.norm_paperFT_le_decay` yields
`|F(s)|² <= C_f w(s)`: square its fourth-order vertical decay and use
`2a|Re s-1/2| <= (Re s)²+a²+a`. On the open xi strip,
`w(rho) <= (5 exp(1)/4)/(1+|gammaOf rho|²)`, so the known actual
zero summability gives `M=Σ m_rho w(rho)<infinity`.

Normalize source readings by `1/pi`. For each `n`, choose the least `k_n>=n`
whose reading of `chi_n w` differs by less than `1/(n+1)` from
`(1/(2pi)) integral log|xi| Delta(chi_n w)`. Existence follows from compact
regulator convergence; the choice condition contains no zero coordinate.
The normalized weight readings tend to `M`, by the current identity and
summable cutoff exhaustion. For any fixed compact smooth test, `chi_n=1`
on its support eventually and `k_n->infinity`, so its readings converge to
its divisor trace along this same schedule.

For nonnegative smooth `phi<=Cw`, denote the common source reading by `R_n`.
For each fixed `m`, positivity and linearity give

```
R_n(chi_m phi) <= R_n(phi)
  <= R_n(chi_m phi) + C(R_n(w)-R_n(chi_m w)).
```

Each bound has a limit as `n->infinity`. Their limits both tend to
`Σ m_rho phi(rho)` as `m->infinity`, using the summable domination by `Cw`.
Thus `R_n(phi)` converges to that trace. This proves convergence for the
squared transform of every compact C² source test with one common schedule.

The same weight controls every finite depth moment, without choosing a new
schedule for scale or moment order. Write `phi_j(f,L)=|F|² k_L^j`. The exact
pointwise translation identity is

```
phi_(j+1)(f,L) = phi_j(T_L f,L)+phi_j(T_-L f,L)-2phi_j(f,L).
```

The last term is nonpositive after subtraction, so universal domination for
order `j` and the two translated compact tests implies domination for order
`j+1`. Induction supplies all finite orders. Consequently the same positive
source sequence simultaneously recovers `D`, the Hecke defect and every
finite fixed-scale depth moment. This is pointwise convergence for each test,
scale and order; no unproved uniform convergence across these parameters is
asserted.

Lean implementation: `UniversalSourceWeight`, `CommonSourceRegulator`,
`CommonSourceMetric`; each passed its individual olean check. Supporting
curvature and Green calculus has also passed. Arithmetic source identification,
the moving-window extension and the final novelty audit remain part of the
contribution gate.

## Verification update

`SourceCurvatureCalculus.lean` and `XiSourceCurrent.lean` passed their individual
olean checks. The new programme umbrella imports these and the previously
checked defect/depth/rigidity leaves; `MainTheorems.lean` imports the programme.
Neither umbrella was compiled. `XiLogRegularization.lean` also passed its
individual olean check after API and elaboration repairs. `XiPositiveSourceMetric`,
`UniversalSourceWeight` and `XiLogL1Convergence` have also passed their individual
olean checks. `SourceCutoffControl`, `CommonSourceRegulator` and
`CommonSourceMetric` have also passed. The theta identification and moving-window
leaves remain unchecked.
The transitive axiom audit passed for eleven principal checked declarations;
their closures contain only `propext`, `Classical.choice` and `Quot.sound`.
No accepted-contribution claim yet.

## Moving logarithmic windows: derivation and further extensions

The C² endpoint with `|τ|≤n/2` and `j|L|≤2log(n+1)` described below is now
verified. Broader windows using higher regularity remain separate conjectures.
Historical proof-plan paragraphs below do not certify those extensions.

Strengthen the common-source limit to `|L| <= c log n` for every fixed compact
smooth test, fixed `c`, and finite moment order. Choose the source regulator by
local L1 potential error below `exp(-n^4)/M_n`, where
`M_n=1+||D_1 chi_n||∞+||D_i chi_n||∞+||Delta chi_n||∞`. Entire-transform bounds and Cauchy estimates control
the compact test Laplacian by `exp(O(n²+n log n))`; the prescribed local error
wins uniformly in the logarithmic window. On the actual strip, translation
costs only a fixed power of n. The existing arbitrary-order transform decay
then controls the full-divisor tail against `summable_zetaZeroConfig`.

The rapid-decay input is already proved in
`ImaginaryShiftQuadraticFourierDefect.norm_paperFT_mul_one_add_pow_le` and
`HTGeometry/CompactTestTransformOrder.exists_testTransform_decay_order`.
The required Cauchy derivative estimate is also available in mathlib and used
by `HTGeometry/CauchySecondOrderStep`. New obligations are the cutoff seminorm
construction, quantitative local error bound and moving-window passage.
This remains a conjecture/proof plan; no uniform-limit theorem has been checked.

The common-index definition now includes both weighted-mass and local-error
requirements. Both have proved eventually valid certificates, so the least
index exists without consulting tests or divisor coordinates. Cutoff support
and supremum bounds are written in `SourceCutoffControl` and under verification.
`SourceSquareCalculus` contains the written, unchecked product-Laplacian and
holomorphic-square estimates needed for the quantitative current bound.

The uniform tail admits a finite-regularity refinement. For a compact Cʳ test,
`|F(rho)|² <= C(1+|Im rho|)^(-2r)`. The reference divisor density is
`q_rho=m_rho/(1+|gammaOf rho|²)`. On the omitted part of the nth cutoff,
`|Im rho|>n`; the moment factor is at most `2^j exp(j|L|)`. Therefore
`|L|<=c log(n+1)` and `cj<=2r-2` leave a summable multiple of `q_rho` as a
uniform tail majorant. The cutoff eventually equals one at each fixed zero,
so dominated convergence includes equality at the boundary `cj=2r-2`.
This is a sufficient regularity range, not a claimed optimal threshold.
Smooth compact tests supply every finite logarithmic window and moment order.
The stronger endpoint still requires a Lean proof and novelty audit.

The first uniform endpoint can stay on the existing `CompactTest` domain:
all C² compact tests and all finite orders `j`, in the joint window
`j |L| <= 2 log(n+1)`. No new smooth-test wrapper is needed. The already
proved universal weight gives `|F(rho)|² <= C e/(1+gamma²)²`. On the omitted
cutoff, `|gamma|>n` and `(n+1)² <= 2(1+gamma²)`. Hence the moment growth
cancels one of the two quadratic denominators, leaving a fixed multiple of
the summable reference density. This closes the boundary tail using only
the checked C² input. The case `j=0` permits every L because that kernel is
independent of L. Higher regularity enlarges the joint window as described
above, but is not needed for this first source-evaluation endpoint.

The endpoint should also be uniform for ordinate modulations `twist τ f` with
`|τ|<=n/2`. This is the form that evaluates a local high-ordinate density
statistic. The corpus already proves conductor-scale upper/lower bounds for
`D(twist τ f)` in `TheLocalWeylLawOfTheCollidedForm`; those bounds are not new
work here. The new obligation is a simultaneous positive arithmetic source
formula for its logarithmic Hecke moments. Outside the cutoff,
`|Im rho-τ|>=|Im rho|/2`, so the fourth-order transform decay again leaves a
summable reference tail. The source Cauchy envelope includes
`(n+3+|τ|)²`, which stays quadratic on the stated ordinate window.
`SourceMovedTests` packages actual compact translated/modulated tests and
identifies their transforms with this two-parameter entire family.

## Source construction: selectivity calibration

The proposed positive metric computes the conjugate diagonal, so it is not a
positivity selector for the reflection pairing. Entire planted-quartet sources
would retain their additional positive divisor masses and their nonzero
translation defects. Multiplicative twins or Beurling completions satisfying
the same entire-function and summability properties would also have positive
source metrics; no successor charge or arithmetic-fibre selection is supplied.

Pole-order relaxations require a separate analysis: at a pole, the regulated
logarithm used here is not a globally smooth potential, and the current has
signed pole mass. The entire xi completion is an actual input to the proved
construction, not a property silently assigned to a meromorphic model.
Height-coupled deformations and escape families are not covered by convergence
for one fixed source; uniformity over a changing source has not been proved.
Changing theta characteristic changes the literal source and requires its own
completion identity. None of these calibrations asserts capacity payment,
Hecke invariance or an RH conclusion.
