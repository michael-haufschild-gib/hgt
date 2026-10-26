# Conjugate-Diagonal Geometry

- **ID:** conjugate-diagonal-geometry
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-2610/hard-obstacles-summary.md`, §3–4.
- **Statement:** Develop arithmetic constructions computing conjugate-diagonal traces and their correspondence defects, retaining the source proposal's full scope.

## Goal

All code belongs to `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/`, with
its own sibling umbrella. The foundational README explains motivation, objects,
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
| Dedicated code and umbrella | New checked leaves, imports in programme and cross-area umbrellas | Pending |
| Q1 conjugation correspondence | Constructed arithmetic action, spectral identification | Open |
| Q2 arithmetic evaluation of `D` | Exact identity or substantive prime-side defect estimate | Open |
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

- `DefectKernel.lean`: individual source check passed; olean built because the
  new `ZetaDepthDistribution.lean` imports it.
- Missing dependency `ArithmeticPolarization/HeckeInvarianceOfTheCollidedPolarizationIsRH.olean`
  built successfully from its existing source; source unchanged.
- `ZetaDepthDistribution.lean`: initial source check exposed two elaboration errors,
  fixed by qualifying translation and making indicator cases explicit. Olean check
  running, exec session `29466`; needed by `TwoScaleDepthRigidity.lean`.
- `TwoScaleDepthRigidity.lean`, `TheConductorForcingGap.lean`: written, not checked yet.
- Programme umbrella, cross-area import, transitive axiom audit, final source checks
  and README theorem references remain pending.

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
and `ZetaXiZeroCorrespondence`. Construction and Lean verification remain pending.
