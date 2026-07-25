# Connes/CCM RH research handover

Date: 2026-07-25

## Mission and success condition

Resume the Connes–Consani–Moscovici lane, guided by Lean as the authoritative research corpus.
Only one of these is terminal progress:

1. `[LEAN-PROVED]` unconditional
   `P_-(L) ≤ C_Γ(L) + P_+(L)` for every `L ≥ π/2`, hence RH;
2. a concrete proved violating `L`, hence disproof of RH;
3. an unconditional theorem excluding every CCM-admissible infinite source transport.

Do not count equivalent RH criteria, estimates, infrastructure, or another excluded subclass.
Use `hgt-fields-medalist`; read `docs/meta/scientific-method.md` and failed-route cards first.

## Exact endpoint already closed in Lean

For finite right-half-plane nodes `P`, the required object is

```text
W_P = [[G_P, r_P], [r_Pᴴ, 4]],
r_P(i) = continuedXiAntiCausalWardResponse(P_i).
```

`formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardCofinalBoundaryLift.lean` proves:

- `continuedXiWardFourUnitBoundaryGram_posSemidef_iff_schur`;
- `riemannHypothesis_iff_continuedXiWardFourUnitBoundaryLiftLaw`;
- the equivalent boundary-Gram law;
- under `¬RH`, one zero-adapted one-node packet makes the Schur defect strictly negative.

Thus unconditional source-side positivity of every `W_P` is exactly RH, not an auxiliary lemma.
`XiWardThresholdEightClosedCompleteness.lean` also closes the two-sided threshold-eight endpoint.

## Exact source geometry already closed

- `MobiusCriticalFisherLowerBoundaryBudget.lean`: actual one-sided lower-corner Hilbert–Schmidt
  energy has critical total `4`.
- `RankTwoFisherCutoffWard.lean`: pointed Fisher connection is the canonical rank-two operator
  `2⁻¹/²(|χ><ψ|+|ψ><χ|)`; its cutoff corners are explicit.
- `EulerSquarefreeDyadicAffineProjection.lean`: exact unitary reindexing `n = d m²`, preserving
  cutoff corners and Hilbert–Schmidt energy.
- `EulerSquarefreeAffineFisherCutoffWard.lean`: the full positive Euler source retains the same
  critical four-unit Fisher/Ward law.
- `FisherOneCornerCoareaTransform.lean` and
  `InfiniteFisherOneCornerCodiagonalContraction.lean`: universal one-corner contraction machinery.
- `SoninBurnolPointedWardTrace.lean`: hypothesis-free Lüders/Burnol boundary split.
- `SoninCofinalMobiusGammaXiIncidence.lean`: source-defined noncompact/cofinal Sonin transports
  reconstruct the full continued Xi trace on the Euler region. Energy incidence is not proved.
- `EulerAffineGammaXiWardTransport.lean`: exact singular graph transport from the all-Euler Fisher
  numerator to the continued Xi source.
- `SquarefreeFixedCurrentLocalization.lean`: division-free identity

```text
ε B_σ(u) J_sq(σ+uε) = -∂_u B_σ(u),
B_σ(u)=squarefreePartition(σ+uε)/squarefreePartition(σ).
```

The strict-right Xi divisor is exactly the failure set of the continued multiplication quotient.

## Paper-proved source completion

Read:

- `docs/drafts/pipeline/2-fully-proven/gamma-sonin-asymptotic-passivity-incidence-curvature.md`;
- `.../complementary-packet-euler-connection-weld.md`;
- `.../complementary-packet-critical-gini-isometry.md`;
- `.../mobius-fixed-current-von-mangoldt-critical-transport-weld.md`;
- `.../mobius-causal-fisher-connection-flatness.md`.

They establish on paper:

- entrywise Gamma completion is asymptotically passive;
- Sonin projection is contractive;
- complementary packets and Euler fixed-current transport preserve the four-unit cofinal budget;
- the assembled causal derivative is Fisher-flat: its two connection terms cancel before the
  Gamma/Sonin boundary split.

Verify exact Lean status before importing any paper-only claim.

## Current open core

Active research card:

`docs/drafts/pipeline/1-in-progress/mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`

`[OPEN CORE]` Construct, before any Xi divisor or target Gram is named, the charged anti-causal
codifferential of the completed Euler-current edge field on the closed multiplication graph
`Graph(B_σ)`. Prove all three:

1. the completed Fisher numerator lies in the source-selected graph range;
2. its anti-causal graph quotient/curvature is exactly the squarefree Hardy block, hence tends to
   `r_P`;
3. Gauss–Codazzi gives a nonnegative causal remainder:

```text
source four-unit curvature
  = anti-causal curvature energy + causal remainder energy.
```

This would give `‖r_P‖²_{G_P⁻¹} ≤ 4`, hence `W_P ⪰ 0`, hence RH.

Equivalent pointwise slogan `|r(1/2+it)| ≤ 2` is not enough unless derived from this source object.

## Anti-theatre results already settled

- `[REDISCOVERED/CIRCULAR]` Orthogonal Hardy projection of the continued logarithmic derivative is
  a classical causal reformulation; identifying its source preimage contains RH.
- `[CORPUS]` `GammaSewnMobiusXiWardHardyTransport.lean` constructs a target-side Julia transport
  whose derivative is `r`; `GammaSewnMobiusXiWardHardyContraction.lean` bounds the finite transport
  by `2`. A bounded curve does not bound its derivative, so this does not prove `|r| ≤ 2`.
- `[CORPUS]` `GammaSewnSynchronizedRecoveryContraction.lean` is a genuine coordinatewise source
  contraction, but multiplies a target-defined Xi transport; it does not establish source incidence.
- `[FALSIFIED]` Generic completely positive/Lüders compression cannot represent the singular
  overlap division. It contracts Hilbert–Schmidt energy but loses the arithmetic current.
- `[FALSIFIED]` Scalar, diagonal, channelwise, finite-rank, bounded-codiagonal, shell-amplification,
  derivative-Pick, and target-factorization shortcuts are recorded in
  `docs/drafts/pipeline/1-in-progress/ccm-four-unit-source-codiagonal-attack.md`.
- `XiWardInteriorSourceBudgetDivergence.lean` proves the full Xi logarithmic trace cannot be one
  finite-energy scalar half-line Laplace source. Anti-causal resolution must precede scalarization.
- Do not propose an “orthogonal product/Pythagoras law” abstractly: corpus already identifies it as
  the desired Gauss–Codazzi incidence, and generic factorization has uncontrolled cross terms.

## New differential-transcendence information

`formal/GaloisForLFunctions/RHTower/MarkusConjecture.lean` proves `markus_conjecture`.
`HTGeometry/DigammaOverDirichletBase.lean` proves
`rotDigamma_hypertranscendentalOver_dirZetaBase`: rotated digamma remains hypertranscendental after
adjoining every finite-abscissa Dirichlet germ simultaneously.

Impact on CCM:

- prime Dirichlet data cannot differentially generate or cancel the archimedean digamma channel;
- every scalar finite-jet/differential-algebraic prime-to-Gamma connector is excluded;
- the missing connector must retain digamma as an independent transverse coordinate and be
  infinite-dimensional, operator-valued, and singular/nonlocal.

This does not imply positivity. Differential independence is not Hilbert orthogonality.
Markus itself is `[REDISCOVERED]` (Feng Lü, BLMS 2025); the simultaneous all-Dirichlet theorem is
`[NOVELTY UNVERIFIED]`.

## Live conjecture to attack

`[CONJECTURE]` **Source conormal Gauss–Codazzi law.**
The Gamma/Sonin completion of the squarefree determinant line has a closed conormal multiplication
graph whose second fundamental form splits orthogonally into:

```text
anti-causal part = continuedXiAntiCausalWardResponse,
causal part      = a positive Hilbert–Schmidt residual.
```

The four-unit Fisher curvature is the sum of their squared norms.

This is falsifiable: a nonzero indefinite cross term in the finite Gamma/Sonin kernel kills it.
It is non-circular only if the graph, projections, and curvature are defined from Möbius packets,
Gamma kernel, Sonin cutoff, and Euler connection before Xi zeros or `r_P` appear.

## Immediate restart attack

1. Inspect exact types and product/corner identities in:
   `SoninBurnolPointedWardTrace.lean`,
   `EulerAffineGammaXiWardTransport.lean`,
   `SquarefreeFixedCurrentLocalization.lean`,
   `MobiusCriticalFisherLowerBoundaryBudget.lean`, and
   `GammaSewnMobiusXiWardHardyNonexpansive.lean`.
2. Write the finite source graph operator and its two boundary corners explicitly.
3. Expand the finite squared norm. Determine the cross term exactly.
4. If it vanishes from Lüders/Sonin orthogonality, prove the finite Gauss–Codazzi identity on paper.
5. If it does not vanish, identify its exact sign. Replace the Hilbert split by the smallest
   source-defined relative/Krein graph in which it becomes a positive residual; do not add a fitted
   target correction.
6. Prove the Euler-region trace identity without zero sums, then take the prescribed cofinal graph
   limit. Only after the paper proof closes, formalize it.

Hostile acceptance tests:

- no Xi zero, canonical right factor, `r_P`, or target norm in the source definition;
- no division by `B_σ` before a proved graph-range theorem;
- no unproved interchange of cofinal limits;
- no inference from finite-parameter contractivity to derivative contractivity;
- no hidden RH-equivalent causality assumption;
- exact energy constant `4`, or two-sided constant `8` with the existing closed endpoint.

## Lean/build discipline

- Search with `scripts/formal_tools.py research "<query>"` before proving reusable lemmas.
- Paper proof first; no Lean infrastructure for an open conjecture.
- Use one foreground process only: `lake env lean <file>`.
- Use `lake build <module>` only for final audit; preserve cache.
- Run `scripts/formal_tools.py lint` and `#print axioms` from `/tmp`.
- No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computations.
- Wire any final theorem into `formal/GaloisForLFunctions/RHTower.lean`.
- Check and terminate stale Lean processes before handoff.

No Lean process was intentionally left running by this session.

---

## LANE CLOSED — 2026-07-25

The CCM four-unit source-budget lane is a dead end.  Card:
`docs/drafts/pipeline/1-in-progress/ccm-critical-clock-divisor-blindness.md`.

**1. The budget is a class invariant.**  The whole source package (Gibbs family `p_σ ∝ x^{-σ}dN`,
signed state, Fisher tangent, cutoff commutator, one-corner field, Gamma/Sonin completion) has a
critical limit that factors through the clock law.  A simple pole of the Mellin transform at
`σ=1` gives, by pure algebra, `Z(σ+u(σ-1))/Z(σ) → 1/(1+u)`; the truncated `Exp(1)` moments of the
score `2(1-y)` are `1-e^{-u}`, `2ue^{-u}`, `4(1-(1+u²)e^{-u})`, and their rank-two Gram is
*definitionally* `squarefreeMobiusCriticalFisherCutoffWardLimit`.  So `E_W`, `E_lower`, the
four-unit total, the Fisher curvature and the Gini curvature are the same for every nonnegative
Mellin source with a simple pole.  Explicit members of that class have strict-right zeros whose
Schwarz-paired Cauchy energy exceeds eight.  Hence `C1`–`C50` and the open core of
`mobius-incidence-curvature-…` cannot close: the hypothesis is constant, the conclusion is not.

**2. Every source hypothesis is refuted, including the functional equation.**  For any
`a₀ ∈ (0,1/2)`, `γ ≠ 0` with `κ = √(a₀²+γ²) < 1/2`, put `β = 1/2+a₀`, `ρ = β+iγ` and add to the von
Mangoldt measure the logarithmic density

```text
d(u) = 4 e^{u/2}[cosh(κu) - cosh(a₀u)cos(γu)].
```

Then: `d ≥ 0`; its power series `2Σ_{n≥1}(κ^{2n}-Re w^{2n})u^{2n}/(2n)!` (`w=a₀+iγ`, `κ=|w|`) has
nonnegative coefficients and vanishing constant term, so `d(u)/(2e^{u/2}u)` is nondecreasing, and
the monotone Möbius criterion `Σ_k μ(k)k^{-2}g(u/k) ≥ (2-π²/6)g(u)` makes the **prime** measure
nonnegative; the Laplace transform is reflection antisymmetric, so the completed function satisfies
the **exact** Riemann functional equation; `κ<1/2` keeps the pole at `s=1` simple (PNT holds); and
the system's zeta `ζ·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)/[(s-1/2-κ)(s-1/2+κ)]²` has **zeros off the critical
line**.  So `Λ ≥ 0`, `dΠ ≥ 0`, an Euler product, PNT, and the Riemann functional equation are
jointly insufficient.

**3. The only surviving input is entirety, and the budget discards it.**  For finite-rank
reflection-antisymmetric corrections, positivity forces a positive coefficient at a *real* leading
frequency (leading-exponential mean value + Parseval), hence a real pole of the completed function;
`ξ` has no real zeros; so `Λ ≥ 0` + FE + entirety forces the correction to vanish.  Entirety is a
pole-cancellation statement between the prime and archimedean sides — exactly what the corpus's own
"Gamma multiplier norm → 1" theorem throws away.  No energy/Gauss–Codazzi apparatus can see it.

**Verdict.**  Do not resume the four-unit/Ward-budget programme.  Any future attempt must take
entirety (equivalently Poisson summation / the theta relation) as a primitive, which is the trace
formula, not the source budget.

Lean: `HTGeometry/CriticalClockSourceUniversality.lean`,
`HTGeometry/MonotoneMobiusPositivity.lean`,
`RHTower/CCMCriticalClockDivisorBlindness.lean`,
`RHTower/LambdaPositiveFunctionalEquationOffLine.lean`.
Standard axioms only; repository lint gate green.
