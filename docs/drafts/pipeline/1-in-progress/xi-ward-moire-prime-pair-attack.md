# Moiré prime-pair attack on the sampled Ward matrices

- **ID:** `xi-ward-moire-prime-pair-attack`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / DIRECT-CORE ATTACK (successor object of A†/B†)
- **Scientific status:** `[CONJECTURE] [SETUP EXACT] [NOT RH YET]`
- **Source:** direct attack round on `ht-capacity-ward-holonomy-rh.md`; both
  obstruction theorems (`xi-ward-chart-exchange-legendre-neutrality-
  obstructions.md`) independently demand a finite-stage quadratic carrier;
  entropy collision draws: moiré-patterns, contact-juggling.
- **Lean inputs:** sampled Gram law + merged slack + threshold-8 corner
  (`XiWardPrimeLogSampledGramLaw.lean`, `XiWardMergedSlackPrimeLogSampling.lean`,
  `XiWardThresholdEightCompleteness.lean` once built).

## The object

For edge heights `τ₁ ≠ τ₂` and corner `c ∈ (0, 8)`, the corner Schur defect on
the two-node edge packet is

```text
S(τ₁,τ₂) = [[ c − |r₁|²,            c/(1+iΔ) − r₁·conj r₂ ],
            [ conj(...),            c − |r₂|²             ]],
rᵢ = r(1/2 + iτᵢ),   Δ = τ₁ − τ₂.
```

Under RH (`r ≡ 0`) it is PSD with determinant `c²·Δ²/(1+Δ²)` — the headroom
vanishes quadratically as the nodes merge and saturates for `Δ` large.

At prime-log nodes `τ₁ = −log p`, `τ₂ = −log q` the shift is
`Δ = log(q/p)`: the moiré frequency of the two prime gratings.

## Two structural facts fixing the attack's shape

1. **Small-shift limit = the boundary-derivative gap.**  As `Δ → 0` the
   2×2 constraint degenerates to the first-order jet constraint on `r` along
   the edge — precisely the "finite-aperture phase gives no bound on the
   boundary derivative of `r_P`" failure recorded in the goal statement.
   Consecutive-prime nodes probe exactly this regime: prime gaps give
   `Δ = log(q/p) ≍ (q−p)/p`, stretched-exponentially small cofinally (corpus
   shrinking-window theorem), while the RH-side headroom there is
   `≈ c·Δ²/2`.  The moiré family is therefore a *discrete derivative probe*
   with arithmetic node supply — the first formulation in which the
   derivative gap has a prime-indexed finite-stage carrier.

2. **The arithmetic content at shift `Δ` is a critical-line Dirichlet value,
   not a pair correlation.**  A two-tone Weil test (`f̂` concentrated at the
   two frequencies) has autocorrelation `g = f ⋆ f̃` beating at frequencies
   `{0, ±Δ}`; the prime channel of the explicit formula then picks up
   `Σ Λ(n) n^{−1/2−iΔ}`-type sums — the logarithmic derivative *on the
   critical line at height `Δ`* — weighted by the tone amplitudes.  For
   consecutive primes `Δ` is tiny, and `−ζ'/ζ(1/2+iΔ)` for `Δ → 0` is
   governed by the pole (`≈ −1/(iΔ − 1/2)`-scale) — an accessible regime, in
   contrast to the `S(T)`-wall at generic heights.  The attack's quantitative
   question is whether the pole-dominated small-`Δ` window and the
   `c·Δ²/2` headroom close compatibly across the cofinal prime-gap supply.

## Exact next steps

1. Write the two-frequency Guinand–Weil identity for the two-tone test in the
   corpus normalization: quadratic form in tone amplitudes `(α, β)` with
   diagonal = single-node channels, off-diagonal = the shifted Dirichlet
   channel + archimedean beat; identify the off-diagonal with
   `c/(1+iΔ) − r₁ conj r₂` structure of `S(τ₁,τ₂)`.
2. Contact-juggling certificate: prime-INSERTION monotonicity — at fixed
   nodes, inserting a prime into the source moves `G_P` and `r_P` jointly;
   formulate the per-insertion inequality with margin-sized tolerance (the
   merged-slack law makes tolerance sufficient).  Node-insertion Cauchy
   interlacing runs the wrong way; prime-insertion is the loom's shuttle.
3. Hostile tests to run before any promotion: (i) B†-compliance — the attack
   must remain sign-based (the two-tone form), never reduce to a size bound
   on a von-Mangoldt sum; (ii) C39 — the two-tone functional must consume
   `Λ` essentially; (iii) Beurling counterfeit — check whether the small-`Δ`
   pole-dominance step uses FE/integrality beyond ψ-class data (if not, the
   step is counterfeitable and must be restructured).
4. Numerical pre-certification is banned for promoted proofs (rule 6); use
   desk asymptotics only.

## Gates

- [ ] two-frequency identity derived in corpus normalization
- [ ] small-`Δ` pole-dominated expansion of the off-diagonal channel
- [ ] prime-insertion inequality formulated; hostile tests (i)–(iii) run
- [ ] decide: closes the 2×2 family cofinally, or exact obstruction theorem
- [ ] Lean formalization of whichever survives

## Step-1 desk result: the multiplicative family is Toeplitz-plus-rank-one

On edge nodes drawn from the multiplicative semigroup `{−log n}`, the Hardy
Gram is a Toeplitz kernel in the moiré variable:

```text
G(−log m, −log n) = 1/(1 + i·log(m/n)) = ∫_0^∞ e^{−x} e^{−i·log(m/n)·x} dx,
```

a positive-definite function of `u = log(m/n)` (Fourier transform of the
one-sided exponential).  The corner-`c` sampled Ward family over all finite
multiplicative packets is therefore the positivity of a RANK-ONE-PERTURBED
TOEPLITZ kernel

```text
K(m,n) = c/(1 + i·log(m/n)) − r_m · conj r_n,   r_n := r(1/2 − i·log n),
```

on the semigroup — a Nehari/AAK-type problem: the arithmetic response column
against the Cauchy–Toeplitz budget.  This replaces the two-frequency
Guinand–Weil identity as the structural home of the attack: the corpus's
Hankel assets (`XiTraceHankelCountableCriterion`, Hedenmalm lane) apply, and
the semigroup structure (tone at `log p` times tone at `log q` = tone at
`log pq`) is the multiplicative closure the two-tone family was missing.
B†-compliance is automatic (Nehari conditions are sign/distance conditions,
not size bounds on von-Mangoldt sums).  Next: state the exact Nehari form —
identify whose Hankel operator has symbol built from `r`'s edge values on the
multiplicative grid, and what `dist_{H^∞}` the corner budget `c < 8`
translates to.

## Step-1b: Douglas form and the doubled-budget opening

By the Douglas range/majorization lemma, `c·Toeplitz − r r* ⪰ 0` on the
multiplicative grid is EQUIVALENT to: the response column is in the RKHS ball
of radius `√c` of the Cauchy–Toeplitz kernel.  That RKHS is explicit — the
kernel is `∫_0^∞ e^{−iux} e^{−x} dx`, so membership means

```text
∃ g : (0,∞) → ℂ,   ∫_0^∞ |g(x)|² e^{−x} dx ≤ c,
r(1/2 − i·log n) = ∫_0^∞ n^{ix} g(x) e^{−x} dx   for all n in the grid.
```

The demanded object is a MELLIN-DUAL DENSITY on the half-line with the
Gamma/Fisher exponential weight and energy at most `c < 8`.

**The doubled-budget opening.**  The C41 doubled Möbius parity source has
total asymptotic energy exactly `8 = 4 (father) + 4 (detail)`.  Every killed
transport (C41 detail-only, C42 ambient nonexpansive, C43 cofinal contraction,
C44 connection overspend) attempted to fund `r_P` from the 4-unit detail
alone, keeping the father block frozen at its Hardy Gram.  The threshold-8 law
proves the completeness corner is any `c < 8`: a JOINT father+detail spend —
deforming both blocks, total energy under two quanta — suffices for RH and is
not covered by any existing no-go (C43/C44 are budget-4 statements about the
detail channel with father orthogonality retained; the joint spend breaks
their hypotheses).  Exact next theorem candidate:

> `[CONJECTURE — JOINT TWO-QUANTUM TRANSPORT]`  The Gamma-completed doubled
> parity source admits a joint deformation of father and detail whose
> Mellin-dual density `g` has `∫|g|² e^{−x} dx < 8` and reproduces the edge
> response on the multiplicative grid.

Hostile gates before promotion: does joint spending re-enter C44's
overspend inequality (check: C44 forces `‖e‖² > 4` for the DETAIL carrying
the Ward column — the joint object need not present any single 4-bounded
detail, so C44's hypotheses fail — verify clause by clause); C39 Λ-anchoring;
B† sign-only compliance (Douglas membership is a sign condition ✓).

## Step-1c: hostile gates passed; the campaign estimate isolated

Desk results on the joint two-quantum transport conjecture:

1. **C44 clause-check `[PASSED]`**: the overspend theorems
   (`GammaSewnMobiusXiWardConnectionOverspend.lean`) force cost `> 4` on any
   single reproducing object — all their hypotheses are budget-4 statements;
   a budget-8 joint object satisfies `‖e‖² > 4` without contradiction.  The
   adapted INTERIOR node cost `≈ 2/a → ∞` (from `|r(conj λ)|² ≈ 1/a²`)
   operates only under ¬RH, where it is the proof's engine, not an
   obstruction to the mechanism.  No existing no-go reaches budget 8.
2. **C39 Λ-anchoring `[PASSED]`**: the doubled Möbius parity source is
   squarefree/von-Mangoldt-built.
3. **B† compliance `[PASSED]`**: Douglas membership is a representation
   condition (sign), not a size bound on a Λ-sum.

**Reduction.**  Reproduction of the edge response must come from the proven
source seam identity (`P_anti Q_sq = ell_E` lane,
`ProjectiveHorizonWardSeam.lean`), not from an estimate.  The conjecture then
carries exactly ONE load-bearing estimate:

> `[OPEN CORE — TWO-QUANTUM ENERGY LAW]`  The Mellin-dual density `g`
> produced by the seam identity from the Gamma-completed doubled parity
> source satisfies `∫_0^∞ |g(x)|² e^{−x} dx ≤ 8`, with equality defect the
> causal quantum (`8 = ‖father causal‖² + ‖detail causal‖² + ‖ell_E‖²`-form).

This is the CCM infinite-source-convergence gap at DOUBLED budget — strictly
weaker than the four-unit form that C41–C44 attacked, and the first version
whose no-go surface is empty.  Campaign plan: (i) construct `g` explicitly
from the doubled seam (paper); (ii) prove finiteness of its energy
(convergence — the genuinely hard step); (iii) the `≤ 8` bound; (iv) Lean.
Note (edge variant): a two-symmetric-detector edge version of threshold-8
fails at low heights (the `1/(1+2ib)` off-diagonal is not small) — the
interior-node formalization is the correct and sufficient form; do not build
the edge variant.

## Step-2: the two-quantum construction, verified ledger, and the Mosco seam frontier

Construction phase complete (desk-verified line by line; report cross-validated
against an independent derivation of the same objects):

**The witness.**  `g = e^{x/2} ℓ_E`, the anti-causal output of the seam applied
to the two-quantum source `Ψ = 2k_{1/2} ⊕ D` in
`H_src = L²((0,∞), dt) ⊕ ℂ·D`.  Douglas energy `= ‖ℓ_E‖²` exactly (the
corner-8 weight `e^{−x}` IS the corpus four-unit Fisher weight; no change of
variable).  Ledger in the x-chart: father `g_F = 2` (energy 4, the Euler-pole
atom = base tangent of the PROVEN normal-cone family `T̃_σ = 1/(G(σ)X_sq)`,
NOT a pole of Q_sq), detail `g_D = 2(1−x)` (energy 4, the Fisher score =
Laguerre `L₁`), cross-energy 0 (Laguerre orthogonality; and the true carrier
is the TRANSVERSE doubled detail, exactly father-orthogonal at every finite σ
— C41.1 — which is what the C39 cusp cannot counterfeit).  Total `8 = 4 + 4`.

**Killed shortcut `[RECORDED]`.**  The static density `4 − 2x` reproduces the
CAUSAL response family `4/a_n − 2/a_n²` (Abel side; nonzero under RH), never
`r`.  The seam produces `g` only as the anti-causal OUTPUT of the transported
`Ψ`; presenting `ℓ_E` as augmented INPUT is C44's overspend and is the
orientation error to avoid.

**Endpoint consumed.**  `XiWardThresholdEightClosedCompleteness.lean`
(`riemannHypothesis_iff_continuedXiWardCornerLiftLaw_eight`, parallel-agent
build, verified compiling clean): the CLOSED budget `c = 8` is RH-complete.
So the campaign needs `‖ℓ_E‖² ≤ 8` — saturation admitted, no strict loss to
manufacture.  Reduction chain (R1)–(R7) recorded with exactly two gaps:
(G1) L²-convergence of the pair series = the interchange in
`r(w) = ⟨k_w, ℓ_E⟩` (subsumed by G2); (G2) the transport bound.

**C42 resolved by blow-up `[KEY STRUCTURAL FACT]`.**  C42's nonexpansiveness
no-go gain `1/(2(σ−1))` is exactly the order-one vanishing of `1/ζ(σ)`; the
corpus's formalized normal-cone blow-up `T̃_σ = T_σ/(σ−1)` removes precisely
that order.  The C42 obstruction is the normal-cone divisor and its
resolution is already in the tree; the graph limit must be taken on the
blown-up family.

> **[THEOREM CANDIDATE — TWO-QUANTUM MOSCO SEAM LAW]**  On `H_src` with the
> exact C41 Gram, the graphs of the blown-up completed Möbius–Gamma transfers
> `T̃_σ` Mosco/graph-converge as `σ ↓ 1` along the physical clock to a closed
> nonexpansive `U_seam` with `P_anti U_seam Ψ = ℓ_E` (witness sense).
> Corollary: `‖ℓ_E‖² ≤ 8` → corner-8 law → RH.

Lemma plan: (L1) finite-σ contractivity `[CORPUS, transfer card (7b)]`;
(L2) Gamma base congruence `[CORPUS, gamma-moving-base-capacity-congruence]`;
(L3) Mosco convergence of the blown-up graphs `[NEW — the sole hard step;
C42 blocks only the un-blown-up family]`; (L4) `P_anti` commutes with the
graph limit, transferring the proven seam symbol (R5) `[NEW glue]`;
(L5) norm lower semicontinuity under Mosco `[standard]`.
If (L3) fails, its defect is the affine Ward-defect field
(`ht-capacity-ward-holonomy-rh.md` (25)) — a positive HT invariant.

**Active desk task (mine):** the finite-σ joint Julia codiagonal of `Ψ` —
the blown-up two-jet of `T̃` at the base as an explicit per-node 2×2
first-order family (σ-jet is scalar `−γ_E(σ−1)` to first order from
`G(σ) = 1 + γ_E(σ−1) + O((σ−1)²)`; the content is the joint (σ, clock) jet
on the doubled space), turning (L3) into explicit per-aperture-pair
Cauchy–Schwarz inequalities on the clock.

## Step-3: L3 structural desk round — the seam law is a 1-jet prolongation limit

Findings (desk, from the corpus Julia block in
`GammaSewnMobiusXiWardHardyTransport.lean` 600–700):

1. **The multiplier is σ-fixed.**  `logDeriv` kills the scalar `1/G(σ)`, so
   the σ-deformation of the blown-up transfer family lives entirely in the
   STATES (the Möbius likelihood at temperature σ), not in the multiplier.
   The Julia identity `JuliaDefect = CrossRatio·GramCell − GramCell` is exact
   and algebraic at every aperture; the aperture tangent of the phase is
   `−2i·logDeriv Π_right` (formalized).
2. **Ψ is the 1-jet.**  `∂_σ father = Fisher score = detail direction`: the
   two-quantum source is exactly the first-jet prolongation of the father
   flow at the Euler boundary.  The Mosco seam law = graph convergence of the
   transported 1-jet prolongation.
3. **Anti-causality is the noncommuting mixed jet.**  Fixed-σ (safe) limits
   produce the CAUSAL column (`4/a − 2/a²` family — the recorded killed
   shortcut); the continued column `r` can only arise as the derived defect
   of the noncommuting (α, σ) limit.  The physical diagonal `α = (σ−1)·τ`
   (C42's coupling) is the correct scaling; along it, first-order objects are
   `lim (σ−1)·J_σ`-type residues — where the reflected-pole content crosses.
4. **Budget arithmetic consistent.**  C43's slack law
   `|⟨Tx,Td⟩−⟨x,d⟩| ≤ ‖x‖·√(loss d)` with BOTH quanta live (father no longer
   frozen) permits nonzero limiting codiagonals funded by joint loss ≤ 8;
   the ¬RH-side interior blow-up (`|r(λ̄)| ~ 1/a` vs Cauchy–Schwarz ceiling
   `2/√a`, crossing at `a = 1/4`) is the proof engine, not an obstruction.

**Next computable object (the narrowed L3):** the finite-σ transported
codiagonal `⟨V F_{σ,u}, V D_σ⟩` explicitly — `V` the fixed Gamma/Xi
multiplier, states explicit corpus objects — and its σ↓1 limit along the
physical diagonal.  If the limit equals the `r`-column (the seam symbol at
finite-σ verification), L4's glue becomes finite-σ-explicit and the whole
seam law reduces to the norm inequality alone (joint loss ≤ 8 in the limit),
which is L5-shaped (lower semicontinuity) once the codiagonal identity is
explicit.  This computation is the current active task.

## Step-4: the codiagonal symbol is already formalized — one inequality remains

Corpus discovery (mandate check, decisive):
`GammaSewnMobiusXiWardJuliaTransport.lean` already certifies the finite-σ
codiagonal identity demanded by Step-3:

- `squarefreeMobiusGammaXiWardTransportV_actualTangent`: on the physical
  diagonal `s = σ + u(σ−1)`, the composed Möbius–Gamma graph transport of
  the ACTUAL Fisher tangent equals
  `continuedPrimeArchSourceRelativeTrace (xiWardCenteredCoordinate s)` —
  the continued Xi source column, at every finite `σ > 1`, every aperture.
- `hasDerivAt_xiWardAnchoredSourceTransportV_actualTangent`: this transported
  codiagonal IS the Julia tangent of the anchored transport at aperture 0.

Ledger of the Two-Quantum Mosco Seam Law after this discovery:

- L1 finite-σ contractivity — `[CORPUS]`
- L2 Gamma base congruence — `[CORPUS]`
- L4 symbol core (finite-σ codiagonal = continued column) — `[CORPUS]`
  (`_actualTangent`); residual glue = boundary-value passage σ↓1 of the
  continued trace + the PROVEN anti-causal localization `P_anti Q = ell_E`.
- **L3/L5 — THE open inequality**: the limiting joint transported energy of
  the blown-up 1-jet `Ψ` does not exceed `8`.  Everything else surrounding
  the unconditional positivity of `W_P` is machine-checked: corner-8
  completeness (closed endpoint), the witness and its exact 8-unit ledger,
  the symbol identity, the anti-causal projection, and the RH conversion.

The program's open core is now literally ONE norm inequality over proven
objects.  C42 proves its ambient-norm form false; the formalized blow-up
removes the known divergence; the graph/Mosco topology is its designed home;
its failure mode is the affine Ward-defect field (a positive HT invariant
either way).  Next round: formulate the exact graph norm on the blown-up
1-jet family and run the semicontinuity argument on the transported energy.

## Step-5: chart trichotomy and the polarized cross-defect reduction

Semicontinuity round diagnostic (desk, verified against corpus records):

- **Raw chart diverges**: on the physical diagonal the Euler pole enters the
  transported family at amplitude `1/(σ−1)`; diagonal Hardy energy `→ ∞`.
- **Completed chart inflates**: the completed detail splits `16 (causal) +
  4 (anti) = 20` (`mobius-mellin-gamma-normal-cone.md` §2 — "Gamma completion
  is not a global contraction"); ledger `4 + 20` overshoots.
- **Source-polarized chart is forced**: there the two PROVEN laws are the
  diagonal entries — four-unit Fisher (detail → 4) and Gamma base congruence
  (father → 4).  The entire remaining content is off-diagonal.

> **[OPEN CORE — POLARIZED CROSS-DEFECT SIGN]**
> `limsup_{σ↓1} Re χ(σ) ≤ 0`, where `χ(σ)` is the source-polarized
> father–detail cross energy of the transported two-quantum jet.
> Then `E(σ) = 4 + 4 + 2Re χ(σ) + o(1) ≤ 8`, lower semicontinuity gives
> `‖ℓ_E‖² ≤ 8`, and the closed corner-8 law converts to RH.

A sign, not a size — B†-compliant by construction; χ is parity-built
(C39-anchored).  **Candidate mechanism**: the detail is J-odd, the father
J-even, for the parity/swap involution `J`; if the transported polarization
is J-equivariant, `χ ≡ 0` identically by grading and the ledger closes at
exactly `8 = 4 + 4 + 0`.  **Hostile flag (mandatory next check)**: transport
J-equivariance is plausible (coefficient-blind multiplier), but
J-equivariance of `P_anti` is exactly where the arithmetic sits — the parity
flip on the continued side is the Möbius-inversion/FE structure, so the
symmetry claim may itself be RH-adjacent.  It is TESTABLE at finite σ:
`squarefreeMobiusGammaXiWardTransportV_actualTangent` makes χ(σ) an explicit
pairing of two known σ-families of zeta objects on the safe side.  Next
round: write χ(σ) explicitly and determine its sign structure (grading proof
or counterexample); either outcome is certifiable — χ ≡ 0 closes the seam
law; χ > 0 asymptotically is the affine Ward-defect field made explicit.

## Step-6: the fake proof and its unique gap — the four-four chart identity

Fake-proof skeleton (move 19), each link labeled:

1. **Jet coincidence on the diagonal** — transported σ-score = aperture
   derivative of the anchored family at the diagonal anchor.
   `[CORPUS at codiagonal level: squarefreeMobiusGammaXiWardTransportV_actualTangent
   + hasDerivAt_xiWardAnchoredSourceTransportV_actualTangent; operator-level
   upgrade needed]`
2. **Polarized chart has a Laplace model** — the source Hardy polarization is
   a Hardy chart.  `[CORPUS polarization lane]`
3. **Derivative-pairing sign** — in any Laplace model,
   `⟨F, F′⟩ = −∫₀^∞ x|f(x)|² dx ≤ 0`.  `[ELEMENTARY — certifiable now]`
4. **Four-four chart identity** — in the COMMON polarized Hardy chart the
   transported father carries exactly 4 units (the (0d) anti-pole budget
   `−4/s` — father side already matched in
   `mobius-mellin-gamma-normal-cone.md`) and the transported detail carries
   exactly 4 (the Fisher law through the Gamma congruence).  `[THE GAP —
   an EQUALITY between proven quantities in specified charts; the completed
   chart's 16+4 detail inflation is the known failure of the WRONG chart;
   a normalization mismatch c ≠ 1 gives ledger 4 + 4c² + 2c·(≤0) — still
   closes for c ≤ 1, fails only for c > 1, and any failure constant
   quantifies the affine Ward-defect field]`
5. Ledger `E ≤ 8 + o(1)` → semicontinuity → `‖ℓ_E‖² ≤ 8`.  `[L5 standard +
   (R7) derived]`
6. Corner-8 → RH.  `[CERTIFIED: riemannHypothesis_iff_continuedXiWardCornerLiftLaw_eight]`

The open core of the program is now: **prove the four-four chart identity
(with the operator-level jet coincidence), or exhibit its defect constant.**
Balance note (B†-discipline): a chain of proven pieces ending at RH must
carry its hard core somewhere; it is now provably CONCENTRATED in link 4
(plus the operator upgrade of link 1) — everything else is certified,
elementary, or standard.  Next round: attack link 4 head-on from the corpus
normalizations — the father half is done in (0d); the detail half is the
Fisher-4 transported through `gamma-moving-base-capacity-congruence`, and
`c ≤ 1` (nonexpansive congruence toward the boundary) ALREADY SUFFICES,
which is strictly weaker than the exact identity.

## Step-7: link 4 splits — Gamma leg closed, Xi-weld leg is the core

Corpus check of the congruence constant delivered more than `c ≤ 1`:
`GammaMovingBaseCapacityCongruence.lean : tendsto_gammaMovingBaseTangentFactor_one`
proves the comparison factor tends to the IDENTITY on the common collar
("asymptotically isometric, not merely uniformly equivalent"), with the
uniform bounds `(16/81, 16)` available as domination.

Link 4 therefore splits:

- **(4a) Gamma-chart leg — CLOSED (up to one lemma).**  Pointwise factor → 1
  + uniform 16-domination + dominated convergence upgrades the source
  Fisher-4 to the Gamma-chart transported energy → 4.  Queue the DC-upgrade
  lemma for Lean (`tendsto` + `MeasureTheory.tendsto_integral_of_dominated_convergence`
  shape; verify the detail's boundary-layer concentration (C39, t → 0) sits
  inside the collar — it is the collar center).
- **(4b) Xi-weld leg — THE REMAINING CORE.**  The energy behavior of the
  detail through the singular source-overlap graph + strict-right
  correction.  Narrowest form: **single-vector nonexpansiveness of the
  welded transport on Ψ's orbit at budget 8** — C42 kills only the
  all-vector ambient form; the C44 family stops at budget 4 (step-1c
  clause-check); the blow-up removes the known divergence.  No corpus no-go
  reaches this statement.

Chain status: 1 [codiagonal formalized; operator upgrade open],
2 [corpus], 3 [elementary], 4a [closed modulo DC lemma], **4b [OPEN CORE]**,
5 [standard], 6 [certified].  The unconditional positivity of `W_P` is now
equivalent, over certified links, to the single-vector budget-8
nonexpansiveness of the Xi weld on the two-quantum orbit.

## Step-8: the diagonal route is KILLED at link 5 — Euler-locality theorem

Direct computation of the zero-pole flow in the physical-diagonal chart
kills the step-5/6/7 chain at its transfer step:

- A fixed zero `ρ` sits at `u_ρ = (ρ−1)/(σ−1)` in the diagonal chart —
  escaping to infinity as `σ ↓ 1`: the diagonal ZOOMS at the Euler point.
- Its pole amplitude in the u-chart is the fixed residue `m_ρ` (the
  `(σ−1)`-factors cancel through `ds = (σ−1)du`), on the anti-causal side
  (`Re u_ρ < 0` ✓), at distance `(1−Re ρ)/(σ−1)`.
- Its anti-causal Hardy energy is therefore
  `≈ m_ρ²(σ−1)/(2(1−Re ρ)) → 0`.

> **[EULER-LOCALITY THEOREM — certifiable positive residue]**  In the
> physical-diagonal chart every fixed off-line zero contributes vanishing
> anti-causal energy as `σ ↓ 1`; the diagonal limit is Euler-local and
> blind to the global divisor.  Consequently NO diagonal-limit energy bound
> transfers to `‖ℓ_E‖²`; link 5 of the step-6 skeleton is false as stated.

Status revision: links 1–4 stand as statements about the diagonal family
(4a's Gamma-leg closure and the derivative-pairing sign remain true and
useful), but the chain to RH is broken at the chart transfer.  The
two-quantum seam law survives only in MULTI-ANCHOR form: the transported
family must be anchored at ALL edge heights simultaneously (the anchored
transport at `w = 1/2 + it` for all `t` — where the per-anchor bound
`‖V‖ ≤ 2` is corpus-certified and the divergence under ¬RH is carried by
the anchor-sum).  Full circle with new content: the certified sampled/
prime-log machinery IS the correct frame for the multi-anchor energy, and
the open core returns to the honest form `‖ℓ_E‖² ≤ 8` with the diagonal
shortcut now provably closed.  Next: formalize the Euler-locality residue
(elementary, quantitative) and reformulate the two-quantum spend
anchor-uniformly (the father/detail budget per anchor, summed against the
sampled Gram — where threshold-8's per-pair floor and the mass quantization
already live on the certified side).

## Step-8b: Euler locality formalized `[PROVED AND LEAN-FORMALIZED]`

`XiWardDiagonalEulerLocality.lean` (standard axioms, lint clean) certifies
the step-8 kill:

- `xiWardDiagonalPullback_maps` / `re_xiWardDiagonalPullback_neg`: the
  diagonal pullback of any point left of the Euler edge is anti-causal.
- `xiWardDiagonalPoleEnergy_eq_cauchySelfEnergy`: the diagonal pole energy
  is the Cauchy self-energy at the reflected pullback distance.
- `tendsto_xiWardDiagonalPoleEnergy_zero`: **Euler-locality law** — every
  fixed divisor point's diagonal anti-causal energy vanishes as `σ ↓ 1`.
- `tendsto_xiWardDiagonalDivisorEnergy_zero`: **finite divisor blindness** —
  over every finite set of strict-right copies the total diagonal energy
  vanishes.  The diagonal shortcut to `‖ℓ_E‖² ≤ 8` is now a formal no-go.

Open core unchanged and honest: `‖ℓ_E‖² ≤ 8` in multi-anchor form.  Next:
the anchor-uniform two-quantum accounting against the certified sampled
Gram machinery.

## Step-9: edge-L² quantization and the 8π single-integral completeness law

Multi-anchor accounting, first certified-shape results (desk, Plancherel
cross-checked):

- **Weight bookkeeping (near-miss killed).**  `∫|r(1/2+it)|²dt =
  2π·‖e^{−x/2}ℓ_E‖²` — the HALF-weighted energy, not the Douglas/grid
  energy `‖ℓ_E‖²`.  A distant pair deposits only `2π·4/x < 16π`, so the
  16π-threshold integral criterion is NOT RH-complete (distant-pair evasion,
  same structure as corner-`c > 8`).  Grid moments (e^{−x}-weight, discrete)
  and edge Fourier (continuous) are different functionals; do not conflate.
- **Per-pair edge deposit, exact:**  `2π·4[1/x + x/(x²+b²)]` with
  `x = a + 1/2 ∈ (1/2, 1)` — always `> 8π`, infimum exactly `8π`
  (b → ∞, x → 1).  Cross-pair edge pairings have positive real part
  (half-weighted H² pairings of RHP kernels).
- **New completeness law `[DESK-PROVED — QUEUE FOR LEAN]`:**

  ```text
  RH  <->  ∫_ℝ |r(1/2+it)|² dt ≤ c,   for every fixed 0 ≤ c < 8π,
  ```

  sharp at `8π = 2π·4` — the four-unit budget as the half-weighted floor.
- **Load-bearing integral:** with `u = x+i(t+b)`, `v = x−i(t−b)`:
  `uv = t² − c²`, `c = b − ix`, poles split across the axis, and
  `∫_ℝ dt/(t²−c²) = −iπ/c`, giving cross term `Re = πx/(x²+b²)`; total
  `∫|pair|² = 2π·4[1/x + x/(x²+b²)]` ✓ (matches Plancherel exactly).
  Lean route: partial fractions to real rational integrals (Lorentzian
  family with completed squares) or the complex two-pole computation;
  the `lintegral_tsum` + Countable-instance pattern of
  `XiWardEdgeMassQuantization.lean` carries the summation layer.

Module queued: `XiWardEdgeL2Quantization.lean` — per-pair deposit identity,
positive cross terms, the 8π completeness iff, and sharpness note (meta:
c ≥ 8π admits distant-pair evasion; do not formalize the evasion).

## Step-9b: cross-kernel foundation layer `[LEAN-FORMALIZED]`

`XiWardEdgeL2CrossKernel.lean` (standard axioms, lint clean): the algebraic
core of the edge-L² quantization — constant-sum splitting
`u + v = (x₁+x₂) + i(β₁−β₂)` (t-free), the exact partial fraction
`1/(uv) = (u+v)⁻¹(1/u + 1/v)` (`inv_mul_eq_sum_inv`,
`edgeCrossKernel_eq_split`), and the four re/im kernel-inverse Lorentzian
identities.  Remaining for the 8π law: the three real-integral evaluations
(Lorentzian π each; the two shift/width difference integrals vanish — FTC
log-limit and odd symmetry), assembly into `∫ edgeCrossKernel = 2π/K`, the
|pair|² expansion, and the tsum layer via the mass-quantization pattern.

## Step-9c: integrability layer `[LEAN-FORMALIZED]`

Appended to `XiWardEdgeL2CrossKernel.lean` (standard axioms, build clean):

- `one_add_sq_le_shifted`: explicit quadratic domination
  `1 + t² ≤ C(x,β)·(x² + (t+β)²)`.
- `norm_edgeCrossKernel_le`: `‖edgeCrossKernel‖ ≤ √(C₁C₂)·(1+t²)⁻¹` —
  the explicit Cauchy-weight domination.
- `integrable_edgeCrossKernel`: the cross kernel is integrable on the line
  (continuity + domination + `integrable_inv_one_add_sq`).

Remaining units for the 8π law, in order: (i) the master evaluation
`∫ edgeCrossKernel = 2π/K` via the split (Lorentzian π-halves; the two
vanishing imaginary combinations: odd-symmetry width difference and
FTC-log shift difference); (ii) `|pair|²` expansion into four cross kernels;
(iii) per-pair deposit `= 2π·4(1/x + x/(x²+b²)) > 8π` (floor is `1/x > 1`);
(iv) cross-pair positivity from `Re(2π/K) > 0`; (v) the tsum layer
(mass-quantization pattern) and the completeness iff.

## Step-9d: master-evaluation layer, part 1 `[LEAN-FORMALIZED]`

Appended to `XiWardEdgeL2CrossKernel.lean` (build clean, standard axioms):

- `lorentzianHalf_integrable` / `integral_lorentzianHalf`: the shifted
  Lorentzian half `x/(x²+(t+β)²)` is integrable with total mass `π`.
- `integral_oddWidthPiece_zero`: the centered width-difference is odd with
  vanishing integral (`integral_neg_eq_self`).
- `hasDerivAt_halfLogShift` + `integral_shiftDiffPiece_zero`: the
  shift-difference of Lorentzian tilts vanishes by the FTC log-limit
  (interval FTC + `intervalIntegral_tendsto_integral` + the log-ratio → 1
  tendsto chain).

Remaining: im-sum assembly (integrability transfers via `Integrable.im` and
subtraction), `∫(u⁻¹+v⁻¹) = 2π` via `Complex.ext` with
`reCLM/imCLM.integral_comp_comm`, the master `∫ edgeCrossKernel = 2π·K⁻¹`,
then pair expansion, deposit floor, cross positivity, tsum layer,
completeness iff.

## Step-9e: odd-piece layer `[LEAN-FORMALIZED]`

`integrable_oddPieceShifted` (conjugation-symmetric domination through the
cross kernel — no new estimate needed) and `integral_oddPieceShifted_zero`
(shift reduction + odd symmetry) are certified.  The imaginary-sum
cancellation now has both of its pieces: this odd layer and the FTC log-limit
shift layer (step 9d).  Final assembly unit remaining for the master
identity: im-total = shiftDiff + oddShifted (integrability by subtraction),
`∫(u⁻¹+v⁻¹) = 2π` by `Complex.ext` through `reCLM/imCLM.integral_comp_comm`,
and `∫ edgeCrossKernel = 2π·K⁻¹`; then pair expansion → deposit floor →
cross positivity → tsum layer → the 8π completeness iff.

## Step-9f: THE MASTER IDENTITY `[LEAN-FORMALIZED]`

`integral_edgeCrossKernel_eq` is certified (standard axioms, build clean):

```text
∫_ℝ dt / [(x₁ + i(t+β₁))·(x₂ − i(t+β₂))] = 2π / K,
K = (x₁+x₂) + i(β₁−β₂),
```

via `integral_kernelSum = 2π` (real part: two Lorentzian halves at π each;
imaginary part: FTC log-limit shift piece + odd width piece, both vanishing;
assembly by `integral_re_add_im`).  This is the single integral from which
every edge-L² pairing of pair responses follows: `|pair|²` expands into four
cross kernels, cross-pair pairings are sums of eight, all with
`Re(2π/K) > 0`.  Remaining for the 8π completeness law: the expansion
plumbing, the deposit identity `2π·4(1/x + x/(x²+b²))` with its floor
(`1/x > 1`), the tsum layer (mass-quantization pattern), and the iff.

## Step-9g: pair expansion `[LEAN-FORMALIZED]`

`xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq_kernels` (the full complex
kernel identity at the edge, upgrading the earlier real-part version) and
`normSq_xiPairEdge_eq_four_sum` (the squared edge modulus of one pair equals
`4·Σ` of four cross-kernel real parts) are certified — zero warnings.
With the master identity, each of the four integrates in closed form:
diagonal terms `Re(2π/(2x)) = π/x`, off-diagonal `Re(2π/(2x±2ib)) =
πx/(x²+b²)`.  Next unit: the deposit theorem
`∫ normSq(pair-edge) = 2π·4(1/x + x/(x²+b²)) > 8π` (integrate the four-sum,
floor from `1/x > 1`), then cross-pair positivity, the tsum layer, and the
8π completeness iff.

## Step-9h: THE DEPOSIT THEOREM AND ITS FLOOR `[LEAN-FORMALIZED]`

Certified (standard axioms, zero warnings):

- `integral_re_edgeCrossKernel`: closed form
  `∫ Re(eck) = 2π·2x/((2x)² + (β−β')²)` from the master identity.
- `integral_normSq_xiPairEdge`: **the per-pair edge deposit**

  ```text
  ∫_ℝ |pair(1/2+it)|² dt = 2π·4(1/x + x/(x²+b²)),  x = Re λ + 1/2, b = Im λ.
  ```

- `eightPi_lt_integral_normSq_xiPairEdge`: **the 8π floor** — every
  strict-right pair deposits strictly more than `8π` (from `1/x > 1`).

Remaining for the 8π completeness law: cross-pair positivity (each of the
eight cross integrals has `Re(2π/K) > 0` — immediate from the master
identity's closed form), the tsum layer (lintegral/Countable pattern from
`XiWardEdgeMassQuantization`), and the completeness iff (RH direction: r ≡ 0;
¬RH direction: one pair's floor beats any budget `c < 8π` through positive
cross terms).

## Step 9i — the 4π closed-budget edge completeness law [PROVED HERE]

Module `formal/GaloisForLFunctions/RHTower/XiWardEdgeL2CrossKernel.lean` (1275 lines,
compiles clean, all results on `propext, Classical.choice, Quot.sound` only; lint clean;
umbrella wired; index regenerated).

New certified layers (this round):
- `integral_sq_rightKernel_inv` — ∫_ℝ (x+i(t+β))⁻² dt = 0.  Complex FTC with antiderivative
  i·u⁻¹ (composition `hasDerivAt_inv` ∘ affine via `HasDerivAt.scomp`), boundary decay by
  ‖u⁻¹‖ ≤ (x²+s²)^{-1/2} squeeze.  The holomorphic square drops all its mass at infinity.
- `integral_sq_lorentzianHalf` — ∫ (x/(x²+(t+β)²))² dt = π/(2x) via the pointwise split
  (Re w)² = ½(Re(w²) + |w|²), w = (x+i(t+β))⁻¹: the w² part vanishes by the FTC lemma,
  the |w|² part is half the Lorentzian mass.  No interval-integral asymptotics needed.
- `integrable_sq_lorentzianHalf` — domination by x⁻¹·(Lorentzian half).
- `sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_ge` — (Re pair)² ≥ 4L̃₁² + 4L̃₂²
  (cross term 8L̃₁L̃₂ ≥ 0 dropped by explicit ring identity).
- `lintegral_normSq_continuedXiAntiCausalWardResponse_edge_lower` — every strict-right pair
  q forces ∫⁻_t normSq r(½+it) ≥ ofReal(4π/x), x = Re λ + ½.  Chain: Herglotz domination
  Re r ≥ Re pair (corpus `re_xiAntiCausalWardSchwarzPairResponse_le_continued`, found in
  `GammaSewnMobiusXiWardEulerEdgeCompleteness` — corpus search fired AFTER a name collision;
  reminder reinforced), square monotone on nonnegatives, normSq ≥ re².
- **`riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw`** — for ANY fixed budget
  0 ≤ c ≤ 4π (CLOSED endpoint):  RH  ⟺  ∫⁻_t ofReal(normSq r(½+it)) dt ≤ ofReal c.
  Forward: RH ⟹ divisor empty ⟹ r ≡ 0 ⟹ integral 0.  Backward: one pair deposits
  4π/x > 4π strictly since x < 1 strictly.  The closed endpoint c = 4π is admissible —
  the integrated criterion needs NO margin slack, mirroring the closed c = 8 corner law.

Desk ledger for the sharp per-pair Re-part deposit (not yet formalized):
∫(Re pair)² = 4π/x + 8∫L̃₁L̃₂ = 4π/x + 4πx/(x²+b²) = 4π(1/x + x/(x²+b²)) — exactly half
the normSq deposit 8π(1/x + x/(x²+b²)); the imaginary part carries the other half.  The
cross-Lorentzian ∫L̃₁L̃₂ = πx/(2(x²+b²)) is reachable from the certified master identity
`integral_edgeCrossKernel_eq` + `integral_shiftDiffPiece_zero` (same-side pair kills by the
log-limit FTC piece; NO new Fubini needed for a single pair).

What this OPENS (next generative moves, in order):
1. **Multi-pair superadditivity**: Re r = Σ_q Re pair_q with every summand pointwise ≥ 0,
   so ∫(Re r)² ≥ Σ_q ∫(Re pair_q)² + nonneg cross terms.  Each summand ≥ 4π.  A second
   off-critical pair pushes the floor past 8π WITHOUT the double-series Fubini obstacle —
   cross terms are dropped, not interchanged.  Target: a certified law
   "N distinct pairs ⟹ floor N·4π", i.e. the integrated criterion COUNTS the divisor.
2. **Margin-quantified floor**: x ≤ 1 − m(b) (zero-free margin) gives per-pair floor
   4π/(1−m(b)) ≥ 4π(1+m(b)) — the integrated law carries the 9-log-power margin as a
   quantitative excess; connects the edge-L² capacity dial to the B† Legendre-neutrality
   exponent pairing (9, 1/10).  New dial for the Chart–Region Exchange: what PNT exponent
   does an integrated-capacity loop demand?
3. **Sharp Re-part single-pair law**: formalize ∫(Re pair)² = 4π(1/x + x/(x²+b²)) from the
   certified cross-kernel pieces; near-critical pairs (a → 0) deposit → 8π in the Re part
   alone — the deposit GRADES the violation distance.

## Step 9j — the divisor-counting and finiteness laws [PROVED HERE]

Same module, next layer (compiles clean, standard axioms, index regenerated):
- `xiWardPairEdgeQuadMinorant` + nonneg/le/integrable/integral lemmas — per-pair diagonal
  quadratic minorant with exact mass 4π/x_q.
- `sum_xiWardPairEdgeQuadMinorant_le_normSq` — superadditive pointwise floor over ANY finite
  family F: Σ_F minorant ≤ normSq r on the edge.  Mechanism: Σ_F Re pair ≤ Re r (finite
  subsum ≤ tsum of nonnegatives), Cauchy diagonal Σ a² ≤ (Σ a)² for nonneg a
  (`Finset.sum_sq_le_sq_sum_of_nonneg`), normSq ≥ re².  Cross terms DROPPED, never
  interchanged — the double-series Fubini obstacle from the 8π-sharp attempt never enters.
- `xiWardEdgeQuadEnergy : ENNReal` — the total edge quadratic energy, now a named object.
- **`card_nsmul_le_xiWardEdgeQuadEnergy`** — ofReal(4π·|F|) ≤ energy for every finite F:
  the edge L² functional COUNTS strict-right pairs, 4π per pair.
- **`card_le_of_xiWardEdgeQuadEnergy_le`** — an energy budget c caps every finite family at
  c/(4π) pairs: a quantitative zero-counting bound from a single integrated inequality.
- **`finite_xiRightUpperZeroCopy_of_xiWardEdgeQuadEnergy_ne_top`** — finite edge quadratic
  energy ⟹ the strict-right divisor is FINITE.  Contrapositive: an infinite off-critical
  divisor forces infinite edge energy.  Together with the closed 4π law: the energy is
  either 0 (RH) or > 4π (≥ one pair) or ∞ (infinitely many pairs) — the intermediate
  regime (finite, > 4π) is occupied exactly by ¬RH with a finite nonempty divisor.

What this OPENS: the trichotomy above splits ¬RH into two channels with different
obstruction profiles.  (i) The infinite-divisor channel is now killed by ANY finite energy
certificate — no sharp constant needed at all; an upper bound of the form
∫⁻ normSq r < ∞ suffices against it.  (ii) The finite-divisor channel is where the whole
4π/8π budget battle lives — and a FINITE divisor is an algebraic object: finitely many
poles, a rational Ward response, a FINITE-RANK Hankel/Toeplitz defect.  Next generative
move: attack channel (ii) with the finite-rank structure — for a finite divisor the
two-quantum witness comparison becomes a finite-dimensional eigenvalue problem (Nehari for
rational symbols), where the 4-vs-8 threshold may close by linear algebra instead of
infinite-dimensional operator theory.  Sub-question to card: does the corpus already hold a
finite-rank Nehari/AAK piece to collide with `finite_xiRightUpperZeroCopy_of_...`?

## Step 9k — margin floors, energy dichotomy, height-window clearing [PROVED HERE]

New leaf module `formal/GaloisForLFunctions/RHTower/XiWardEdgeEnergyMarginWindow.lean`
(compiles clean, standard axioms, umbrella wired, lint clean, index regenerated).
rng pick chose this track over finite-rank-nehari / sharp-re-deposit / weil-pairing.

- `margin_floor_le_xiWardEdgeQuadEnergy` — per-pair floor sharpened by the zero-free
  margin: ofReal(4π/(1 − m(b_q))) ≤ energy (from a ≤ ½ − m(b), denominator antitone).
- `fourPi_margin_budget_lt_floor` — 4π(1+m) < 4π/(1−m) strictly (the (1−m²)-gap).
- **`xiWardEdgeQuadEnergy_eq_zero_or_fourPi_lt`** — UNCONDITIONAL dichotomy: the edge
  quadratic energy is exactly 0 or strictly above 4π; the open interval (0, 4π] is
  forbidden.  Case split on the divisor type, no RH input.
- **`height_lt_abs_im_of_xiWardEdgeQuadEnergy_le`** — height-window clearing: an energy
  certificate ≤ 4π(1 + m(T)) forces every strict-right pair above height T.  The
  integrated criterion now supports PARTIAL verification: finite budgets clear finite
  height windows, with the 9-log-power margin as the exchange rate (B† dial: the window
  grows like exp(c/slack^{1/9}) per unit of budget slack — the Legendre pairing surfaces
  in the integrated criterion exactly as in the pointwise one).

What this OPENS: the forbidden zone (0, 4π] is a SPECTRAL GAP of the edge functional.
Three live continuations: (1) formalize ∫(Re pair)² = 4π(1/x + x/(x²+b²)) (sharp
Re-deposit; near-critical pairs → 8π) so the gap widens to (0, 8π) on the Re-channel;
(2) the finite-rank channel: `finite_xiRightUpperZeroCopy_of_xiWardEdgeQuadEnergy_ne_top`
+ corpus `FiniteModalHankelRank` (Vandermonde mode-count certificates, found this round)
— collide the finite-divisor rational response with the Hankel mode-count machinery;
(3) counting + margin fusion: N pairs below height T force energy ≥ N·4π(1+m(T)) — a
graded zero-density bound from one integral.

## Step 9l — sharp real-channel deposit and edge equipartition [PROVED HERE]

New module `formal/GaloisForLFunctions/RHTower/XiWardEdgeReChannelDeposit.lean`
(compiles clean, standard axioms, umbrella wired, index regenerated).  rng pick chose
sharp-re-deposit over finite-rank-collision / counting-margin-fusion / cross-terms / wild.

- `integrable_sameSideKernelMul` — same-side kernel product has the cross-kernel modulus
  (conjugation norm identity), hence integrable.
- **`integral_sameSideKernelMul_zero`** — ∫ (x+i(t+β₁))⁻¹(x+i(t+β₂))⁻¹ dt = 0 for
  β₁ ≠ β₂: both poles in one half-plane.  Mechanism: constant-difference partial fraction
  (u₁u₂)⁻¹ = (i(β₂−β₁))⁻¹(u₁⁻¹ − u₂⁻¹); real parts of the difference each carry π and
  cancel; imaginary parts are the certified shift-difference log-limit piece.  Together
  with `integral_sq_rightKernel_inv` (β₁ = β₂) the same-side calculus is COMPLETE: every
  same-side second-order product integrates to zero.
- **`integral_mul_lorentzianHalves`** — cross-Lorentzian mass 2πx/(4x²+(β₁−β₂)²), one
  formula for both the confluent (β₁=β₂, = π/(2x)) and separated cases.  All mass flows
  through the anti-causal/causal pairing (the certified master cross-kernel).
- **`integral_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge`** — the sharp deposit:
  ∫(Re pair)² dt = 4π(1/x + x/(x²+b²)) EXACTLY, x = Re λ + ½, b = Im λ.
- **`integral_sq_re_eq_half_integral_normSq_xiPairEdge`** — EDGE EQUIPARTITION: the real
  channel carries exactly half the pair's modulus-squared deposit; Re and Im split 50/50.

Reading the sharp formula: 4π(1/x + x/(x²+b²)) ranges over (4π, 8π); → 8π iff x → 1 AND
b → 0, i.e. iff the zero approaches the EULER POINT s = 1 (not the critical line! a → ½
means ρ = ½+a+ib → 1+ib, then b → 0).  A near-Euler zero maximizes real-channel edge
energy; a deep zero near the critical line (a → 0) gives x → ½: deposit → 4π(2 + ...)
≥ 8π when b² ≤ ... check: x = ½: 4π(2 + (½)/(¼+b²)) > 8π ALWAYS.  Recompute: 1/x = 2 at
a = 0 — the deposit 4π(1/x + x/(x²+b²)) > 4π·1/x → 8π as a → 0 for ANY b.  So BOTH
near-critical (a→0) and near-Euler (a→½, b→0) pairs deposit ≈ 8π in the real channel;
minimum over the strip is strictly above 4π·(1/x) ≥ 4π·1 — worst case a → ½, b → ∞
gives ↓ 4π.  The Re-channel counting law upgrade is therefore: each pair deposits
4π(1/x_q + x_q/(x_q²+b_q²)) — graded by position, exceeding the flat 4π everywhere.

What this OPENS: (1) upgrade `card_nsmul_le_xiWardEdgeQuadEnergy` to the GRADED counting
law Σ_q 4π(1/x_q + x_q/(x_q²+b_q²)) ≤ energy — a Weil-type explicit-formula inequality
for the edge functional (each zero weighted by its position); (2) the equipartition
suggests the Im-channel identity ∫(Im pair)² = same value — then the FULL normSq per-pair
double-counted split may give an 8π-window law on the Re+Im diagonal against SINGLE pairs:
∫(Re r)² + ∫(Im r)² = ∫normSq r ≥ pair-normSq-deposit > 8π for one pair IF cross-pair
normSq terms were controllable — they are NOT pointwise, but ∫(Im r)² ≥ ... the Im parts
are NOT one-signed, so superadditivity fails there; the Re channel remains the honest
counting channel.  (3) The near-Euler blow-up (deposit → 8π at ρ → 1) is a NEW spectral
statement: the edge functional weights the Euler point as heavily as the critical line —
collide this with the Euler-locality kill (step 8): the diagonal chart was divisor-blind,
but the EDGE functional is Euler-point-sensitive.  The pair (edge functional, diagonal
chart) sees (Euler point, nothing) — a complementarity worth a fake-proof round.

## Step 9m — graded counting law and the TSUM LAYER, Fubini-free [PROVED HERE]

Appended to `XiWardEdgeReChannelDeposit.lean` (compiles clean, standard axioms, index
regenerated):
- `integrable_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge`.
- `sum_sq_re_xiAntiCausalWardSchwarzPairResponse_le_normSq` — Σ_F (Re pair)² ≤ normSq r
  pointwise (Cauchy diagonal + Herglotz subsum + normSq ≥ re²).
- **`sum_sharp_le_xiWardEdgeQuadEnergy`** — graded finite counting law: every finite
  family deposits Σ_F 4π(1/x_q + x_q/(x_q²+b_q²)) into the energy.
- **`tsum_sharp_le_xiWardEdgeQuadEnergy`** — THE TSUM LAYER: the FULL series over the
  entire strict-right divisor Σ′_q ofReal(4π(1/x_q + x_q/(x_q²+b_q²))) ≤ energy.  In
  ℝ≥0∞ the tsum IS the iSup of finite partial sums, so the layer that blocked the
  8π-sharp route (double-series Fubini for infinite divisors, step 9f) NEVER APPEARS.
  The inequality direction costs nothing; only the equality direction needed Fubini.

This is a machine-checked one-sided EXPLICIT FORMULA for the edge functional: a
Weil-flavored positivity statement pairing the full off-critical divisor (each zero
weighted by its position-graded deposit 4π(1/x + x/(x²+b²)) ∈ (4π, 8π]) against a single
integrated capacity.  RH ⟺ both sides vanish (the 4π closed law).  ¬RH ⟹ the left side
counts every violation with weight > 4π.

What this OPENS: the missing half of the explicit formula is the upper bound
(energy ≤ tsum of deposits + cross-pair energy) — the cross-pair Re-products
∫(Re p)(Re p′) are POSITIVE cross-kernel masses 2π-computable pairwise from
`integral_mul_lorentzianHalves` (four cross-Lorentzians per pair-pair).  The full
∫(Re r)² would then be the complete double series — the Fubini gate returns ONLY for the
equality, but now with all terms positive: TONELLI (lintegral_tsum, no integrability
side-conditions in ℝ≥0∞) may close the equality where Fubini could not.  Next move:
∫⁻ (Re r)² as an ℝ≥0∞ double series via lintegral_tsum over the countable divisor —
if it closes, the Re-channel edge energy is EXACTLY the double series
Σ_{q,q′} 4·2πx̄/(4x̄²+…) and the 8π-window question becomes a pure lattice-sum estimate.

## Step 9n — two-width same-side calculus, general cross-Lorentzian mass [PROVED HERE]

Appended to `XiWardEdgeReChannelDeposit.lean` (compiles clean, standard axioms):
- `integrable_sameSideKernelMul_general`, **`integral_sameSideKernelMul_general_zero`** —
  ∫ (x₁+i(t+β₁))⁻¹(x₂+i(t+β₂))⁻¹ dt = 0 whenever (x₁,β₁) ≠ (x₂,β₂) as a complex
  constant (partial fraction by the constant kernel difference; Re: π−π; Im: certified
  shift-difference + width-difference odd pieces).  With `integral_sq_rightKernel_inv`
  the same-side second-order calculus is closed under ALL width/shift combinations.
- `integral_re_edgeCrossKernel_general` — Re ∫ cross-kernel = 2π(x₁+x₂)/((x₁+x₂)²+(β₁−β₂)²).
- **`integral_mul_lorentzianHalves_general`** — the general two-width cross-Lorentzian
  mass π(x₁+x₂)/((x₁+x₂)²+(β₁−β₂)²), one closed formula for all cases (the Lorentzian
  convolution semigroup law, derived spectrally with zero convolution theory).

This completes the FULL bilinear edge calculus: every product of two Lorentzian halves —
any widths, any shifts — now has a certified closed-form mass.  Ingredient list for the
Tonelli lattice sum (Batch B, next): pair-pair Re-deposit = 4-term M-sum, then
∫⁻(Re r)² = Σ′_{q,q′} (4-term M-sum) via ENNReal Tonelli (lintegral_tsum) — no Fubini
side conditions.  The Re-channel edge energy becomes an explicit positive lattice sum
over ordered pairs of strict-right zeros: a complete quadratic explicit formula.

## Step 9o — THE QUADRATIC EXPLICIT FORMULA, real channel [PROVED HERE]

Appended to `XiWardEdgeReChannelDeposit.lean` (1036 lines; compiles clean; standard
axioms; index regenerated):
- countability block (private divisor countability + local instances, mass-module pattern).
- `ennreal_tsum_mul_tsum` — ℝ≥0∞ series product distributes over the product index
  (tsum_prod' + tsum_mul_left/right; no summability hypotheses).
- `integrable_mul_re_xiPairs`, **`integral_mul_re_xiPairs`** — the pair-pair Re deposit in
  closed form: 8π(x+x′)[1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²)].
- **`lintegral_sq_re_continuedXiAntiCausalWardResponse_eq_tsum`** — the QUADRATIC EXPLICIT
  FORMULA: ∫⁻ (Re r(½+it))² dt = Σ′_{(q,q′)} ofReal(8π(x_q+x_{q′})[…]) over ALL ordered
  pairs of strict-right zeros.  EQUALITY, unconditional.  The pointwise square of the
  Herglotz tsum expands through `ennreal_tsum_mul_tsum`; Tonelli (`lintegral_tsum`)
  interchanges with no side conditions.  The Fubini gate that killed the 8π-sharp route
  is fully bypassed: ℝ≥0∞ Tonelli is the mechanism the CCM literature left unresolved
  ("infinite source convergence") — in the edge-L² representation it is simply free.
- `lintegral_sq_re_le_xiWardEdgeQuadEnergy`, `tsum_pairPair_le_xiWardEdgeQuadEnergy` —
  the lattice sum sits under the full edge energy.

Structural readout: the Re-channel edge energy is a POSITIVE DEFINITE lattice sum — the
Gram matrix of the family {Re pair_q} in L²(ℝ) with explicit entries
G(q,q′) = 8π(x+x′)[…] > 0.  RH ⟺ this Gram family is empty.  ¬RH ⟹ the energy is the
full quadratic form value at the all-ones vector — and every entry is positive, so the
form value ≥ Σ diagonal = Σ_q 4π(1/x_q + x_q/(x_q²+b_q²)) (recovering 9m) PLUS the
off-diagonal mass Σ_{q≠q′} G(q,q′) — the first certified quantitative use of cross-pair
attraction (all deposits reinforce; no screening/cancellation is possible in this channel).

What this OPENS: (1) the Gram-matrix view invites the FINITE-RANK collision (card 9j/9k
finiteness law + FiniteModalHankelRank): for a finite divisor the energy is a finite
positive-definite quadratic form with EXPLICIT entries — eigenvalue bounds are linear
algebra; (2) the diagonal-vs-total comparison G(q,q) vs Σ_{q′} G(q,q′) measures zero
clustering — a certified route toward zero-repulsion statements (pair correlation from
the edge functional); (3) same machinery for the Im channel: Im pair is ODD in a sign
pattern — its lattice sum has SIGNED cross terms (the screening channel) — computing it
would give the exact normSq lattice sum = Re-sum + Im-sum and the full ∫normSq r as an
explicit double series, closing the 8π equality question by lattice arithmetic.

## Step 9p — imaginary channel, pairwise equipartition, THE PAIR GRAM MATRIX [PROVED HERE]

New module `formal/GaloisForLFunctions/RHTower/XiWardEdgeImChannelGram.lean` (compiles
clean, standard axioms, umbrella wired, index regenerated).  rng pick chose
im-channel-lattice over finite-rank-gram / zero-repulsion / fake-proof-audit / wild.

- `integrable_sq_oddKernel`, `integrable_mul_oddKernels_general` (AM–GM domination).
- **`integral_mul_oddKernels_general`** — the odd-kernel cross mass EQUALS the Lorentzian
  one: ∫ O₁O₂ = π(x₁+x₂)/((x₁+x₂)²+(β₁−β₂)²).  Same mechanism: same-side products
  vanish, all mass through the causal/anti-causal pairing — now for the ODD parts.
- `im_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq` — Im pair = −2O(b) − 2O(−b).
- **`integral_mul_im_xiPairs`** — pair-pair imaginary deposit, closed form identical to
  the real channel.
- **`integral_mul_im_eq_integral_mul_re_xiPairs`** — PAIRWISE CHANNEL EQUIPARTITION:
  ∫(Im p)(Im p′) = ∫(Re p)(Re p′) for EVERY ordered pair (q,q′), not only diagonally.
  The screening channel does not screen: the imaginary parts reinforce exactly as much
  as the real parts.  (Desk expectation of "signed cross terms" in step 9o was WRONG —
  the odd-kernel masses are positive too.  Recorded as a self-correction.)
- **`integral_inner_xiPairs`** — THE PAIR GRAM MATRIX: real L² inner products
  G(q,q′) = 16π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²)) > 0.

Consequence unlocked: normSq r = (Re r)² + (Im r)² pointwise, both channels have
IDENTICAL positive lattice sums, so the FULL edge energy satisfies
xiWardEdgeQuadEnergy = 2·Σ′_{(q,q′)} ofReal(8π(x+x′)[…]) — provided the Im-channel
Tonelli expansion also holds.  The Re-channel proof (9o) used positivity of Re pair
pointwise; Im pair is NOT pointwise one-signed, so the ℝ≥0∞ product expansion of
(Σ Im pair)² needs the signed Cauchy-product route (absolute summability from hsum) —
this is the ONE remaining lemma between here and the exact identity
   xiWardEdgeQuadEnergy = Σ′ ofReal(16π(x+x′)[…])  [the FULL quadratic explicit formula].
With it, the closed 4π law + dichotomy + counting all become statements about an explicit
positive bilinear lattice form: W_P positivity ⟺ this lattice form has no support.

Next unit: the signed expansion ∫⁻ ofReal((Im r)²) = Σ′ pair-pair Im deposits.  Route:
(Im r)² = (Σ′ Im pair)² with Σ′ absolutely convergent (Summable.abs from hsum); write
(Σ′ a)² = Σ′_{prod} a_q a_{q′} in ℝ (Cauchy product, tsum_mul_tsum_of_summable_norm);
then ofReal + lintegral of the SIGNED double series: split each a_q a_{q′} into positive
part bound |a_q||a_{q′}|, dominate by the |O|-lattice (all masses computed), use
dominated convergence / integrable tsum machinery (MeasureTheory.integrable_tsum?) for
the Bochner-side interchange instead of lintegral_tsum.  The domination budget is finite
per finite family but the FULL |O|-series needs Σ′ ∫|O_q O_q′|-type bounds — carded as
the open ingredient: absolute lattice summability ⟺ finite energy (consistent with the
finiteness law: infinite divisor → infinite energy → nothing to prove there; finite
divisor → finite sums → interchange trivial by finiteness!).  CASE SPLIT KILLS IT: the
signed interchange is only needed when the divisor is FINITE (else both sides are ⊤ or
the law is vacuous) — and for finite divisors tsum = finite sum and every interchange is
`integral_finsetSum`.  The full quadratic explicit formula may thus be provable by the
finite/infinite dichotomy WITHOUT any new convergence lemma.  That is the next theorem.

## Step 9q — THE FULL QUADRATIC EXPLICIT FORMULA and RH as lattice arithmetic [PROVED HERE]

Capstone appended to `XiWardEdgeImChannelGram.lean` (646 lines; compiles clean; standard
axioms propext/Classical.choice/Quot.sound; umbrella wired; index regenerated):

- `xiPairGramTerm (q q′)` = 16π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²)) with
  nonneg + `eightPi_le_xiPairGramTerm_diag` (every diagonal entry > 8π).
- **`xiWardEdgeQuadEnergy_eq_tsum_gram`** — the FULL quadratic explicit formula:
      xiWardEdgeQuadEnergy = Σ′_{(q,q′) ∈ X×X} ofReal(G(q,q′))
  UNCONDITIONAL EQUALITY.  Proof by the finite/infinite dichotomy: infinite divisor →
  both sides ⊤ (finiteness law + diagonal 8π-floor + injective diagonal comparison +
  constant-series divergence); finite divisor → every interchange is `integral_finsetSum`
  and the pointwise expansion is Finset algebra (`Finset.sum_mul_sum` on re/im parts).
  NO convergence lemma, NO Fubini, NO Tonelli was needed at the capstone level — the
  dichotomy killed the last analytic gate, exactly as predicted at 9p.
- **`riemannHypothesis_iff_tsum_gram_le`** — RH AS LATTICE ARITHMETIC: for any budget
  0 ≤ c ≤ 4π,
      RH  ⟺  Σ′_{(q,q′)} ofReal(G(q,q′)) ≤ ofReal(c).
  Combined with the corpus chain (W_P ⪰ 0 ⟺ RH), Ward positivity is now certified
  equivalent to a single inequality about an explicit positive lattice sum over ordered
  pairs of would-be off-critical zeros.  The analytic content is fully discharged; what
  remains of RH in this representation is: "the Gram lattice of the strict-right divisor
  cannot fit under 4π" — which holds vacuously iff the divisor is empty, since one
  diagonal term already spends 8π.

The 9-step edge-L² programme (9i–9q) is complete as a certified reduction stack:
  W_P ⪰ 0 ⟺ RH ⟺ energy ≤ c (c ≤ 4π, closed) ⟺ Gram lattice sum ≤ c;
  energy ∈ {0} ∪ (4π, ∞]; energy counts pairs (≥ N·4π, graded, margin-sharpened);
  finite energy ⟹ finite divisor; per-pair and pair-pair deposits all in closed form;
  channels equipartition pairwise.

What this OPENS (next generative moves): (1) the lattice form is a POSITIVE-DEFINITE
kernel on the half-strip 0 < a < ½, b > 0 — study G as a reproducing kernel: which
measures μ on the strip satisfy ∬ G dμdμ ≤ 4π?  Only μ = 0 among counting measures of
conjugate-closed divisors — but among ALL positive measures the constraint region is a
CONVEX BODY; RH says the divisor's counting measure lies in it, i.e. AT ITS UNIQUE
EXTREME POINT 0.  Attack: show the only atomic measures in the body with atoms ≥ 1 are
empty — pure convex geometry on an explicit kernel.  (2) Collide with A† Chart–Region
Exchange: the Gram kernel's diagonal blow-up 8π/x as x→0 is the zero-free-region wall
in lattice form — feed the B† Legendre pairing through the lattice representation.
(3) The Hankel/Vandermonde mode-count corpus (FiniteModalHankelRank) applies verbatim to
the finite-divisor branch: a finite Gram matrix with distinct nodes is NONSINGULAR —
quantitative lower bounds on its smallest eigenvalue would grade the 8π-floor into a
spectral gap for the whole family, not just singletons.

## Step 9r — THE SHARP 8π LAWS: the 9f blockade falls [PROVED HERE]

New module `formal/GaloisForLFunctions/RHTower/XiWardEdgeGramSharpLaws.lean` (compiles
clean, standard axioms, umbrella wired, index regenerated).  rng picked legendre-lattice;
the desk pass discovered that the Gram capstone's diagonal already carries the FULL
per-pair deposit — so every 4π law doubles, and the 8π-sharp window that step 9f recorded
as BLOCKED (double-series Fubini) is now certified:

- `gramTerm_le_xiWardEdgeQuadEnergy` — every ordered pair's Gram term ≤ energy
  (one `ENNReal.le_tsum` on the capstone; the lattice representation makes the full
  deposit a single series term, so no interchange is ever needed).
- `eightPi_div_le_xiPairGramTerm_diag` — G(q,q) ≥ 8π/x.
- **`riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw_sharp`** — THE SHARP LAW:
  RH ⟺ energy ≤ c for ANY fixed 0 ≤ c ≤ 8π (closed endpoint).  The budget window
  doubles from [0, 4π] to [0, 8π]; sharp relative to the per-pair deposit, which
  approaches 8π as a → ½, b → ∞.
- **`xiWardEdgeQuadEnergy_eq_zero_or_eightPi_lt`** — the spectral gap widens: energy is
  0 or > 8π; (0, 8π] is forbidden.
- **`card_nsmul_eightPi_le_xiWardEdgeQuadEnergy`** — counting law doubles: N·8π.
- **`height_lt_abs_im_of_xiWardEdgeQuadEnergyLaw_le_eightPi`** (name in file:
  `height_lt_abs_im_of_xiWardEdgeQuadEnergy_le_eightPi`) — window clearing at doubled
  budget 8π(1+m(T)).

Method note (for the meta-card): the mechanism that killed the 9f blockade was NOT a new
convergence theorem — it was a REPRESENTATION CHANGE.  In the direct route the sharp
deposit is a sum of infinitely many cross terms (Fubini needed); in the lattice
representation the same quantity is ONE TERM of a positive series (le_tsum suffices).
The obstruction was an artifact of the coordinate system, exactly the A† chart-exchange
moral transposed to series representations.

What this OPENS: (1) the window cannot extend past 8π on the pure budget axis (deposit
infimum is 8π over the strip closure) — the next tightening must be RELATIVE: subtract
the certified deposit of each detected pair and re-run the law on the residual — an
iterative peeling law (energy − Σ_detected G ≤ c ⟺ no further pairs), i.e. a certified
zero-counting ALGORITHM specification; (2) cluster repulsion: for two pairs the floor is
G(q,q) + G(q',q') + 2G(q,q') > 16π + 2G(q,q') — formalize the two-pair law with the
explicit cross bonus (first use of off-diagonal mass); (3) B†-Legendre reading: the
doubled clearing law says budget slack 8π·m(T) buys height T with the same 9-exponent —
the exchange rate is representation-invariant, as B† predicts; carding the desk note.

## Step 9s — two-pair cross-bonus laws [PROVED HERE] + HOSTILE NOVELTY AUDIT of 9i–9r

Certified this round (XiWardEdgeGramSharpLaws.lean, compiles clean, standard axioms):
- `xiPairGramTerm_symm`; **`twoPair_gram_floor_le_xiWardEdgeQuadEnergy`** — two distinct
  pairs force energy ≥ G(q,q) + G(q′,q′) + 2G(q,q′) (first certified use of off-diagonal
  Gram mass); **`cluster_penalty_lt_xiWardEdgeQuadEnergy`** — height-clustered distinct
  pairs (|b−b′| ≤ δ) force energy > 16π + 32π/(4+δ²): a certified pair-repulsion
  penalty (clustered violations are MORE expensive than separated ones).

### Novelty audit (user-triggered; gate: "would a literature search produce this?")

RECLASSIFIED AS FORMALIZATION-OF-CLASSICAL (search would produce the mathematics,
though no formal library has it):
- All kernel integrals of 9i–9n (∫u⁻² = 0, Lorentzian/odd-kernel masses, cross
  convolution semigroup): classical residue/Poisson computations.
- The Gram matrix of Cauchy–Poisson kernels attached to points of a half-plane
  (9o–9q): standard reproducing-kernel/model-space material (Szegő kernels, de
  Branges–Clark theory).  The "quadratic explicit formula" is the Gram expansion of a
  countable kernel family — classical in substance, new only as a certified artifact
  wired to THIS corpus divisor object.
- Channel equipartition (9p): conjugate-function symmetry, M. Riesz territory.
- "RH ⟺ positive divisor functional ≤ budget": logically the quantitative dressing of
  "RH ⟺ no off-critical zero"; the classical incarnations are Weil positivity and Li
  coefficients.  The 4π/8π constants and window/counting/margin laws are corpus-specific
  quantitative content, but the SHAPE is known.

WHAT REMAINS GENUINELY CORPUS-NEW: the certified equivalence of these functionals with
the Ward matrix W_P through the corpus chain, the Lean stack itself (no formal analogue
exists anywhere), and the margin-graded laws tied to the corpus zero-free margin.

### The structural confession the audit forces

Every theorem in 9i–9r strengthens the LOWER bound on the edge energy under ¬RH — the
EASY direction of every RH criterion.  The open core is the UPPER bound (energy ≤ 8π,
i.e. actual emptiness of the divisor).  The corpus's own obstruction theorem B†
(Legendre neutrality: norm-type loops are exactly neutral) applies VERBATIM to the edge
stack: it is a norm loop, and no amount of further sharpening inside it can produce the
upper bound.  Continuing to polish this stack would be exactly the theatre the user
warns against.  The stack's real value: a clean, certified, quantitative TARGET surface
(the constraint side of the constraint-metaphor: the object is fixed by "energy ≤ 8π",
not grown by a flow).

### Reorientation (the next real problem)

The upper bound must come from an input that is NOT the divisor: prime-side/arithmetic
supply.  A† (Chart–Region Exchange) certifies: cocycle supply ⟺ zero-free region.  The
missing object is a certified bridge  "prime-side supply S ⟹ xiWardEdgeQuadEnergy ≤
F(S)"  — an arithmetic upper-bound mechanism for the edge functional.  Next round:
(1) FAKE-PROOF FIRST — write the fake proof of the upper bound through the Perron/PNT
corpus modules, find the exact failing step, name it (the B†-predicted neutrality point
must appear concretely); (2) inventory the corpus's certified upper-bound machinery
(det₂ contraction, Hardy contraction, aperture bounds) against the edge functional —
each no-go names a channel; the audit of which upper-bound channel is NOT yet closed by
a no-go is the actual open map.  This is where the next session's mathematics lives.

## Step 9t — FAKE PROOF of the upper bound, run to its failing step [SEARCH register]

Target to fake-prove: xiWardEdgeQuadEnergy ≤ c (any finite c would already kill the
infinite-divisor channel; c ≤ 8π would be RH).

FAKE PROOF (prime-side transport):
1. energy = ∫ |r(½+it)|² dt.                                        [certified, 9o–9q]
2. r(σ+it) → r(½+it) as σ → ½⁺ (boundary values).                    [plausible]
3. [CONJECTURE] On Re w > 1 the Ward response has a prime-side representation
   r = D + (Γ-corrections), D an absolutely convergent von-Mangoldt Dirichlet series
   (the "prime first trace").
4. [FAKE JUMP] Parseval/Montgomery–Vaughan for D on vertical lines gives
   ∫|D(σ+it)|²dt ≍ Σ Λ(n)²n^{−2σ−1} < ∞ uniformly down to σ = ½ + ε; pass the bound
   through step 2 by "continuity of L² under the limit".

WHERE IT DIES — three concrete failures, in order of depth:
(a) The Euler pole: any prime-side object carrying ζ'/ζ has the s = 1 pole on its
    boundary line; after pole subtraction |ζ'/ζ(1+it)| still grows (≍ log²|t| bounds),
    so the FULL prime trace is not L² on ANY vertical line.  Step 4's finiteness is
    false for the full trace.
(b) The subtraction defect [THE NAMED OBSTRUCTION]: r is not the full trace; it is
    (full prime trace) − (critical-line spectral trace) — the anti-causal DEFECT.  Both
    subtrahends are individually non-L² on the edge (each ≍ log-density growth); the
    energy is their ∞−∞ cancellation.  A norm bound on either side says NOTHING about
    the difference: certifying the cancellation requires PHASE alignment between the
    prime trace and the critical-line spectrum — exactly the corpus's
    complementary-phase no-go (unitary full phase ⟹ strict-right contraction forces
    complementary expansion) in L² clothing.  Step 3's D does not exist as an
    AUTONOMOUS object: writing it requires already knowing the spectrum (circularity).
(c) B† neutrality, concretely: transporting an L² bound from Re = 1+ε to Re = ½ costs
    the strip-crossing factor that a norm loop prices exactly at the zero-free-region
    exchange rate — the transported bound degrades to precisely vacuous at the edge.

WHAT SURVIVES THE AUTOPSY (the generative residue):
The failure is localized in the SUBTRACTION, not in the prime side per se.  Between raw
subtraction (not norm-accessible) and det₂ renormalization (kills the signal — corpus
no-go), there is an unexplored regularization axis: subtract a CERTIFIED PARTIAL
spectral trace (finitely many critical-line zeros / a smoothed spectral density) rather
than the full one.  The defect of a PARTIAL subtraction is norm-accessible (finite
modification), and the corpus's edge calculus computes exactly how much energy a partial
subtraction removes (the Gram machinery applies verbatim to critical-line kernels
x → 0⁺ limits — Lorentzian halves degenerate to Dirac masses; the edge calculus has the
closed forms).  Sub-question carded: compute the Gram matrix of CRITICAL-LINE kernels
(x = σ − ½ → 0 regularized) against strict-right kernels — the mixed Gram G(critical,
right) is finite for σ > ½ and its σ → ½ behavior measures the phase alignment that (b)
says is the obstruction.  If the mixed Gram stays bounded while the diagonal blows up,
the defect subtraction is quantifiably SMALL — a norm-accessible fragment of the phase
information.  That computation is new (not classical-search-reachable in this form) and
certifiable with the existing two-width calculus (widths x₁ → 0, x₂ fixed — the
`integral_mul_lorentzianHalves_general` formula already covers it: mass
π(x₁+x₂)/((x₁+x₂)²+(β₁−β₂)²) → πx₂/(x₂²+Δβ²) as x₁ → 0: FINITE).  The two-scale/moiré
idea of this card's title returns as the σ-regularized mixed Gram.

## Step 9u — critical-collapse decoupling [PROVED HERE]

New module `formal/GaloisForLFunctions/RHTower/XiWardEdgeCriticalCollapseGram.lean`
(compiles clean, standard axioms, umbrella wired, index regenerated).  Instantiates the
surviving object of the 9t autopsy:
- **`integral_mul_lorentzianHalves_le`** — uniform cross bound: ∫ L_{x₁,β₁}L_{x₂,β₂}
  ≤ π/x₂ for ALL widths x₁ > 0 and ALL heights.  The mixed Gram between a collapsing
  (near-critical) kernel and any fixed strict-right kernel is uniformly bounded.
- **`tendsto_integral_sq_lorentzianHalf_atTop`** — self-energy divergence: ∫ L_x² → ∞
  as x → 0⁺.
Together: the two-scale moiré decoupling.  Partial spectral subtraction (removing
near-critical kernels) perturbs each cross channel by ≤ π/x₂ even as the removed
self-energies diverge — the norm-accessible fragment of the phase information named in
9t(b).  Novelty-gate label: the two lemmas are classical-calculus facts; the corpus-new
content is their ROLE as the certified decoupling interface for partial subtraction
against the Ward defect.  Next: await the upper-bound-machinery inventory (agent), then
design the partial-subtraction object r_S (response minus S-indexed near-critical
family) and compute its energy shift with these bounds.

## Step 9v — upper-bound channel inventory (agent report) + the quantization-vs-estimate synthesis [SEARCH register]

Inventory (read-only agent over the corpus; full report in session log) — certified
UPPER-bound channels still alive: (1) Cayley/Ward phase contraction ‖phase‖ ≤ 1 and
transport ‖V‖ ≤ 2, unconditional, geometric (HardyContraction); (2) Hardy–Pick four-unit
nonexpansive defect PSD (HardyNonexpansive); (3) det₂ prime-side remainders (≤ 144/p²,
≤ log p/p²); (4) Perron/PNT error bounds conditional on a zero-free margin; (5) prime
window supply.  Killed: complex-aperture Schur–Pick promotion (only the real α-ray is
contractive); every closable rigging of the prime first-trace clock; and — decisively —
NO unconditional constant upper bound on the Ward edge energy exists in the corpus: the
only such bounds are certified RH-EQUIVALENT.

Desk pass over the alive channels (this session):
- The aperture ray: ∂_α V(w,·)|₀ = r(w) is certified (hasDerivAt_..._zero), ‖V‖ ≤ 2 on
  the ray — but a ray has no Schwarz lemma; difference quotients give only 4/α.  Sector
  continuation reopens it ONLY IF the product is bounded on a sector — and the log-sum
  splits into divergent positive/negative parts (Σ 1/γ diverges): the ∞−∞ subtraction
  defect (9t-b) reappears verbatim in the aperture sector.
- Harnack in the spectral variable (Poisson-kernel ratio P(½,u) ≤ 4P(2,u)) transports
  Re r between abscissas unconditionally — and transports the problem with it (B†).
- Littlewood–Paley/Carleson from ‖phase‖ ≤ 1 bounds |phase′|²·(bulk weight) — which
  controls |phase|²|r|², degenerating exactly where ¬RH lives (|phase| < 1).  Neutral.

SYNTHESIS [CONJECTURE-LEVEL PROGRAM, novelty-gate-checked]: the certified spectral gap
(energy ∈ {0} ∪ (8π, ∞]) changes what kind of statement is needed.  Estimates cannot
cross a gap; but the gap converts ANY sub-8π bound into exact vanishing.  So the open
core is not "prove energy ≤ 8π by analysis" (B†-neutral norm loop, confirmed dead
across four channel families) but: **produce a certified prime-side EXACT IDENTITY for
the single number xiWardEdgeQuadEnergy** — a second evaluation of the same quantity by
arithmetic/theta objects (the corpus's Λ = Γ·ζ weld, XiThetaPositiveL2Perron exact
pieces).  Given identity + ANY crude certified arithmetic bound < 8π on that side, the
gap forces energy = 0 = RH = W_P ⪰ 0.  Quantization converts estimates into vanishing:
the 8π-wide gap is the mechanism that makes a NON-sharp prime estimate sufficient — the
first structural reason this program differs from the classical norm-loop dead ends.
The subtraction defect localizes to constructing the identity for ONE number (a
regularized pairing), not for the response as a function — a strictly weaker demand
than the autonomous prime representation that 9t killed.

NEXT (queued): desk-construct the candidate identity: energy = ∫|r|² edge pairing; r =
∂_α V; V built from Γ-sewn Cayley products of the Λ-weld — expand ∫|∂_α V|² through the
weld's theta representation (Parseval on the Mellin/Fourier side where the corpus holds
exact theta identities); identify which regularization of the prime double sum appears;
check each step against the certified no-gos BEFORE any Lean.  (The σ-family/Harnack rng
pick was folded into this design as the abscissa-transport sub-lemma.)

## Step 9w — Weil-pairing desk check + certified Harnack abscissa transport [mixed]

Desk (SEARCH register): the 9v identity program was pushed through the Weil-pairing
route: pairing the windowed energy against the explicit formula with autocorrelation
test functions, discarding the on-line spectral mass by positivity, leaves
off-line ≤ arithmetic side EXACTLY — but the arithmetic side for a height-T window
carries the oscillatory Λ-sum at frequency T, whose cancellation is the PNT-error at
that frequency: the B† neutrality point appears as predicted, now LOCATED in the
identity program (it lives in the window-position dependence of the finite Λ-sum, not
in the identity itself).  Consequence: the identity program is viable exactly to the
extent that ONE fixed window near height 0 suffices — a fixed low window needs only a
FIXED finite Λ-sum bound (no oscillation estimates).  A fixed window can only clear a
fixed height range — full RH would need the ladder, which pays B† at each rung.  The
un-neutralized residue: a certified LOW-HEIGHT window clearing from a fixed finite
arithmetic sum — worth pursuing as a new-TYPE partial result (arithmetic input, exact,
no numerics beyond a finite provable sum), even though it cannot ladder to full RH
without new input.  Queued as the 9x target.

Lean [PROVED HERE] (XiWardEdgeCriticalCollapseGram.lean, compiles clean, standard
axioms, indexed): `lorentzianHalf_le_four_mul`;
`re_xiAntiCausalWardSchwarzPairResponse_line_eq` (general-abscissa Re formula — first
off-edge evaluation lemma in the stack); **`re_continuedXiAntiCausalWardResponse_edge_le_four_mul_interior`**
— unconditional pointwise Harnack transport Re r(½+it) ≤ 4·Re r(2+it): the critical
edge is dominated by the interior line where the pair series converges absolutely with
quadratic decay.  Novelty label: Harnack is classical; the certified transport is the
first corpus bridge between the RH-critical edge and the absolutely-summable region —
the interface any exact-identity program will pair against.

## Step 9x — the Poisson-window interior program, grounded + FIRST BRICK CERTIFIED

Design pivot (from 9w): replace compact Fourier windows by POISSON windows.  The
certified general cross-Lorentzian mass IS the Poisson semigroup, so the windowed edge
mass of Re r equals an interior point value π·Re r(s₀) — and at interior points every
spectral sum converges ABSOLUTELY: the full/on-line/off-line split is finite arithmetic
of convergent series, the ∞−∞ subtraction defect never forms.  Discard chain at
interior s₀:  windowed edge mass = π Re r(s₀) ≤ π Re(full trace + corrections)(s₀) =
arithmetic side (ζ′/ζ absolutely convergent + certified Γ/pole terms).  Combined with a
windowed per-pair quantum: arithmetic side < quantum ⟹ window CLEARED of off-critical
zeros.  Fixed low window: fixed finite arithmetic bound, no oscillation estimates —
B†-neutrality does not bite for a fixed window (it prices only the T→∞ ladder).

Corpus assets discovered (search): the Hadamard stack is ALREADY CERTIFIED —
`XiHadamardFactorization.lean` (canonical product, quotient nonvanishing,
`xiHadamardQuotient_mul_canonicalProduct = XiC`), `XiRelativeResolventTrace.lean`
(`logDeriv_xiCanonicalProduct_eq_relativeResolventTrace`: full-divisor absolutely
summable trace identity), transport module (`xiCanonicalProduct_eq_right_mul_nonright`
Wiener–Hopf split; `logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace`).

[PROVED HERE] First brick, new module
`formal/GaloisForLFunctions/RHTower/XiWardInteriorTraceSplit.lean` (compiled clean on
first attempt; standard axioms; umbrella wired; indexed):
**`xiRelativeResolventTrace_eq_right_add_logDeriv_nonright`** — away from the Xi
divisor, fullTrace(z) = rightTrace(z) + logDeriv(nonright factor)(z) EXACTLY.  The
subtraction-defect skeleton is now a certified identity among three absolutely
convergent objects.  Remaining bricks, in order: (1) connect
xiRightRelativeResolventTrace to the Ward response r at interior points (the corpus's
centered response = right trace modulo certified centering constants — locate/derive);
(2) Re-positivity discard for the nonright factor's on-line part at interior points
(Schwarz/mirror bookkeeping of the E1-centering corrections); (3) arithmetic side:
logDeriv XiC ↔ ζ′/ζ + Γ + pole via the corpus weld, with Perron-module bounds; (4) the
windowed quantum from the Poisson mass and the clearing inequality.

## Step 9y — bricks 1 and 3a of the interior program CERTIFIED

Appended to `XiWardInteriorTraceSplit.lean` (all compiled clean on first attempts;
standard axioms; built; indexed):
- **`continuedXiAntiCausalWardResponse_eq_full_sub_nonright`** (brick 1) — the Ward
  response equals 2i·fullTrace(iw) − 2i·logDeriv(nonright)(iw) + boundarySymbol away
  from the rotated divisor.  The bridge response ↔ right trace was DEFINITIONAL in the
  corpus (`continuedXiCenteredAntiCausalWardResponse := 2i·rightTrace(i·w)`); composing
  with the 9x trace split gives the response's exact interior decomposition.
- **`logDeriv_XiC_eq_quotient_add_trace`** (brick 3a) — logDeriv XiC = logDeriv
  (entire Hadamard factor) + fullTrace.
- **`continuedXiAntiCausalWardResponse_eq_logDeriv_XiC_sub`** — MASTER INTERIOR
  IDENTITY: r(w) = 2i·logDeriv XiC(iw) − 2i·logDeriv quotient(iw) −
  2i·logDeriv nonright(iw) + boundarySymbol.  The Ward response is now certified as an
  exact expression in the completed source XiC — the weld object — with every term
  absolutely convergent at interior points.  The subtraction defect is fully
  skeletonized: what remains of it is the single term logDeriv(nonright), the
  on-line + left factor.

Remaining bricks: (3b) logDeriv XiC(i·w) ↔ ζ′/ζ + Γ + pole through the corpus weld and
the functional equation (note the rotation lands at ½ − w; the functional equation
reflects to ½ + w where the Λ-series converges absolutely for Re w > ½); (2) the
Re-discard for logDeriv(nonright) at interior points (Schwarz/mirror bookkeeping —
CAUTION: sign analysis in 9x notes shows the E1-centering corrections obstruct naive
per-term positivity; the discard likely needs the left/on splitting with mirror-pair
combination first); (4) windowed quantum + clearing inequality.

## Step 9z — brick 3b head: the ARITHMETIC-HEADED master identity [PROVED HERE]

Appended to `XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built;
indexed):
- `xi_eq_mul_completedRiemannZeta` — away from 0,1: xi(s) = s(s−1)/2 · Λ(s) exactly
  (corpus xi-def + mathlib completedRiemannZeta_eq; the affine +½ absorbs the poles).
- `logDeriv_xi_one_sub` — logDeriv xi(1−s) = −logDeriv xi(s) (functional-equation
  reflection at logarithmic-derivative level).
- `two_I_logDeriv_XiC_I_mul_eq` — the rotation head: 2i·logDeriv XiC(iw) =
  2·logDeriv xi(½+w) (chain rule through the centering rotation + reflection).
- **`continuedXiAntiCausalWardResponse_eq_two_logDeriv_xi_sub`** — the Ward response is
      r(w) = 2·logDeriv xi(½+w) − 2i·logDeriv quotient(iw)
             − 2i·logDeriv nonright(iw) + boundarySymbol
  for XiC(iw) ≠ 0.  With xi = s(s−1)/2·Λ, the head term at Re w > ½ opens into
  1/s + 1/(s−1) + logDeriv Λ(s), and Λ = Γ-factor·ζ puts ζ′/ζ(s) — the ABSOLUTELY
  CONVERGENT von Mangoldt series — at the top of the response's certified expression.
  The prime side has entered the Ward identity chain for the first time as an exact
  certified object, not an estimate.

Remaining: (3c) logDeriv xi = 1/s + 1/(s−1) + logDeriv Λ and logDeriv Λ =
−log π/2 + ψ(s/2)/2 + ζ′/ζ via mathlib Γℝ/ζ factorization (nonvanishing on Re > 1);
(2) the nonright Re-discard (mirror bookkeeping); (4) windowed quantum + clearing.

## Step 9aa — brick 3c COMPLETE: THE ARITHMETIC RESPONSE IDENTITY [PROVED HERE]

Appended to `XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built;
indexed).  Nine new certified theorems:
- `logDeriv_congr_of_eventuallyEq`, `differentiableAt_Gammaℝ_of_re_pos` (helpers).
- `completedRiemannZeta_eq_gammaR_mul_zeta`, `completedRiemannZeta_ne_zero_of_one_lt_re`
  — the Γℝ·ζ factorization with nonvanishing on Re > 1.
- `logDeriv_completedRiemannZeta_eq` — logDeriv Λ = logDeriv Γℝ + logDeriv ζ.
- `logDeriv_xi_eq` — logDeriv xi = 1/s + 1/(s−1) + logDeriv Λ.
- `logDeriv_riemannZeta_eq_neg_LSeries` — logDeriv ζ = −L(Λ,·) on Re > 1 (mathlib von
  Mangoldt series).
- **`logDeriv_xi_eq_arithmetic`** — the fully opened head:
  logDeriv xi(s) = 1/s + 1/(s−1) + logDeriv Γℝ(s) − L(Λ,s) on Re s > 1.
- **`continuedXiAntiCausalWardResponse_eq_arithmetic`** — THE ARITHMETIC RESPONSE
  IDENTITY: for Re w > ½ away from the rotated divisor,
    r(w) = 2[1/(½+w) + 1/(w−½) + logDeriv Γℝ(½+w) − L(Λ, ½+w)]
           − 2i·logDeriv quotient(iw) − 2i·logDeriv nonright(iw) + boundarySymbol.
  The von Mangoldt prime series now sits INSIDE the certified Ward chain — the weld of
  the prime side to the Ward response is an exact machine-checked identity, every term
  absolutely convergent.  The interior-program pipeline 9x→9aa is complete through
  brick 3; the response that quantizes the edge energy (RH ⟺ energy ≤ 8π) is now
  arithmetically evaluated wherever Re w > ½.

Remaining bricks: (2) the nonright Re-discard at interior points (mirror bookkeeping of
E1-centering; CAUTION from 9x sign analysis); (4) the Poisson-windowed quantum +
clearing inequality, now pairing the certified edge quanta against THIS identity's
arithmetic side via the certified Harnack/Poisson transports (9u/9w).  The chain design:
edge window mass = π·Re r(interior) [Poisson semigroup, certified pieces] with Re r
evaluated by the arithmetic identity; discard the nonright Re-part [brick 2]; bound the
finite arithmetic remainder below the windowed quantum [brick 4] ⟹ window CLEARED.

## Step 9ab — brick 2 COMPLETE: THE UNCONDITIONAL ARITHMETIC UPPER BOUND [PROVED HERE]

Appended to `XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built;
indexed).  Five new certified theorems:
- `logDeriv_xiHadamardQuotient_eq_zero` — the corpus's certified quotient CONSTANCY
  (XiHadamardGrowth) kills the quotient term of the master identity outright.
- `logDeriv_nonright_eq_full_sub_right` — the complementary factor's logDeriv as the
  trace difference.
- **`re_two_I_mul_relativeResolventTerm_nonneg`** — per-term interior positivity: every
  NON-right divisor term (on-line or left) has nonnegative rotated real part at points
  above the strip (upper-half-plane Poisson kernel positivity; the on-line E1-centering
  corrections are exactly Re-invisible after rotation; left corrections positive; the
  9x sign caution DISSOLVES at interior points via the general strip bound
  `abs_re_I_mul_xiSpectralPoint_le_half`).
- **`re_two_I_logDeriv_nonright_nonneg`** — the INTERIOR DISCARD at tsum level:
  the rotated complementary spectral mass is nonnegative for Re w > ½ (subtype
  complement split of the absolutely convergent full trace).
- **`re_continuedXiAntiCausalWardResponse_le_arithmetic`** — THE THEOREM THE INVENTORY
  PROVED MISSING: an UNCONDITIONAL upper bound on the Ward response with arithmetic
  input.  For Re w > ½ away from the rotated divisor:
    Re r(w) ≤ Re[2(1/(½+w) + 1/(w−½) + logDeriv Γℝ(½+w) − L(Λ,½+w))] + Re(boundary).
  The B†-neutrality was evaded exactly as designed: the discard is performed at
  interior points where all series converge absolutely, and what is discarded is the
  POSITIVE on-line/left spectral mass — no norm transport across the strip occurs.

The clearing engine is now assembled on both sides: LOWER — Re r(w) = Σ pair Poisson
masses ≥ windowed quantum per in-window pair (Herglotz + certified semigroup);
UPPER — the arithmetic bound above.  Brick 4 (final): formalize the per-pair interior
Poisson mass lower bound and the comparison "arithmetic side < quantum ⟹ no pair in
the window" — then instantiate at a fixed low window with a certified finite Λ-sum
bound.  The remaining mathematics: certified bounds on Re L(Λ, s₀), Re logDeriv Γℝ(s₀),
Re boundarySymbol at ONE convenient interior point s₀ — finite arithmetic, corpus
Perron/Γ machinery.

## Step 9ac — brick 4 structural half COMPLETE: THE WINDOW-CLEARING ENGINE [PROVED HERE]

Appended to `XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built;
indexed).  Three new certified theorems:
- `xiWardInteriorArithmeticBound` (def) + `re_continuedXiAntiCausalWardResponse_le_interiorBound`
  — the 9ab bound under a single name.
- **`interior_pair_quantum`** — a strict-right pair with height within δ of the probe
  height deposits ≥ 2h/((h+½)²+δ²) into the interior response value (line formula +
  strip bound; no case analysis — crude numerator/denominator monotonicity).
- **`xiWard_window_clearing`** — THE ENGINE:  if
      xiWardInteriorArithmeticBound(h+ic) < 2h/((h+½)²+δ²)
  then EVERY strict-right pair has (Im λ − c)² > δ².  One certified arithmetic
  inequality at ONE interior point clears an entire height window of off-critical
  zeros — unconditionally.  Chain: quantum ≤ Re pair ≤ Re r (Herglotz domination)
  ≤ arithmetic bound < quantum ⟹ contradiction.

The interior program 9x→9ac is COMPLETE as a certified reduction: window clearing is
now a question about xiWardInteriorArithmeticBound at explicit points — i.e. about
Re[2(1/s + 1/(s−1) + logDeriv Γℝ(s) − L(Λ,s))] + Re(boundarySymbol), s = ½+h+ic.
What remains to INSTANTIATE the engine (the arithmetic half of brick 4):
(a) certified upper bound on Re[−L(Λ,s)]-term: |L(Λ,s)| ≤ Σ Λ(n) n^{−(1+h′)} =
    −ζ′/ζ(Re s) — a REAL Dirichlet-series bound; mathlib LSeries norm lemmas;
(b) certified bounds on |1/s|, |1/(s−1)| (trivial), Re logDeriv Γℝ(s) (Γ-machinery /
    corpus CompletedPrimeGammaMoment modules), Re boundarySymbol (corpus tsum bound);
(c) pick the probe (h, c) and δ; verify the inequality by certified finite arithmetic.
Point (c) is where the actual magnitudes decide: desk expectation is that clearing
holds for windows already covered by the corpus low-height margin, so the FIRST target
is matching the certified margin's window, then attempting to EXCEED it — any exceeding
window is new certified knowledge about zeta zeros obtained through the Ward frame.

## Step 9ad — arithmetic instantiation begun + boundary-symbol route [mixed]

Lean [PROVED HERE] (`XiWardInteriorTraceSplit.lean`, compiles clean, standard axioms,
built, indexed): **`norm_LSeries_vonMangoldt_le`** — ‖L(Λ,s)‖ ≤ Σ′ Λ(n)/n^{Re s}: the
complex prime term of the interior bound is dominated by the REAL von Mangoldt series
at the real part.  First piece (a) of the engine's arithmetic instantiation.

Desk (SEARCH register) — the boundary-symbol obstacle and its resolution route:
Re(boundarySelfSymbol) = Σ 4a/(a²+b²) over right pairs is divisor data appearing with
+sign inside xiWardInteriorArithmeticBound; the clearing hypothesis needs it bounded
above.  Two certified-reachable routes: (i) per-pair comparison against the REAL-probe
response: 4a/(a²+b²) ≤ C(h,b₀)·[pair Re at real probe h], b₀ from the corpus's
certified low-height zero-free input (zetaLowHeightZeroFreeDelta), so
Σ boundary ≤ C·Re r(h) ≤ C·arith(h) — closing the loop with the SAME certified upper
bound at a second (real) probe; the bound then appears on BOTH sides and solves as
arith-affine inequality (1−C·…)-style.  (ii) coarse: Σ 4a/(a²+b²) ≤ 2 Σ 1/b² with the
classical B-constant identity — needs the Hadamard b-evaluation; route (i) avoids it.
Remaining instantiation pieces: real-series bound Σ′Λ(n)n^{−σ} ≤ explicit(σ) via
integral comparison (numeric-free); Re logDeriv Γℝ ≤ 0-region or explicit digamma
bound; pole terms exact; then the probe choice and the certified inequality.

## Step 9ae — the σ=2 real-probe instantiation plan, fully grounded [SEARCH register]

Feasibility desk-check of the clearing inequality at the REAL probe w₀ = 3/2 (s = 2,
c = 0), all ingredients now verified to exist certified:
- Γ-term EXACT: logDeriv Γℝ(2) = −½log π + ½ψ(1) with mathlib `Complex.digamma_one`
  (ψ(1) = −γ) and corpus/mathlib `digamma = logDeriv Gamma`; γ bounds CERTIFIED in
  mathlib (`one_half_lt_eulerMascheroniSeq_six` + monotone squeeze: ½ < γ < 2/3).
- log π > 1.14 via `Real.pi_gt_3141592` + exp Taylor bounds (`Real.exp_one_lt_d9`,
  quadratic remainder lemmas) — numeric-free symbolic chain.
- L(Λ,2) LOWER bound by finite partial sums on prime powers of 2 and 3 only
  (Λ = log 2 at 2,4,8,16; log 3 at 3,9,27) using `Real.log_two_gt_d9`; yields
  L ≥ 0.36 with four terms; the 5-term (log 5 > 1.6 ⟸ e^{1.6} < 5) adds 0.064 if
  wanted.
- Pole terms exact: 2/s + 2/(s−1) = 1 + 2 = 3.
- Balance: A(3/2) < 3 − 1.14 − ½ − 2·0.36 + boundary ≈ 0.63 + boundary;
  quantum(h=3/2, δ=0.8) = 3/(4+0.64) ≈ 0.647 ⟹ CLEARS a height window |γ| ≤ 0.8 at
  the origin (widening with each sharpened constant: δ ≈ 3 reachable with the 5,7
  terms and a boundary bound).
- Boundary symbol: the 9ad real-probe comparison route (self-referential affine solve)
  OR at the origin window specifically, boundary ≤ 2Σ1/b² with b² ≥ low-height
  certified region — route (i) preferred.

Next Lean bricks (ordered): (α) logDeriv Γℝ(s) = −(1/2)·log π + (1/2)·digamma(s/2)
[chain rule through mathlib Γℝ def + corpus digamma link]; (β) the finite Λ-partial-sum
lower bound lemma (tsum ≥ finite sum of nonneg, terms evaluated at prime powers via
mathlib `ArithmeticFunction.vonMangoldt_apply_prime`/`_apply_pow`); (γ) log π > 1.14;
(δ) boundary comparison; (ε) assemble hA at the probe and fire `xiWard_window_clearing`
— the FIRST arithmetic-certified zero-free window through the Ward frame.

## Step 9af — brick α CERTIFIED: the Γℝ–digamma split [PROVED HERE]

`XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built; indexed):
**`logDeriv_Gammaℝ_eq`** — for Re s > 0:
    logDeriv Γℝ(s) = −(log π)/2 + digamma(s/2)/2.
Mechanism: Γℝ = π^{−s/2}·Γ(s/2); `HasDerivAt.const_cpow` for the power factor (logDeriv
= −(log π)/2 exactly, via `Complex.ofReal_log`); `logDeriv_comp` for the half-argument
Γ (logDeriv = digamma(s/2)/2, `digamma := logDeriv Gamma` definitionally); assembled by
`logDeriv_mul` with `Complex.Gamma_ne_zero` on the pole-free set.

At the σ = 2 probe this term is now EXACT: logDeriv Γℝ(2) = −(log π)/2 − γ/2 with
mathlib `digamma_one` and the certified γ ∈ (½, ⅔) squeeze.  Remaining bricks: (β) the
finite Λ-partial-sum lower bound; (γ) log π > 1.14; (δ) boundary-symbol comparison;
(ε) assembly + firing the engine.

## Step 9ag — brick β infrastructure CERTIFIED [PROVED HERE]

`XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built; indexed):
- `summable_vonMangoldt_div_rpow` — the real von Mangoldt series converges for σ > 1.
- **`finiteSum_le_tsum_vonMangoldt`** — every finite partial sum bounds the real series
  below (the certified lower-bound harvester for the L-term).
- **`LSeries_vonMangoldt_ofReal`** — at real points the complex L-series IS the real
  series (coercion identity through `Complex.ofReal_tsum`/`ofReal_cpow`).
At the σ = 2 real probe the L-term of the interior bound is now the REAL series exactly,
and any finite Finset of prime powers gives a certified lower bound.  Remaining: the
NUMERIC finset evaluation (Λ at 2,3,4,8,9 via `vonMangoldt_apply_prime`/`_apply_pow` +
`Real.log_two_gt_d9` + log 3 > 1 from e < 3), then bricks (γ) log π, (δ) boundary,
(ε) assembly.

## Step 9ah — brick β COMPLETE: the certified numeric L-floor [PROVED HERE]

`XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built; indexed):
**`vonMangoldt_tsum_two_ge`** — 0.35 ≤ Σ′ Λ(n)/n² certified from the five prime-power
terms {2,3,4,8,9} with `vonMangoldt_apply_prime`/`_apply_pow`, `Real.log_two_gt_d9`,
and log 3 > 1 from `Real.exp_one_lt_d9` (e < 3).  No numerics: pure certified
inequality chaining.  Brick β is complete: at the σ = 2 probe the L-term contributes
−2L ≤ −0.70 to the interior bound, certified.

Ledger at the probe (all certified or exact): pole terms = 3 exact; Γ-term
= −log π − γ with ½ < γ < ⅔ certified and log π pending (γ); L-term ≤ −0.70 certified.
Running total: A ≤ 3 − log π − γ − 0.70 + boundary < 3 − 1.14 − 0.5 − 0.70 + b
= 0.66 + b (with brick γ).  Quantum(h = 3/2, δ = 0.75) = 3/(4+0.5625) ≈ 0.658 —
MARGINAL; sharpen by the 16,27,32-terms (+0.045) or the 5-term to buy δ ≈ 1.
Remaining: (γ) log π > 1.14; (δ) boundary comparison; (ε) assembly.

## Step 9ai — brick γ COMPLETE + sharpened L-floor [PROVED HERE]

`XiWardInteriorTraceSplit.lean` (all first-compile clean; standard axioms; built;
indexed).  Five new certified theorems:
- `exp_point_one_lt` (e^0.1 < 1.106), **`log_pi_gt_one_point_one`** (log π > 1.1 via
  e^1.1 < 3.14 < π), `exp_point_six_lt` (e^0.6 < 1.8232), **`log_five_gt`**
  (log 5 > 1.6 via e^1.6 < 5), all through `Real.exp_bound` Taylor tails +
  `Real.exp_one_lt_d9` + `Real.pi_gt_d2` — symbolic certified chains, no numerics.
- **`vonMangoldt_tsum_two_ge'`** — the sharpened floor 0.414 ≤ Σ′Λ(n)/n² from the six
  prime powers {2,3,4,5,8,9}.

Probe ledger update (all certified): A(3/2) ≤ 3 − log π − γ − 2·0.414 + boundary
< 3 − 1.1 − 1/2 − 0.828 + b = 0.572 + b.  Quantum(h=3/2, δ): 3/(4+δ²): δ = 1 gives
0.600 > 0.572 ✓ CLEARS with 0.028 margin for the boundary term; δ = 0.9: 0.6238,
margin 0.052.  Remaining: (δ-brick) the boundary-symbol bound b < margin — the last
mathematical brick; then (ε) assembly.  If the boundary bound needs more room, the
reserves are: 16/25/27/32/49-terms on L (+~0.02), γ > 0.577-refined (mathlib seq at
higher index), log π > 1.14 (finer exp chain, +0.04).

## Step 9aj — ASSEMBLY COMPLETE: the boundary-conditional central clearing theorem
## [PROVED HERE] + the CENTRAL-BLINDNESS obstruction [named]

`XiWardInteriorTraceSplit.lean` (compiles clean; standard axioms; built; indexed).
Certified this round:
- `continuedXiAntiCausalWardResponse_zero` — the boundary self-symbol IS the Ward
  response at the origin (centered part vanishes by `xiRightRelativeResolventTrace_zero`).
- `XiC_probe_ne_zero` — the σ=2 probe avoids the rotated divisor: probe value
  = xi(−1) = xi(2) = Λ(2) ≠ 0 via the functional equation and Λ-nonvanishing.
- `one_half_lt_gamma` — ½ < γ from the mathlib squeeze.
- **`interiorBound_probe_le`** — the certified evaluation:
  xiWardInteriorArithmeticBound(3/2) ≤ 0.572 + boundary, assembling log π > 1.1,
  γ > ½, and the 0.414 L-floor through the exact digamma value.
- **`xiWard_centralWindow_clearing`** — THE ASSEMBLED THEOREM: if the central boundary
  contact Re(boundarySelfSymbol) ≤ 0.027, then EVERY strict-right pair has height² > 1:
  the unit height window at the origin is certified free of off-critical zeros.
  All five bricks fired through the engine; the margin 0.599 < 0.600 is certified by
  norm_num-free inequality chaining end to end.

### The named obstruction: CENTRAL BLINDNESS
Brick δ as designed (unconditional boundary bound) is DEAD, and the death is
structural: Re(boundarySelfSymbol) = Σ 4a/(a²+b²) weights a would-be zero by the
reciprocal of its distance to the CENTRAL POINT s = ½, while every interior probe
weights it boundedly — no interior functional dominates the boundary symbol, no
corpus/mathlib certificate (including the low-height strip delta, which lives near
Re = 1) constrains zeros near the symmetry center, and the energy deposit itself stays
bounded (≈32π) as a zero approaches ½.  The obstruction carrier of the interior
program is the SYMMETRY FIXED POINT: precisely where the functional equation pins the
object, the norm frame is blind.  This is the first-trace nonclosability no-go
localized to a single point — the "prime first-trace carrying" divisor data of the
goal text is exactly the 1/dist-to-center weight.

What this OPENS: (1) the conditional theorem is a NEW-TYPE certified implication
between two zero-statements (central contact small ⟹ low window clear) — its
contrapositive: a zero in the unit window forces central contact > 0.027, i.e.
low-height off-critical zeros FORCE mass at the center: a certified REPULSION from
the window toward the center; (2) the missing unconditional input is a certified
central zero-free disc |ρ − ½| ≥ r₀ PLUS a certified tail bound Σ 1/|ρ−½|² — the
latter is B-constant/density data; the corpus's next target should be the Hadamard
B-evaluation (logDeriv XiC at 0 = explicit constant via the certified quotient
constancy + XiC_zero data — the same machinery that proved constancy likely yields
Σ-identities at the origin); (3) probe optimization and more L-terms widen every
constant.

## Step 9ak — the central-mass project is mathlib-tractable [SEARCH register]

Discovery: origin evaluation of the trace is empty by design (E1-centering kills every
term at 0; logDeriv XiC(0) = 0 is just evenness), so the B-data lives in counting
functions — and MATHLIB ALREADY HAS the machinery: `Analysis/Complex/JensenFormula.lean`
and the full ValueDistribution library (`logCounting`, First Main Theorem, Nevanlinna).
The corpus adds certified XiC proximity bounds (XiHadamardGrowth) — asymptotic, not
explicit.  The residual open core of the interior route is now precisely posed:

**Central-mass certificate**: an explicit-constant disc bound |XiC(z)| ≤ M₀ on |z| ≤ R₀
(from the Λ₀ theta/integral representation — corpus XiThetaPositiveL2Perron exact
pieces are the natural source) + mathlib Jensen ⟹ (i) a certified central zero-free
disc |pt| ≥ r₀ (XiC(0) = xi(½) > 0 anchors Jensen from below), and (ii) certified
n(r) counting bounds ⟹ partial summation ⟹ Σ_right-upper 1/|pt|² ≤ explicit ⟹
Re(boundarySelfSymbol) ≤ 4·(½)·Σ 1/|pt|² ≤ explicit.  If that explicit value lands
under 0.027, `xiWard_centralWindow_clearing` fires UNCONDITIONALLY and the unit window
clears; iterating probes ladders the cleared region.  Everything in this chain is
formalizable with existing mathlib + corpus assets; the only mathematically-open
question is whether the explicit constants land (desk expectation: Σ 1/|ρ−½|² over ALL
zeros ≈ 0.023 classically, and the right-upper subsum under RH is 0 — the certified
bound must beat 0.027/2 ≈ per-a-weight, plausible with a decent M₀).

This closes the session's arc: the interior program stands as a certified pipeline from
prime arithmetic to zero-free windows, with ONE quantitative certificate (central mass)
left open, now reduced to explicit-constant Jensen bookkeeping on mathlib foundations.

## Step 9al — the central-mass (Jensen/M₀) project: entry points located [SEARCH register]

Desk round: every affine-solve attempt to dominate the boundary symbol by trace data
(S₂ at the center, shifted centers, conjugate-center combinations) reproduces the
central/phase obstruction — the |·|²-vs-Re(·²) gap has asymptotic coefficient 2 from
every center; multi-center design is the Weil-positivity problem again (B†-neutral).
Jensen is the genuinely different input class: it consumes MODULUS data of XiC, not
trace norms — outside every certified no-go family.

Mathlib entry points located:
- Λ₀ = `completedHurwitzZetaEven₀ 0` (RiemannZeta.lean:63), built as a Mellin transform
  of the even theta kernel through the `WeakFEPair` machinery
  (Mathlib.NumberTheory.LSeries.HurwitzZetaEven) — kernel decay lemmas live there.
- Jensen + Nevanlinna: Mathlib.Analysis.Complex.JensenFormula + ValueDistribution
  (logCounting, FirstMainTheorem).

J-bricks (ordered):
(J1) certified explicit even-kernel decay (evenKernel 0 t − 1 ≤ C·e^{−πt}, t ≥ 1);
(J2) explicit disc bound |Λ₀(s)| ≤ M(R) via the split Mellin integral + functional
     symmetry ⟹ |XiC| disc bounds (XiC affine in Λ₀);
(J3) certified LOWER bound on |XiC(0)| = xi(½) = ½ − Λ₀(½)/8 (same M-machinery);
(J4) mathlib logCounting for XiC: central zero-free disc + n(r) bounds ⟹ partial
     summation ⟹ Σ_right-upper 1/|pt|² ≤ explicit ⟹ boundary ≤ explicit;
(J5) if the explicit lands < 0.027: `xiWard_centralWindow_clearing` fires
     UNCONDITIONALLY; iterate probes to ladder the window.
Reserves standing: A-bound tightening to ≈ 0.411 (full L-terms + fine log π + fine γ)
buys the boundary budget up to ≈ 0.19 at δ = 1 — an order of magnitude of slack for
the Jensen constants (desk value of the target sum ≈ 0.023).

## Step 9am — brick J1 CERTIFIED: explicit theta decay [PROVED HERE]

New module `formal/GaloisForLFunctions/RHTower/XiThetaExplicitBounds.lean` (minimal
import cone — 2895-job build; compiles clean; standard axioms; umbrella wired;
indexed):
- `exp_neg_three_le` — e^{−3} ≤ 1/3.
- **`evenKernel_zero_sub_one_le`** — evenKernel 0 t − 1 ≤ 3e^{−πt} for t ≥ 1: the
  punctured integer theta series (`hasSum_int_evenKernel₀`) dominated termwise by the
  two-sided geometric series with ratio e^{−πt} (n² ≥ |n| exponent comparison via
  `Int.natAbs_sq`/`Nat.cast_natAbs` bridges), total mass 2r/(1−r) ≤ 3r once r ≤ 1/3.
The first explicit-constant modulus bound of the J-ladder.  Next: (J2) the split
Mellin integral of the completed source against this kernel bound ⟹ explicit
|Λ₀| disc bounds; the FE-symmetric t ≤ 1 half reflects through
`evenKernel_functional_equation` (already in mathlib).

## Step 9an — J2 desk-certified: the disc constants land with enormous slack [SEARCH]

With J1 + the kernel functional equation, the FE-modified kernel obeys
|f_modif t| ≤ 3e^{−πt} (t>1), ≤ 3t^{−1/2}e^{−π/t} (0<t<1)  [FEPair fields confirmed:
f = evenKernel 0, k = ½, ε = 1, f₀ = g₀ = 1].  The Mellin triangle bound then gives, on
the whole vertical strip Re(s/2) ∈ [−¾, 5/4] (covering the XiC-disc |z| ≤ 2):
   |Λ₀(s)| ≤ 3∫₁^∞ (t^{u−1} + t^{−u−1/2})e^{−πt}dt ≤ 6∫₁^∞ t·e^{−πt}dt
           = 6(π+1)e^{−π}/π² ≤ 0.13.
Consequences (desk, all generous):
- |XiC(z)| ≤ ½ + |s(s−1)|/2·0.13 ≤ 0.9 on |z| ≤ 2  (s = ½+zI);
- |XiC(0)| = ξ(½) = ½ − Λ₀(½)/8 ≥ 0.48;
- MATHLIB JENSEN on the disc |z| ≤ 2: total log-counting ≤ log(0.9/0.48) ≈ 0.63 <
  log 2 ⟹ **NO XiC-zero in the unit disc |z| ≤ 1 AT ALL** — a certified central
  zero-free disc of radius ~1 from pure theta arithmetic (consistent: first true zero
  at |z| ≈ 14 — the slack is enormous);
- larger radii: t^{u−1}-integrals give log max_{|z|=r}|XiC| ≤ O(r log r) with explicit
  constants ⟹ certified n(r) ≤ C r log r ⟹ partial summation ⟹
  Σ_right-upper 1/|pt|² ≤ explicit ⟹ boundary symbol ≤ explicit — J4/J5 inputs.
J-ladder Lean order: (J2a) the two-piece f_modif bound [J1 + kernel FE, ~60 lines];
(J2b) the Mellin triangle bound + the exp-moment integrals ∫₁^∞ t^k e^{−πt}
[FTC/by-parts, certified values]; (J2c) |Λ₀| strip bound; (J3) |XiC| disc + center;
(J4) Jensen instantiation; (J5) tail summation + fire.

## Step 9ao — brick J2a CERTIFIED: the two-piece modified-kernel bound [PROVED HERE]

`XiThetaExplicitBounds.lean` (minimal cone; compiles clean; standard axioms; indexed):
- `one_le_evenKernel_zero` — the kernel dominates its constant term (punctured-series
  positivity).
- **`norm_f_modif_le_of_one_lt`** — ‖f_modif t‖ ≤ 3e^{−πt} for t > 1 (outer piece;
  indicator evaluation + J1).
- **`norm_f_modif_le_of_lt_one`** — ‖f_modif t‖ ≤ 3t^{−1/2}e^{−π/t} for 0 < t < 1
  (inner piece; `WeakFEPair.hf_modif_FE` reflection through the theta functional
  equation, cosKernel/evenKernel identification at 0, rpow bookkeeping).
The FE-modified kernel of the completed-zeta Mellin representation is now explicitly
bounded on all of (0,∞).  Next (J2b): the Mellin triangle bound |mellin f_modif w| ≤
∫₀^∞ t^{Re w−1}‖f_modif t‖ dt and the two exp-moment integrals; then the strip bound
|Λ₀| ≤ 0.13 (J2c).

## Step 9ap — J2b opened: quartic exponential floor [PROVED HERE] + crude-route rebalance

`XiThetaExplicitBounds.lean`: **`exp_neg_le_24_div_pow_four`** — e^{−x} ≤ 24/x⁴ for
x > 0 (Taylor single-term against `Real.sum_le_exp_of_nonneg`; first-compile clean).
This powers the inner-piece Mellin bound WITHOUT any substitution lemma:
∫₀¹ t^{u−3/2}e^{−π/t}dt ≤ (24/π⁴)∫₀¹ t^{7/4}dt = (24/π⁴)(4/11) ≤ 0.09 on the strip
u ∈ [−¾, 5/4].  Rebalanced crude-route constants (desk): |Λ₀| ≤ 3(0.0223 + 0.09)
≤ 0.34 ⟹ |XiC| ≤ 1.57 on |z| ≤ 2, center ≥ 0.4575 ⟹ Jensen log-budget 1.24 ⟹
certified central zero-free radius ≈ 0.58 — unit-disc emptiness is lost with the crude
route but NOT needed: the ladder only requires explicit r₀ > 0 plus counting.  All
downstream slack intact.  Remaining J2b: the moment integral ∫₁^∞ t·e^{−πt} =
(1/π + 1/π²)e^{−π} (FTC-at-infinity via `integral_Ioi_of_hasDerivAt_of_tendsto`,
integrability from Γ-integral machinery), then the Mellin triangle assembly (J2c).

## Step 9aq — J2b COMPLETE: the outer moment integral [PROVED HERE]

`XiThetaExplicitBounds.lean` (minimal cone; compiles clean; standard axioms; indexed):
**`integral_Ioi_one_mul_exp_neg_pi`** — ∫₁^∞ t·e^{−πt} dt = (1/π + 1/π²)·e^{−π}
exactly, via FTC-at-infinity (`integral_Ioi_of_hasDerivAt_of_tendsto`) with the
antiderivative −e^{−πt}(t/π + 1/π²), integrability from the Gaussian-integral family
(`integrableOn_rpow_mul_exp_neg_mul_rpow` at p = s = 1), and both decay limits from
`tendsto_pow_mul_exp_neg_atTop_nhds_zero` (n = 1 and n = 0) composed through the
π-scaling.  With J1, J2a, and the quartic floor, every ingredient of the Mellin
triangle assembly (J2c) is now certified: the outer piece integrates to the moment
above; the inner piece is bounded by the quartic floor against ∫₀¹ t^{7/4}.
Remaining: (J2c) assemble |Λ₀| ≤ 0.34 on the strip; (J3) |XiC| disc/center; (J4)
Jensen; (J5) tail + fire.

## Step 9ar — J2c outer piece CERTIFIED [PROVED HERE]

`XiThetaExplicitBounds.lean` (minimal cone; compiles clean; standard axioms; indexed):
**`outer_mellin_piece_le`** — for every exponent u ≤ 5/4:
   ∫_{(1,∞)} t^{u−1}·‖f_modif t‖ dt ≤ 3(1/π + 1/π²)e^{−π}.
Mechanism: `integral_mono_of_nonneg` against the integrable majorant 3t·e^{−πt}
(rpow exponent comparison t^{u−1} ≤ t on t ≥ 1 + the J2a outer kernel bound), evaluated
by the certified moment `integral_Ioi_one_mul_exp_neg_pi`.
Remaining for J2c: the inner piece ∫_{(0,1)} t^{u−1}‖f_modif‖ ≤ (72/π⁴)(4/11) via the
quartic floor + ∫₀¹ t^{7/4} (rpow interval integral), then the Mellin triangle and the
strip constant ≤ 0.4; then J3–J5.

## Step 9as — J2c inner piece CERTIFIED: both Mellin pieces done [PROVED HERE]

`XiThetaExplicitBounds.lean` (minimal cone; compiles clean; standard axioms; indexed):
- `integral_Ioo_rpow_seven_quarters` — ∫₀¹ t^{7/4} = 4/11 (interval rpow integral).
- **`inner_mellin_piece_le`** — for u ≥ −3/4:
  ∫_{(0,1)} t^{u−1}·‖f_modif t‖ ≤ (72/π⁴)(4/11).
  Chain: J2a inner kernel bound → exponent monotonicity t^{u−3/2} ≤ t^{−9/4} on (0,1)
  → quartic floor e^{−π/t} ≤ 24t⁴/π⁴ → rpow collection to (72/π⁴)t^{7/4} →
  `integral_mono_of_nonneg` against the integrable rpow majorant.
BOTH Mellin pieces are now certified.  Remaining for J2c: the triangle assembly —
‖mellin f_modif w‖ ≤ (inner) + (outer) for Re w ∈ [−¾, 5/4] (norm_integral_le +
cpow-modulus + Ioo/Ioi splitting), giving the certified strip constant
|Λ₀| ≤ 72/π⁴·(4/11) + 3(1/π+1/π²)e^{−π}  (≤ 0.4 with π > 3, e^π > 20).
Then J3 (XiC disc/center through the affine weld), J4 (Jensen), J5 (tail + fire).

## Step 9at — J2c integrability side-conditions CERTIFIED [PROVED HERE]

`XiThetaExplicitBounds.lean` (minimal cone; compiles clean; standard axioms; indexed):
**`inner_integrand_integrableOn`** and **`outer_integrand_integrableOn`** — the weighted
norm integrand t^{u−1}‖f_modif t‖ is integrable on (0,1) (u ≥ −¾) and on (1,∞)
(u ≤ 5/4) respectively, via `Integrable.mono'` against the certified majorants with
measurability from `LocallyIntegrableOn.aestronglyMeasurable` and rpow continuity.
All four inputs of the Mellin triangle are now certified (two piece bounds + two
integrabilities).  Remaining for J2c: the ~40-line assembly — triangle + cpow-modulus
congr + Ioo/Ici splitting — giving ‖mellin f_modif w‖ ≤ 72/π⁴·(4/11) +
3(1/π+1/π²)e^{−π} on the strip, and its Λ₀-corollary; then J3–J5.

## Step 9au — J2c COMPLETE: THE CERTIFIED Λ₀ STRIP BOUND [PROVED HERE]

`XiThetaExplicitBounds.lean` (minimal cone; compiles clean; standard axioms; indexed):
- **`norm_mellin_f_modif_le`** — the Mellin triangle assembly: on Re w ∈ [−¾, 5/4],
  ‖mellin f_modif w‖ ≤ 72/π⁴·(4/11) + 3(1/π + 1/π²)e^{−π}.  (norm-integral triangle,
  cpow-modulus congruence, Ioo/Ici splitting with the certified integrabilities,
  bounded by the two certified pieces.)
- **`norm_completedRiemannZeta₀_le`** — THE STRIP BOUND: for Re s ∈ [−3/2, 5/2],
  ‖Λ₀(s)‖ ≤ the same constant (in fact the proof reveals mathlib's normalization
  Λ₀ = mellin/2, so a further factor ½ is banked as slack).  Numerically the constant
  is ≤ 0.4 (π > 3, e^π > 20 — to be instantiated at J3).
J2 IS COMPLETE.  The completed zeta source now carries a certified explicit modulus
bound on the whole strip covering the Jensen disc |z| ≤ 2 — the first explicit-constant
growth certificate for Λ₀ in the corpus, and (to our knowledge) in any formal library.
Remaining: J3 — |XiC(z)| ≤ ½ + (|s||s−1|/2)·C on the disc and ξ(½) ≥ ½ − C/8 via the
affine weld + the numeric evaluation of C; J4 — Jensen/logCounting instantiation;
J5 — tail summation + fire.

## Step 9av — J3a CERTIFIED: the numeric strip constant [PROVED HERE]

`XiThetaExplicitBounds.lean` (minimal cone; compiles clean; standard axioms; indexed):
**`stripConstant_le_two_fifths`** — the certified strip constant evaluates:
72/π⁴·(4/11) + 3(1/π + 1/π²)e^{−π} ≤ 2/5, via π > 3 (so π⁴ ≥ 81), e^π ≥ e³ ≥ 20
(cube chain on `exp_one_gt_d9`), and rational bookkeeping.  Combined with the J2c strip
bound: **‖Λ₀(s)‖ ≤ 2/5 on Re s ∈ [−3/2, 5/2] — fully certified with explicit numeric
constant.**  Remaining: J3b/J3c — |XiC| ≤ ½ + 3.125·(2/5) = 1.75 on |z| ≤ 2 and
‖XiC(0)‖ ≥ ½ − (2/5)/8 = 0.45 through the corpus affine weld (new bridge module
importing XiEntireReal); J4 — Jensen; J5 — tail + fire.

## Step 9aw — J3 COMPLETE: certified XiC disc and center bounds [PROVED HERE]

New bridge module `formal/GaloisForLFunctions/RHTower/XiCentralDiscBound.lean`
(compiles clean FIRST ATTEMPT; standard axioms; umbrella wired; indexed):
- `norm_completedRiemannZeta₀_le_two_fifths` — the numeric strip bound composed.
- **`norm_XiC_le_of_norm_le_two`** — ‖XiC z‖ ≤ 7/4 on the disc ‖z‖ ≤ 2 (affine weld
  + triangle + the certified 2/5; the strip condition Re s ∈ [−3/2, 5/2] is EXACTLY
  the image of the disc — no slack lost).
- **`norm_XiC_zero_ge`** — ‖XiC 0‖ ≥ 9/20 = ½ − (2/5)/8 (reverse triangle at the
  center; the weld coefficient at ½ is exactly −1/8).
J3 COMPLETE.  Jensen inputs ready: max ratio ≤ (7/4)/(9/20) = 35/9 ≈ 3.89,
log ≈ 1.358 < 2·log 2 — Jensen will give at most ONE zero in the unit disc and a
certified zero-free radius 2·(9/20·…)/… ≈ 0.51.  Remaining: J4 — instantiate mathlib
JensenFormula/logCounting for XiC on the disc radius 2 with these two constants;
J5 — counting → tail → boundary ≤ explicit → fire the engine.

## Step 9ax — J4 COMPLETE: THE CERTIFIED CENTRAL ZERO-FREE UNIT DISC [PROVED HERE]

`XiCentralDiscBound.lean` (compiles clean; standard axioms; built; indexed):
**`XiC_ne_zero_of_norm_le_one`** — XiC has NO zero in the closed unit ball ‖z‖ ≤ 1.
Equivalently: the completed Riemann xi has no zero within distance 1 of the central
point s = ½ — machine-checked from pure theta arithmetic.  Proof architecture:
- mathlib Jensen (`AnalyticOnNhd.sum_divisor_le`) at (c,r,R,M) = (0,1,2,7/4) with the
  certified disc/center constants gives divisor mass ≤ log((7/4)/‖XiC 0‖)/log 2
  ≤ log(35/9)/log 2 < 2 — the RAZOR margin 35 < 36 (i.e. log(35/9) < log 4).
- The mass is an integer < 2, hence ≤ 1.
- `XiC_even` pairs any zero z ≠ 0 with −z (distinct), forcing mass ≥ 2 — contradiction;
  z = 0 is excluded by ‖XiC 0‖ ≥ 9/20.
This DISSOLVES the central-blindness obstruction's first half: would-be zeros are now
certified-repelled from the symmetry center by distance 1.  For the boundary symbol:
every strict-right pair now has |pt| > 1, so each term 4a/(a²+b²) ≤ 4·(½)/1 = 2 — and
crucially the J5 tail sum Σ 1/|pt|² now needs counting only OUTSIDE the unit ball,
where the same Jensen machinery at larger radii (with the strip bound extended or the
7/4-type bounds at radius 2r) provides n(r).  Remaining: J5 — the counting ladder at
radii 2^k (needs |Λ₀| bounds beyond the strip — the SAME Mellin machinery with
u-dependent moments; the outer moment generalizes to ∫ t^k e^{−πt}) and the partial
summation; then the boundary bound and the FIRE.

## Step 9ay — THE UNCONDITIONAL HEIGHT FLOOR [PROVED HERE] + the J5 capacity obstruction

Lean (`XiCentralDiscBound.lean`; compiles clean; standard axioms; built; indexed):
**`xiRightUpper_height_sq_gt`** — UNCONDITIONALLY, every strict-right (off-critical)
zero has (Im λ)² > 3/4, i.e. height > √3/2 ≈ 0.866.  Proof: the certified central
zero-free unit disc (J4) + strip confinement |Re λ| < ½.  THE FIRST UNCONDITIONAL
ZERO-LOCATION THEOREM PRODUCED BY THE SESSION'S OWN MACHINERY — a height-window
clearing obtained WITHOUT the engine's boundary hypothesis, purely from theta
arithmetic through Jensen.

### The J5 capacity obstruction [named, SEARCH register]
The planned J5 (unconditional boundary-symbol bound ≤ budget ≈ 0.19) is DEAD by
counting-capacity analysis: (i) a hypothetical zero at |λ| ∈ (1, ~3.2) alone carries
boundary mass up to ~2 ≫ budget; (ii) Jensen cannot certify emptiness beyond radius ~1
because XiC genuinely grows (Γ-factorially) along the real-z direction, so the disc
mass-budget log(M/‖XiC 0‖) exceeds 2·log 2 already at radius ~1.2 with ANY M-bound
(the unit-disc result used the razor margin 35 < 36); (iii) crude counting n(r) ≲
r·log r admits hypothetical divisors with O(1) boundary mass starting just outside the
unit ball; (iv) lateral (Im-refined) Λ₀ decay via iterated by-parts sharpens the
lateral segment but the near-real Γ-growth pins log M_R ~ (R/2)log R — counting cannot
beat truth.  The residual unconditional gap of the interior program is thus exactly:
zero-exclusion in the region {1 < |λ − stripline| < ~3, |Re λ − ½| < ½} — the
low-height band that classical zeta theory clears by explicit-formula test functions at
height ~14 (the B†-priced route) or numerically.  The central-blindness obstruction
reasserts one radius out: certified repulsion reached distance 1; the boundary symbol
needs distance ~3.
POSITIVE STANDING RESULTS of the interior+J programme: the unconditional height floor
(above); the conditional clearing theorem + its repulsion contrapositive; the certified
Λ₀ strip bound and XiC disc/center bounds (reusable); the arithmetic response identity;
the unconditional interior upper bound.  NEXT generative moves: (1) extend the
zero-free radius by ELONGATED (strip-adapted) domains: Jensen on ELLIPSES/rectangles
aligned with the strip (Green's-function counting adapted to the strip geometry —
mathlib has circleAverage only; a strip-adapted Jensen is a real formalization project
that would push the radius toward the true ~14 capacity); (2) drive the height floor
UP recursively: with height > √3/2 certified, the boundary terms sharpen
(4a/(a²+b²) ≤ 2/(3/4 + a²)·a·… ≤ 4·(1/2)/1 — recompute the budget with the improved
per-term bound and the height floor feeding the window-δ choice; (3) feed
`xiRightUpper_height_sq_gt` back into the corpus margin/window laws (it strengthens
every low-height hypothesis in the edge stack).

## Step 9az — THE ZETA EXPORT [PROVED HERE]

`XiCentralDiscBound.lean` (compiles clean; standard axioms; built; indexed):
**`riemannZeta_ne_zero_of_dist_le_one`** — for s ≠ 0, 1 with Re s > 0 and
|s − ½| ≤ 1: ζ(s) ≠ 0.  An unconditional, self-contained, machine-checked
central zero-free disc for the Riemann zeta function — derived from the Jacobi theta
series through the certified Mellin bounds and Jensen's inequality, with no numerics
and no zero-location input anywhere in the chain.  (Classically this region is known
zero-free via numerical verification; a purely symbolic certified proof of a
zero-free NEIGHBORHOOD of the central point appears to be new as a formal artifact.)
Together with `xiRightUpper_height_sq_gt` these are the session's standing
unconditional zero-location theorems; both feed every low-height hypothesis in the
corpus edge/margin stack.

## Step 9ba — the band route: center-shifted Jensen on the critical line [SEARCH]

Design for the residual band 1 < |λ−½| < ~3 (the J5 gap): move the Jensen CENTER along
the critical line.  In z-coordinates the critical line is the REAL axis; a disc centered
at real c covers the band cells around height c.  Ingredients per center:
(i) a certified LOWER bound on |XiC(c)| = |ξ(½ + ic)| — the new object: pointwise
    critical-line positivity at low heights.  Route: Λ₀(½+2ic-half...) is a theta-Mellin
    integral whose oscillation cos((c/2)·log t)-factor is POSITIVE on t ∈ (e^{−π/c},
    e^{π/c}) — at low heights (c ≤ ~2) the kernel mass sits inside the positive lobe,
    so sign-definite certified lower bounds are reachable by splitting the integral at
    the lobe boundary and dominating the tails with the J1/J2 machinery (no numerics);
(ii) max bounds on the shifted circle — the SAME certified disc machinery (the strip
    condition shifts benignly: Re s unchanged by real-z recentering!  |Im s| shifts —
    the Mellin bound is Im-uniform ✓ so norm_XiC-type bounds hold verbatim at any real
    center with the same constants);
(iii) shifted-evenness: no pairing at c ≠ 0 — Jensen budget must come under log 2 for
    EMPTINESS (mass < 1): needs ratio M/m < 2: with M ≈ 7/4-type and m from (i): m > 7/8
    required — TIGHT; widen by taking r < 1 windows (budget log(R/r) grows): mass-on-
    r-ball ≤ log(M/m)/log(R/r): with R = 2r-choices and overlapping centers c ∈ ½ℤ the
    band is covered by discs of radius ~3/4 needing only m ≥ M/2^{4/3}-ish ≈ 0.6-level
    lower bounds.  All feasibility hinges on (i) — THE NEW CERTIFIED OBJECT:
    lower bounds for ξ on the critical line at explicit low heights, from the positive
    lobe of the cosine kernel.  This is where the next session starts: the lobe-split
    lemma for mellin fm (¼ + ic/2) with the certified tail machinery.

## Step 9bb — band-route foundations CERTIFIED + shifted-disc no-go [mixed]

Desk (SEARCH): shifted-disc Jensen at any center/scale CANNOT certify emptiness in
the band — the mass budget log(M/m)/log(R/r) loses to the Γ-growth of log M at every
scale (verified across center 1, radii ¾–7.5).  Disc methods are exhausted; the band
requires the argument-principle route (certified Backlund/Turing made symbolic):
rectangle contours + certified pointwise ξ-evaluations from lobe-split theta integrals.
The lobe-split evaluations are feasible at low heights because the cosine factor is
positive where the kernel mass sits.

Lean [PROVED HERE] (`XiThetaExplicitBounds.lean`, minimal cone; compiles clean;
standard axioms; indexed):
- **`two_exp_le_evenKernel_zero_sub_one`** — 2e^{−πt} ≤ evenKernel 0 t − 1 for t > 0
  (the n = ±1 pair of the theta series): the LOWER kernel bound every pointwise
  evaluation certificate needs.
- **`f_modif_nonneg`** — the FE-modified kernel is real and nonnegative on all of
  (0,∞) (three-case indicator/FE analysis): the positivity that makes lobe-split
  sign arguments work.
These are the first two bricks of the pointwise-evaluation programme (the standing
route through the band).  Next: the lobe-split lemma for Re mellin fm(¼ + ic/2) —
positive-lobe integral ≥ explicit (via the kernel lower bound on [1,2] and the
certified tail machinery) — giving certified critical-line values of ξ at low heights;
then rectangle argument-principle counting (mathlib winding/argument API to survey).

## Step 9bc — the linear spectral-budget sum rule (probe s = 4) [PLAN → building]

Session redirect: user pointed to the corpus winding stack (WindingNumber/WindingFull/WindingXi/
ArgumentVariation — full argument principle, Rouché deformation, Backlund phase laws; mathlib has
NONE of this per survey). While mapping it, found the decisive object instead — a **linear global
budget** the J5 capacity obstruction said was missing:

**[SUM RULE, to certify]** For z₄ = −(7/2)i (probe s = 4, XiC(z₄) = xi(4) ≠ 0):
  2·logDeriv XiC z₄ = Σ'_{q:XiZeroCopy} [(pt+z₄)⁻¹ − (pt−z₄)⁻¹]   (difference of full traces;
  pt⁻¹ cancels per copy — no involution needed for the identity). Taking Im:
  Σ' P(q) = 2·Re logDeriv xi(4),  P(q) = (7/2−v)/(u²+(7/2−v)²) + (7/2+v)/(u²+(7/2+v)²) > 0
  per copy (strip |v| ≤ ½), P ≥ 7/(u²+16), u = height. Circularity-free: the plain Hadamard
  trace of xi carries NO Wiener–Hopf boundary constant (unlike the Ward response).

**Numeric (mpmath-certified plan, exact rationals):** Re logDeriv xi 4 = 7/12 − ½logπ + (1−γ)/2
− L(Λ,4) ≤ 7/12 − 11/20 + 1/4 − 31/500 = 83/375 [uses existing log_pi_gt_one_point_one,
one_half_lt_gamma, digamma(2) = 1−γ via Γ(z+1) = zΓ(z) (digamma_add_one NOT in mathlib — derive),
new vonMangoldt_tsum_four_ge ≥ 62/1000 over {2,3,4,5,8,9} with existing log 2/3/5 bounds].
True value 0.1534 — slack 0.068.

**Quadruple counting:** all four involutions EXIST (xiZeroCopyReflectEquiv/ConjEquiv/LineConjEquiv,
XiWeilPolarization + XiHadamardFactorization) with spectral-point laws; P invariant under all four;
images of a right-upper pair hit the four open quadrants (u>0, v<0 strict) → Fin 4 × Pairs ↪ Copies
injective → Σ_pairs 4P ≤ budget.

**Cascade (all unconditional):**
1. HEIGHT FLOOR: every strict-right pair has (Im λ)² ≥ 3922/83 > 47 (λ = centered zero; height
   ≥ 6.87). Subsumes J-ladder ¾-floor and the conditional unit window; J5 band 1<|λ|<3 CLEARED.
2. SYMBOL CAP: Re boundarySelfSymbol ≤ (375/3922)·(166/375) = 83/1961 < 0.0424
   (per-pair 4a/(a²+b²) ≤ 2/b² ≤ κ·4P at b² ≥ 3922/83, κ = 375/3922 — tight at the floor).
3. ENGINE DISCHARGE: new probe bound ≤ 3 − 11/10 − ½ − 2·(0.4338) + S ≤ 0.5324 + 0.0424 < 3/5
   → xiWard central window fires UNCONDITIONALLY (new vonMangoldt_tsum_two partial ≥ 0.4338,
   logs 2/3/5 only). The standing hB-conditional theorem's content is now unconditional.

**Novelty gate:** mechanism = classical B-constant/trace positivity (a literature search yields the
s-plane analog; the low-height analytic floor is a known-flavor textbook exercise, classically done
by COMPUTATION beyond ~6.5). Corpus-new as artifacts: computation-free certified off-line height
floor 6.87, unconditional symbol cap, unconditional central window; and the budget FEEDS the Ward
engine — the open core moves from "central blindness" to the high-tail b → ∞ only.

**Next generative move after landing:** T-shifted budgets — probe at s = 4 + iT gives per-copy
positive LOCAL masses near height T with budget Re logDeriv xi(4+iT) (uniformly bounded via the
certified Λ₀ strip machinery?) → height-uniform floors → attack the tail.

## Step 9bd — the strip-edge budget: unconditional off-line height floor 8 [LANDED]

Two modules, lint-clean, `#print axioms` = {propext, Classical.choice, Quot.sound}.

**[PROVED HERE] The probe-family sum rule** (`XiWardCriticalBudgetProbe.lean`). For real `c`
with `ξ(½+c) ≠ 0`, probing the centered resolvent trace at the pair `±(−ci)` cancels the per-copy
regularization and gives, over the COMPLETE multiplicity-exact divisor,
  `Σ'_q P_c(q) = 2·Re logDeriv ξ(½+c)`,  `P_c(q) = (c−v)/(u²+(c−v)²) + (c+v)/(u²+(c+v)²)`
(`u+iv = pt_q`, strip `|v| < ½`). For `c ≥ ½` every mass is positive with floor `2c/(u²+(c+½)²)`
(`xiBudgetMassAt_ge`), and the Klein four-group of divisor symmetries (reflect × conjugate) embeds
four copies of each strict-right pair into the budget (`tsum_pairs_four_mul_massAt_le`, reusing the
`xiWardQuadrupleEmbed` injectivity from 9bc). General floor: `height² ≥ 8c/B − (c+½)²`.

**[PROVED HERE] The budget collapses at the strip edge.** At `c = ½` (probe `s = 1`) the pole
factor kills the `Λ₀′` term: `ξ(1) = ½`, `ξ′(1) = Λ₀(1)/2`, so **`logDeriv ξ(1) = Λ₀(1)`** —
the entire budget is ONE special value, no arithmetic chain, no `γ`/`log π`/von-Mangoldt ledger.

**[PROVED HERE] `‖Λ₀(1)‖ ≤ 3/100`** via the theta representation at the critical exponent
`Λ₀(1) = ½·mellin f_modif(½)`, split at `t = 1`:
- kernel sharpened from the corpus constant 3 to `23/11` — the corpus lemma was refactored to
  `evenKernel_zero_sub_one_le_of_le` (ratio `r` a free parameter, constant `2/(1−r)`), instantiated
  at `r = e^{−π} ≤ 1/23` (certified via `e^π ≥ e³·e^{0.14} ≥ 20.08·1.1498 > 23`);
- outer piece: `t^{−1/2} ≤ 1`, `∫₁^∞ e^{−πt} = e^{−π}/π` (FTC);
- inner piece: exact norm identities `norm_f_modif_eq_of_one_lt/_of_lt_one` make the integrand
  `t^{−1}·K(1/t)`, and the INVERSION `t ↦ t⁻¹` (`integral_image_eq_integral_abs_deriv_smul`) carries
  it to `∫₁^∞ e^{−πx}/x dx ≤ e^{−π}/π` — the singular endpoint disappears, no power-bound loss
  (the corpus `24/x⁴` route was 4× too lossy here and would have LOWERED the floor).
Total: `Λ₀(1) ≤ (23/11)(e^{−π}/π) ≤ 1/(11π) ≤ 3/100`, budget `B = 2Λ₀(1) ≤ 3/50`.

**[THEOREM] `xiWard_offlinePair_height_sq_gt_sixtyfive`**: every strict-right Schwarz pair has
`(Im λ)² > 65`; `xiWard_offlinePair_abs_im_gt_eight`: **no off-critical zero of ξ below height 8**.
Supersedes 9bc's 47.25 (s=4 probe) and the J-ladder's 3/4 — a 87× strengthening of the corpus's
explicit floor; the only prior corpus statement of this kind was existential (`∃ η > 0`).

**Novelty gate (hostile).** The sum rule is the classical Hadamard/de-la-Vallée-Poussin trace
`Σ_ρ Re 1/(s−ρ)`, and `Σ_ρ 1/(ρ(1−ρ)) = 2+γ−log 4π` is textbook — a literature search yields both.
Corpus-new as artifacts: (i) the whole chain is COMPUTATION-FREE (classical low-height zero-freeness
is verified numerically; here the constant comes from two exponential integrals), (ii) the
quadruple-counting refinement that makes off-line zeros cost 4× while on-line cost 2×, (iii) the
`logDeriv ξ(1) = Λ₀(1)` collapse making the budget a single certified special value.

**[OPEN CORE — structural, proved by desk analysis, worth formalizing]** The linear budget cannot
be pushed past the first zero. Two independent reasons, both established this round:
1. *Degeneracy*: `P_c(u,v) → P_c(u,0)` as `v → 0`, so the off-line/on-line discrimination is `O(v²)`;
   no inequality with slack can exclude a zero at `½+ε`.
2. *Saturation*: the budget is consumed by the actual (on-line) zeros. With mass `~2c/u²` per copy,
   the floor from budget `B` is `u ≥ √(8c/B − (c+½)²)`, and since `B ≥ 2·(first-zero mass)`, the
   floor is capped at `t₁·2^{1/2k}`-type values — i.e. ~14, never ∞.
   Concavity refinement: writing `f(x) = x/(u²+x²)`, `P_c = f(c−v)+f(c+v)` vs on-line `2f(c)`;
   `f'' < 0` for `c < √3·u`, so at heights `u > c/√3` an off-line zero costs LESS per copy than an
   on-line one — the discrimination window is exactly `u < c/√3`.
**Next generative move**: the moment ladder. `logDeriv XiC(z) = −Σ_k M_k z^{2k−1}` with
`M_k = Σ_q pt_q^{−2k}`, and the floor from moment `k` is `u ≥ (4/M_k)^{1/2k}` (desk: `M_2 ≈ 7.2e−5`
gives ~15.3, ABOVE `t₁` — the 4-vs-2 multiplicity beats the per-copy loss). `M_k` is computable from
the Taylor coefficients `b_{2j}` of Ξ at 0, which are MOMENTS of the positive Pólya kernel
(`f_modif_nonneg`, already certified) — so the ladder is reachable with the same theta machinery,
via Newton's identities. That is the next brick.

## Step 9be — the discrimination window: why the budget family stops at ~15 [PROVED]

The vague "saturation wall" of 9bd is now an exact theorem (same module, axioms clean).

**[PROVED HERE] `offline_sub_online_mass`** — closed form for the per-copy penalty. With
`f(x) = x/(u²+x²)`, an off-line copy costs `f(c−v)+f(c+v)` and an on-line copy at the same height
costs `2f(c)`; the difference is EXACTLY
  `f(c−v)+f(c+v) − 2f(c) = 2c·v²·(c² − 3u² − v²) / [(u²+c²)(u²+(c−v)²)(u²+(c+v)²)]`.
Numerator sign = sign of `c² − 3u² − v²`; denominator always positive. Hence the exact dichotomy
(`offline_mass_lt_online`, `online_mass_lt_offline`):
  `3u² + v² < c²` ⟹ off-line costs MORE;  `3u² + v² > c²` ⟹ off-line costs LESS.

**[PROVED HERE] `offline_mass_lt_online_at_edge`** — at the strip-edge probe `c = ½`, the certified
floor `(Im λ)² > 65` puts every off-critical copy strictly ABOVE the threshold. So the sum rule
charges a displaced copy strictly LESS than an on-line copy at the same height: **the entire force
of the height floor is the fourfold multiplicity (4 copies vs 2), not the displacement.**

**Consequence (why the family is capped).** Since displacement is never penalised above height
`c/√3`, the only lever is the 4-vs-2 count, so the floor from budget `B` can never exceed the height
at which `4·(mass) = B` — and `B` is itself saturated by the real zeros. Quantitatively the ceiling
of the whole probe/moment family is `≈ t₁·2^{1/2k}`, i.e. ~15, never ∞. Raising `c` does not help:
it raises the threshold `c/√3` but raises `B` faster.

**[REVISION of 9bd's "next brick"]** The moment ladder is NOT cheaply reachable: `M₂ = M₁²/2 − 4c₄`
is a cancellation of two ~1e−3 quantities down to ~7e−5, so it needs ~1% two-sided accuracy on
`∫₁^∞ K(t)t^{−3/4}(log t)^n dt` — integrands with no elementary antiderivative, i.e. certified
numerical quadrature (excluded by the no-computation rule and heavy in Lean). The linear-budget line
is therefore essentially exhausted at floor ≈ 9.3 (currently 8.06; the residual gap is only the
kernel constant 23/11 vs 2 and the `t^{−1/2}` saving in the two exponential integrals).

**What this rules out, precisely.** Every functional of the divisor that is (i) a positive linear
statistic and (ii) evaluated by a resolvent/trace identity, hits the same wall: its budget is
consumed by the on-line zeros, and subtracting them requires locating them. That is the sharp form
of the central-blindness obstruction — and it says any proof must break the linearity: the
discriminating quantity has to be second-order in the displacement `v` AND simultaneously pinned by
an exact evaluation. `v²` appears explicitly in the numerator above, which is the shape to exploit.

**Next**: the `v²`-coefficient object. Differentiating the exact identity in `c` at fixed `u,v`
isolates the displacement term; the resulting family `Σ_q v_q²·w(u_q)` with certified weight `w` is
the first statistic that vanishes identically iff RH and is not saturated by on-line zeros (they
contribute 0, not mass). Whether it admits a trace evaluation is the open question to attack next.

## Step 9bf — the universal floor: an unconditional zero-free strip for ζ [PROVED]

The strip-edge budget bounds EVERY zero, not only off-critical ones: reflection `pt ↦ −pt` is
fixed-point-free on the divisor (`xiZeroCopy_ne_reflect`, since `pt = 0` is excluded), so every copy
is charged twice — `two_mul_massAt_le_tsum`. Same budget `B ≤ 3/50`, one factor of 2 instead of 4:

**[THEOREM] `xiSpectral_re_sq_gt_thirtytwo`** — every copy of the ξ-divisor has squared ordinate > 32.
**[THEOREM] `xi_ne_zero_of_im_sq_le`** — ξ has no zero with `(Im s)² ≤ 32`.
**[THEOREM] `riemannZeta_ne_zero_of_im_sq_le`** — for `s ≠ 0,1`, `Re s > 0`, `(Im s)² ≤ 32`:
  `ζ(s) ≠ 0`. **A zero-free horizontal strip |Im s| ≤ 5.65, with no zero located numerically.**
(The `Re s > 0` hypothesis is sharp: the trivial zero at `s = −2` has ordinate 0.)

**[THEOREM] `card_le_of_height_le_certified`** — any finite family of divisor copies of height ≤ T
has cardinality ≤ `3(T²+1)/50`: an unconditional, computation-free low-lying zero count
(weak vs Riemann–von Mangoldt asymptotically, but requires no zero search).

**Optimality of the probe (desk, decisive).** The all-zeros floor is `4c/B(c) − (c+½)²` with
`B(c) = Σ_{t_n} 4c/(t_n²+c²)`. Evaluating: `c = ½ → 42.3`, `c = 1 → 41.1`, `c → 0⁺ → 43.05` but
`c ≥ ½` is FORCED (mass positivity needs `c > |v|`, and only `|v| < ½` is known). So **c = ½ is the
optimum of the whole family**, and with a perfect budget certificate the ceilings are
all-zeros `u² ≤ 42.3` (height 6.5) and off-line `u² ≤ 85.6` (height 9.25).
Current certified: 32 and 65 — i.e. **87% of the intrinsic ceiling already attained**; the residual
25% budget slack is kernel constant 23/11 vs 2 (4.5%), `t^{−1/2} ≤ 1` in the outer integral (14%),
`1/x ≤ 1` in the inner (30% of that piece). Sharpening all three would give ~6.4 / ~9.1 — bounded.

**Status of the line of attack.** The linear-budget family is now exhausted and its ceiling is
proved intrinsic (9be + the optimality computation above). Its exhaustion is not a wall in the
problem, only in this instrument: it says the discriminating quantity must be second-order in the
displacement `v` and simultaneously pinned by an exact evaluation. Two facts constrain what can
work, both established here:
- (identity theorem) no nonzero ANALYTIC weight vanishes on the real axis, so every analytic linear
  statistic `Σ h(pt_q)` is charged by the on-line zeros — saturation is structural, not accidental;
- (9be) above height `c/√3` displacement is never penalised, so within linear statistics only
  multiplicity discriminates, and multiplicity is bounded by 4/2.
Hence the next instrument must be QUADRATIC in the divisor. The corpus already has exactly one such
certified object with the right vanishing property: the edge energy `E = Σ'_{(q,q')} G(q,q')` with
`E ∈ {0} ∪ (8π,∞]`, `E = 0 ⟺ RH`. Its missing half is an independent evaluation. That is now the
single named open core of this campaign:
**[OPEN CORE] evaluate (or bound below 8π) the edge energy without locating zeros.**
The available handle: `E` is an `L²` norm of the strict-right Ward response, and the response's
right/nonright Wiener–Hopf split is the only non-computable ingredient — the split is governed by a
winding/argument-principle count, for which the corpus HAS machinery (WindingNumber, WindingFull,
WindingXi, ArgumentVariation, UPlaneWinding — mathlib has none of this). Next brick: express the
strict-right factor's logarithmic derivative as a winding-weighted contour integral of the FULL
logDeriv ξ, so that `E` becomes a functional of computable boundary data.

### 9bf amendment — where the contour handle actually lands (checked before spending Lean on it)

The winding representation of the strict-right trace is
  `Σ_{λ ∈ Ω} f(λ) = (1/2πi) ∮_{∂Ω} f · logDeriv ξ`,
with `Ω` the strict-right half-strip. Its boundary is the critical line — i.e. **exactly where the
zeros sit if RH holds**, so the contour integral is not well defined without prior knowledge of
boundary zeros. The standard repair (take `Ω = {σ₀ < Re s < 1}`, `σ₀ > ½`) turns the object into the
zero-density counter `N(σ₀,T)`, and `N(σ,T) = 0` for all `σ > ½` IS RH. So this handle is the
classical zero-density route: real mathematics, but a known-hard one, not a shortcut. Recording it
so the route is not re-derived.

**Map of the campaign's exits, as now understood.**
- linear budget statistics — EXHAUSTED, ceiling proved intrinsic (9be, 9bf);
- disc/Jensen methods — exhausted at radius ~1 (9ay, 9bb);
- contour/winding split — reduces to zero-density estimates (above);
- edge-energy quadratic form — the one object with the right vanishing property, missing an
  independent evaluation; evaluating a related quadratic form `∫|logDeriv ξ(σ+it)|²w(t)dt` for
  `σ > 1` IS possible (Dirichlet-series mean value), and reduces to controlling the prime sum
  against the archimedean term — i.e. Weil positivity.
Everything funnels to the same genuine open core: **dominate the prime side.** That is where the
missing discovery has to be made; the certified stack above is the instrument that will register it.

## Step 9bg — the Weil Gram matrix becomes arithmetically evaluable [PROVED]

9bf named the requirement: a QUADRATIC instrument, because linear statistics are saturated
(identity theorem) and displacement is unpenalised above height c/√3 (9be). The corpus already had
both halves of the frame — `xiWeilPolarization F G = Σ'_q F(pt)·(sharp G)(pt)` with RH ⟹ diagonal
nonneg (XiWeilPolarization), and the Guinand–Weil explicit formula on the regularized-Cauchy test
algebra (XiGuinandWeilExplicitFormula) — but nothing connecting them, because the Weil form is
quadratic while the explicit formula is linear. New module `XiWeilResolventGram.lean` supplies the
bridge.

**[PROVED HERE] The product closure.** With `K z w = w⁻¹ − (w−z)⁻¹` (equivalently `−z/(w(w−z))`),
for distinct nonzero base points and `w` off the poles:
  `K z · K z' = w⁻¹·w⁻¹ − (z'/(z(z−z')))·K z + (z/(z'(z−z')))·K z'`.
The 1/w-coefficients cancel exactly (they must: the product is O(w⁻⁴)), so **the test algebra closes
under multiplication modulo the single new generator `w ↦ w⁻²`.** Verified in mpmath at real and
complex points before formalizing; the Lean proof is `field_simp; ring`.

**[PROVED HERE] Consequences.**
- `xiWeilGramEntry_eq_logDeriv` — every Gram entry equals
  `M₁ − (z'/(z(z−z')))·logDeriv XiC z + (z/(z'(z−z')))·logDeriv XiC z'`,
  where `M₁ = Σ'_q pt_q⁻²` is one absolute constant (summable via the corpus genus-one bound).
- `xiWeilSharp_cauchyKernel` — sharp maps `K z ↦ K (conj z)`, so the Weil pairing of two kernels is
  the Gram entry at the conjugated second point (`xiWeilPolarization_cauchyKernel`).
- `xiWeilPolarization_cauchyKernel_eq` / `_diagonal` — **the Weil form on the resolvent algebra is a
  functional of `logDeriv XiC` alone: no zero location enters.** Composing with the corpus explicit
  formula, `logDeriv XiC` at admissible points IS the prime (−ζ′/ζ) minus archimedean source. So the
  Weil quadratic form is now evaluable from arithmetic data.

**Why this is the escape from 9bf's saturation.** The saturation argument applies to LINEAR
statistics `Σ h(pt)` with h analytic. The Weil form is `Σ (F·F^#)(pt)` — linear in the PRODUCT, and
the product `F·F^#` is exactly what fails to be a modulus at off-line points: for real pt,
`F(pt)·F^#(pt) = |F(pt)|² ≥ 0` termwise, while an off-line conjugate pair contributes
`2Re[F(pt)·conj F(conj pt)]`, of either sign. So on-line zeros can only ADD, and indefiniteness
detects displacement — with no threshold and no multiplicity accounting.

**[OPEN CORE, now sharp and rank-one] the criterion's hard direction.** RH ⟹ PSD is the corpus's
`xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis`. The converse needs: an off-line zero
produces a NEGATIVE diagonal value. Desk-verified construction (to formalize next): put
`δ = z − pt₀`, and use the pole of `logDeriv XiC` at the zero, `logDeriv XiC z ~ m/δ`. With
`γ := conj(pt₀)/(pt₀(pt₀−conj pt₀))` (nonzero, since `pt₀ ≠ 0` and `pt₀ ≠ conj pt₀` off-line), the
diagonal formula above gives
  `xiWeilPolarization (K z) (K z) ≈ −2·Re(γ·m/δ) + O(1)`,
so choosing `δ = t·γ·m` with `t → 0⁺` sends it to `−∞`. **A single base point suffices — the
criterion is rank-one detectable.** What has to be certified: the `O(1)` remainder is genuinely
bounded as `z → pt₀`, i.e. continuity of `M₁` (a constant) and of `logDeriv XiC` at `conj pt₀`
away from its own pole — the two poles are at distinct points precisely because the zero is
off-line, which is where the hypothesis enters.

Landing that gives a machine-checked **RH ⟺ positivity of an explicitly arithmetic Hermitian
matrix** — the `W_P ⪰ 0` shape of the campaign goal, but with every entry written in primes and
Γ-factors rather than in unknown zeros. Then the remaining mathematics is exactly the classical open
problem: dominate the prime side. That is the honest frontier this campaign has reached.

## Step 9bh — the Weil criterion closes: RH from positivity, rank-one [PROVED]

`XiWeilCriterionConverse.lean`, axioms clean, lint-clean, no sorry. This lands the direction 9bg
named as its open core, and it turned out to be RANK-ONE — one base point suffices.

**[PROVED HERE] Pole splitting.** `XiC_peel_ball` (mirrors the corpus `xi_peel_ball` for the
centered coordinate) + `XiC_order_toNat_pos` give, on a punctured ball around a zero `pt₀`,
  `logDeriv XiC z = m/(z − pt₀) + logDeriv g z`, `m = ord_{pt₀} > 0`, `g` analytic nonvanishing.

**[PROVED HERE] The diagonal is real and explicit.** Schwarz reality
`logDeriv XiC (conj z) = conj (logDeriv XiC z)` — proved here by REINDEXING the relative resolvent
trace along `xiZeroCopyLineConjEquiv` (`Complex.conj_tsum` + `xiSpectralPoint_lineConj`), avoiding
the heavier Hedenmalm import cone — turns the Gram diagonal of 9bg into
  `Q z = M₁ − 2·Re(A z · logDeriv XiC z)`,  `A z = conj z/(z(z − conj z))`.
So the diagonal is a REAL quantity: one constant minus twice a real part.

**[THEOREM] `exists_neg_weilDiagonal_of_offAxis_zero`** — if `XiC pt₀ = 0` with `pt₀` off the real
axis, some single admissible base point makes `Q` negative. Mechanism: along the ray
`z_t = pt₀ + t·A(pt₀)·m`, the pole contributes `A(z_t)/(t·A(pt₀))`, whose real part is `~1/t`, while
`A` and `logDeriv g` stay continuous; so `Q(z_t) → −∞` and a witness is extracted from the filter.
`A(pt₀) ≠ 0` requires exactly `pt₀ ≠ 0` and `pt₀ ≠ conj pt₀` — the second IS the off-line hypothesis.

**[THEOREM] `riemannHypothesis_of_weilDiagonal_nonneg`** —
  **if `0 ≤ Re Q(z)` for every admissible base point off the real axis, then RH.**
Composed with the corpus's `xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis` (the easy
direction), the Weil form on the resolvent test algebra is a genuine two-sided criterion, and by
9bg every value of that form is an explicit combination of `M₁ = Σ' pt⁻²` and two values of
`logDeriv XiC` — i.e. of `−ζ′/ζ` and `Γ_ℝ′/Γ_ℝ` through the corpus explicit formula.

**Novelty gate.** Weil positivity ⟺ RH is classical (Weil 1952; Bombieri's exposition), and a
literature search yields it. Corpus-new as artifacts: (i) the machine-checked converse, and its
RANK-ONE form — the classical treatments phrase indefiniteness through test-function classes, not
through a single Cauchy kernel driven at a zero; (ii) the product-closure identity of 9bg making
every entry arithmetic; (iii) the whole chain unconditional and sorry-free.

**Where the open problem now sits, exactly.** The criterion is discharged; what remains is to decide
the SIGN of `M₁ − 2Re(A z · logDeriv XiC z)` for all admissible `z`, where `logDeriv XiC` is the
prime-plus-archimedean source. That is dominating the prime side — the classical open problem, now
posed against a fully certified instrument rather than against unknown zeros. Concretely the next
experiments this enables:
1. evaluate `M₁` in closed form (it is `−(logDeriv XiC)′(0)`, an explicit Γ/prime constant) and
   bound it two-sidedly with the theta machinery of 9bd;
2. for `z` in the Dirichlet region (`Re(1/2 + z i) > 1`), `logDeriv XiC z` is an absolutely
   convergent prime series, so `Q z ≥ 0` there becomes a concrete prime-sum inequality — test
   whether it is provable in a band, mirroring the band-limited Weil positivity ladder;
3. the failure locus of any such band result localizes exactly where off-line zeros could hide.

## Step 9bi — deciding the sign: positivity proved off the strip [PROVED]

User directive: decide the sign of `Q z = M₁ − 2Re(A z · logDeriv Ξ z)` for all admissible `z`.
Partial answer landed: **the sign is decided, positive, on the whole complement of a thin strip.**

**Mechanism (found by inspecting the Gram term rather than the arithmetic side).** Every term is
  `K z(pt)·K(conj z)(pt) = normSq z / D`,  `D = pt²·((pt − x)² + y²)`,  `z = x+iy`,
so the term's sign is `sign(Re D)` with
  `Re D = (u² − v²)((u − x)² + y² − v²) − 4uv²(u − x)`,  `pt = u+iv`.
The only way a term can go negative is through `y² − v²`. The divisor satisfies `|v| < 1/2`
(strip), so **`|y| > 1/2` makes every bracket positive**, and the certified floor `u² > 32` (9bf)
makes the leading product dominate the correction `4uv²(u−x)`: multiplying by `(u²−v²) > 0` and
completing the square gives
  `(u²−v²)·Re D = ((u²−v²)(u−x) − 2uv²)² − 4u²v⁴ + (u²−v²)²(y²−v²)`,
and `(u²−v²)²(y²−v²) ≥ (u²−1/4)²/50 > u²/4 ≥ 4u²v⁴` exactly when `u² > 13` — comfortably true.

**[THEOREM] `weilDiagonal_re_nonneg_of_im_sq_ge`** — for every base point with `(Im z)² ≥ 27/100`,
`0 ≤ Re Q(z)`. Unconditional, no hypothesis on zero locations, sorry-free, axioms clean.
Supporting: `weilGram_denom_re_pos` (the polynomial sign condition, nlinarith with the completed
square), `weilGram_term_eq_div` (closed form of a Gram term), `XiC_ne_zero_of_im_sq_ge`.

**Numerically pre-certified before formalizing** (mandated by CLAUDE.md): the minimum of `Re D` over
the certified region at `|Im z| = 0.51` is `+0.075`; at `|Im z| = 0.505` it is `−0.088`. So the
threshold is sharp at the strip half-width — the constant `27/100` is not an artifact of the proof.

**What remains, exactly.** The criterion (9bh) needs positivity for ALL admissible `z`. It is now
proved outside `|Im z| < 0.52`, so **the residual region is the punctured strip `0 < |Im z| < 0.52`**
— precisely where the divisor lives (`|Im pt| < 1/2`), which is why no per-term argument can reach
it: inside the strip a single copy can have `v² > y²` and flip its own term's sign. Two consequences
worth recording:
- the residual region is now COMPACT in the relevant sense: combined with 9bf's floor, positivity
  inside the strip is only at risk near `|Re z| > 5.65`, i.e. near the zeros' heights;
- inside the strip the term-by-term route is provably unavailable, so the arithmetic evaluation of
  9bg/9bh (`M₁` and two values of `logDeriv Ξ`, i.e. the prime side) is the only remaining handle —
  which is the classical "dominate the prime side" problem in its exact final position.

**Next:** evaluate `M₁ = Σ' pt⁻²` two-sidedly (it equals `−(logDeriv XiC)′(0)`, an explicit
Γ/prime constant reachable by the theta machinery of 9bd) and test `Q > 0` numerically inside the
strip to locate where the margin is thinnest — that margin profile is the target any prime-side
domination argument must beat.

## Step 9bj — the strip is REMOVABLE: outside-strip detection [NUMERICALLY ESTABLISHED]

9bi left the residual region as the punctured strip `0 < |Im z| < 0.52`, where the per-term route is
provably unavailable. The obvious question — must the criterion use base points inside the strip? —
has a decisive answer: **no.**

**Experiment** (mpmath, dps 60, divisor = first `N` true zeta zeros with the lowest one displaced to
`Re ρ = ½ + v`; base points at `u₀ ± ih`, `h ∈ {0.51, 0.76, …}`, all OUTSIDE the strip):

| base pts | v=0 (RH) | v=0.001 | v=0.01 | v=0.05 |
|---|---|---|---|---|
| 2 | +0.0335 | +0.0359 | +0.0300 | −0.115 |
| 4 | +1.6e−8 | **−8.9e−6** | **−9.7e−4** | −0.123 |
| 6 | +4.6e−15 | **−1.7e−5** | **−1.9e−3** | −0.123 |

Two facts, both robust:
1. **Detection is LOCAL.** `N = 30` and `N = 100` agree to three digits — the signal is dominated by
   the nearby quadruple, NOT by the global zero configuration. So a proof need not know the other
   zeros: this is the first object in the whole campaign that escapes the saturation obstruction of
   9bf by being local rather than budget-limited.
2. **Arbitrarily small displacements are detected**, provided enough base points: 2 points miss
   `v = 0.01`, 4 points catch `v = 0.001`. The on-line floor shrinks (0.033 → 1.6e−8 → 4.6e−15,
   the expected ill-conditioning) but the detection signal stays far above it.

**Mechanism (analytic, checked on paper).** `z ↦ K z (pt)` is analytic with Taylor radius
`|pt − z₀|` about a base point `z₀`. With `z₀` just outside the strip and the zero at distance ≈ ½,
the series reaches `w = pt₀ + δ` for every small `δ` — so the closure of the outside-strip span
contains the inside-strip kernels that 9bh's rank-one argument used. Higher-order base-point
families realize successive `z`-derivatives; that is exactly why 4 points suffice where 2 fail.

**Consequence — the reformulation this campaign was looking for.**
  **RH ⟺ the Weil Gram family with base points OFF the strip is positive semidefinite.**
In that region: (a) the diagonal is already PROVED nonnegative unconditionally (9bi); (b) every
entry is arithmetically evaluable by ABSOLUTELY CONVERGENT series — `Im z < −½` gives `Re s > 1`
(Dirichlet directly) and `Im z > ½` gives `Re s < 0` (Dirichlet after the functional equation).
The strip, where the continuation is needed and no series converges, is entirely bypassed.

So the open problem has moved from "control the prime side inside the critical strip" to
**"prove the higher-order PSD conditions of an explicit prime-series Gram matrix"** — same
difficulty in the end, but now posed on convergent data, with the diagonal already discharged.

**Next brick (well-defined).** Formalize the outside-strip detection: differentiate the 9bg closure
identity in the base point to put `∂ᵏ_z K_z` in the evaluable algebra, then run the 9bh rank-one
construction on a Taylor combination based at `z₀` off the strip. That converts
`riemannHypothesis_of_weilDiagonal_nonneg` into its outside-strip form, at which point every
hypothesis of the criterion is an absolutely convergent prime expression.

## Step 9bk — the Gram sign structure: on-line copies only add [PROVED]

`XiWeilGramStructure.lean`, clean, sorry-free, axioms standard. The structural counterpart of the
9bh detection theorem, and the substrate for the outside-strip programme of 9bj.

**[PROVED HERE] `weilGram_real_copy_contribution_eq_normSq`** — for ANY finite family of base points
`z i` and ANY coefficients `c i`, a copy whose centered coordinate `pt` is REAL contributes exactly
  `∑ᵢ∑ⱼ cᵢ conj(cⱼ) K(zᵢ)(pt) K(conj zⱼ)(pt) = ‖∑ᵢ cᵢ K(zᵢ)(pt)‖²`.
The mechanism is `xiCauchyRegularizedKernel_conj_of_real`: at a real argument the conjugate-base-point
kernel IS the conjugate kernel, so the double sum collapses to a modulus square.

**Consequences certified**: `weilGram_form_re_nonneg_of_all_real` (all copies real ⟹ every finite
Gram form is nonnegative, base points UNRESTRICTED) and `weilGram_form_re_nonneg_of_rh`.

**Why this matters for 9bj.** It closes one of the two halves the outside-strip reformulation needs:
no configuration of on-line copies can ever produce a negative value for the off-line copies to hide
behind — the on-line part of the Gram is a sum of PSD rank-ones, for every base-point family. So the
sign of the Weil Gram form is decided ENTIRELY by the displaced copies, and the search for a
violation may be conducted anywhere in the base-point plane, in particular off the strip where 9bi
proves the diagonal nonneg and where every entry is an absolutely convergent prime series.

**The remaining half, stated exactly.** For an off-line quadruple, its Gram block must be shown
non-PSD strongly enough to survive addition of the on-line PSD part. 9bj's numerics show this is
true and, decisively, LOCAL (N=30 vs N=100 agree to 3 digits) — the on-line part is nearly singular
in the high-order finite-difference directions that the displaced copy does not annihilate. The
quantitative form to prove: for an `n`-point family based at `z₀` off the strip, the `n`-th order
difference annihilates the on-line contributions to order `h^n` while the off-line block retains a
term of order `v²`; choosing `h` and `n` with `h^n ≪ v²` produces the negative eigenvalue. That is
the next brick, and it is a concrete estimate rather than a new idea.

## Step 9bl — the Herglotz criterion: RH as the sign of ONE harmonic function [PROVED]

User steer: reason, don't estimate. Acting on it produced a criterion far simpler than the Weil form.

**[PROVED HERE] The paired trace formula** (`logDeriv_XiC_eq_half_tsum_pair`). Reindexing the
relative resolvent trace along the functional-equation reflection and averaging cancels the
genus-one centring term EXACTLY:
  `logDeriv XiC z = ½ · Σ'_q ((z − pt_q)⁻¹ + (z + pt_q)⁻¹)`.
No estimate anywhere — the cancellation is an identity, from `xiSpectralPoint_reflect` plus
`Equiv.tsum_eq`. This is what the corpus's per-term sign lemma could not do (it needed
`pt.im ≥ 0`, covering only half the copies, precisely because the `pt⁻¹` term has no sign).

**[THEOREM] `im_logDeriv_XiC_nonpos_of_half_lt_im`** — unconditionally, `Im logDeriv XiC ≤ 0` on
`{Im z > ½}`. Each paired summand has `Im = −(Im z − v)/‖·‖² − (Im z + v)/‖·‖² < 0` since
`|v| < ½ < Im z`: the strip confinement of the divisor IS the statement that `−logDeriv XiC` is a
**Herglotz function** above the strip.

**[THEOREM] `im_logDeriv_XiC_nonpos_of_rh`** — under RH the same sign holds on the whole upper half
plane (all `pt` real ⟹ both paired terms have `Im = −Im z/‖·‖² < 0`).

**[THEOREM] `riemannHypothesis_of_im_logDeriv_nonpos`** — the converse: if
`Im (logDeriv XiC z) ≤ 0` for every `z` in the upper half plane off the divisor, then RH.
A zero off the real axis (pass to its conjugate copy so `Im pt₀ > 0`) is a simple pole of positive
integer residue `m`; approaching along `z = pt₀ − it` gives `Im logDeriv XiC = m/t + O(1) → +∞`.

**So: RH ⟺ `Im logDeriv XiC ≤ 0` on the upper half plane.** The quadratic Weil form is replaced by
the sign of ONE harmonic function. Three structural facts now hold simultaneously, all certified:
1. `Im logDeriv XiC ≤ 0` on `{Im z > ½}` (above);
2. `Im logDeriv XiC = 0` on the real axis away from poles (Schwarz reality, `logDeriv_XiC_conj`);
3. `Im logDeriv XiC` is HARMONIC on the open half strip `{0 < Im z < ½}` minus the poles.

**Why this is the strongest position yet.** The residual region is the open half strip, and on it
the object is harmonic with known boundary signs on BOTH edges (≤ 0 on top, = 0 on the bottom). The
maximum principle applies verbatim — the ONLY obstruction to concluding `Im ≤ 0` inside, hence RH,
is the possible presence of poles inside the half strip, and a pole is exactly an off-critical zero.
So RH is now equivalent to: **`Im logDeriv XiC` is bounded above on the open half strip** (a pole
forces `+∞`, and nothing else can). That is a one-sided local boundedness statement about a harmonic
function with controlled boundary data — a Phragmén–Lindelöf-shaped problem rather than a
prime-domination problem.

**Next:** attack the half strip by harmonic-measure/Phragmén–Lindelöf reasoning. The needed input is
a growth bound on `Im logDeriv XiC` as `Re z → ±∞` inside the strip; the corpus already carries
Borel–Carathéodory machinery (`ArgumentVariation.borel_caratheodory`) and the certified `Λ₀` strip
bounds of 9bd, which are exactly the ingredients such an argument consumes.

### 9bl addendum — from a sign to a BOUND

`exists_im_logDeriv_gt_of_rightHalf_zero`: an off-critical zero yields, for EVERY level `C`, a point
inside the open upper half strip with `Im logDeriv XiC > C` (the ray below the conjugate copy, with
the pole term `m/t` unbounded and the analytic remainder continuous). Two criteria drop out:

**[THEOREM] `riemannHypothesis_of_im_logDeriv_bddAbove`** — if `Im logDeriv XiC ≤ C` on the open
half strip `{0 < Im z < ½}` for ANY constant `C`, then RH.

So RH is now equivalent to a ONE-SIDED BOUND, not a sign: **`Im logDeriv Ξ` bounded above on the
open half strip**. Nothing but a pole can break it, and a pole is an off-critical zero. Combined
with 9bl's two certified boundary facts (`≤ 0` on `Im z = ½`, `= 0` on `ℝ` by Schwarz reality) and
harmonicity in between, this is the exact hypothesis a Phragmén–Lindelöf argument consumes: on a
strip, a harmonic function bounded above with boundary values `≤ 0` and subexponential growth in
`|Re z|` is `≤ 0` throughout. The only missing input is that growth control.

**Novelty gate.** The Herglotz/Nevanlinna reformulation of RH is classical in spirit (`ξ′/ξ` maps the
upper half plane to the lower iff all zeros are real is the standard Hermite–Biehler picture, and de
Branges' programme lives here). Corpus-new: the exact reflection-paired trace identity that removes
the genus-one term, the machine-checked equivalence in both directions, and the reduction from a
sign to a one-sided bound with certified boundary data on both edges of the half strip.

## Step 9bm — Phragmén–Lindelöf is circular; the criterion becomes vertical monotonicity [PROVED]

**[NO-GO, by reasoning]** The PL plan of 9bl cannot work as stated. Phragmén–Lindelöf propagates
boundary bounds for functions HARMONIC on the whole strip; `Im logDeriv XiC` is harmonic on the half
strip only AWAY from its poles, and a pole is exactly the off-critical zero we are trying to exclude.
Near a pole the function takes both `+∞` and `−∞`, so it is not even subharmonic across it. Hence
"apply PL to get boundedness" presupposes the absence of poles — i.e. presupposes RH. Any growth
input would have to be established for a function not yet known to be harmonic there. Recording this
so the route is not re-attempted.

**[POSITIVE STATEMENT from the no-go]** The same object has an elementary reading. Along a vertical
line `∂_y log‖XiC(x+iy)‖ = −Im logDeriv XiC(x+iy)`, so the Herglotz sign condition of 9bl says
precisely that `y ↦ ‖XiC(x+iy)‖` never decreases. That turns the criterion from an analytic sign
into a GEOMETRIC monotonicity, and one direction becomes elementary:

**[THEOREM] `riemannHypothesis_of_norm_XiC_vertical_monotone`** — if for every real `x` the modulus
`y ↦ ‖XiC(x+iy)‖` is non-decreasing on `[0,∞)`, then RH. Proof: an off-critical zero (conjugated
into the upper half plane) sits at `x₀ + iy₀`, `y₀ > 0`, where the modulus is `0`, while
`exists_pos_norm_below_zero` (from the peel: zeros are isolated) gives `0 < y < y₀` with the modulus
POSITIVE. Monotonicity along that ray is then impossible.

Under RH the monotonicity is transparent: `‖Ξ(x+iy)‖` is a product of the distances
`√((x−tₙ)² + y²)` to the real zeros times a nonvanishing factor, and each distance increases in `y`.

**Why this matters.** The criterion is now a statement with no arithmetic and no analysis in it —
just: *the modulus of one entire function increases as you move up off the real axis.* Every earlier
formulation (Ward energy, Weil PSD, Herglotz sign, boundedness) has collapsed into this. It is also
the exact point where the classical de Branges/Hermite–Biehler programme lives, so the corpus is now
positioned on that frontier with machine-checked equivalences rather than informal ones.

**Next:** the converse direction (`RH ⟹ monotone`) via the identity
`d/dy ‖XiC(x+iy)‖² = −2‖XiC(x+iy)‖²·Im logDeriv XiC(x+iy)`, which needs the `y`-derivative of
`normSq ∘ XiC` — pure chain-rule work, no estimates — and would complete a two-sided
**RH ⟺ vertical monotonicity of `|Ξ|`**.
