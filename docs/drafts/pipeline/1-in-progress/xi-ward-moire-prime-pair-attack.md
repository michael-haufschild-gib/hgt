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
