# Wild conjectures from the GR / Wheeler–DeWitt lens (rh-corp × Giulini synthesis)

- **ID:** dewitt-gr-lens-conjectures
- **Stage:** 0-backlog (seed list — CANDIDATE conjectures, for shaping)
- **Type:** CANDIDATE × 3 — Door grades flagged per seed (EMBASSY / D2-candidate)
- **Source:** `../2-fully-proven/dewitt-supermetric-no-margin.md` (Giulini 2011) × `docs/rh-corp/` review (3 subagents, 2026-06-19); ../../door/bucket-time-and-non-holonomic-time.md
- **Why these three:** rh-corp has the *arithmetic* side richly (Hodge-index `(1,ρ−1)`, no-margin, type-III, info-geometric horizon) but **no Wheeler–DeWitt/supermetric material** (its "DeWitt" is a codename, theorist:336). The genuinely new lever is the **GR-side structure** Giulini supplies. Each seed below imports a GR tool onto the arithmetic wall. **Honesty constraint (rh-corp critic:1392, 2630):** the no-margin/positivity/index lane is RH-*equivalent* (≥8 names for one wall); none of these is sold as a C5 path — each is graded as a reframe whose value is **new tools / new cross-links**, not a bypass.

## Seed A — RH lives in the arithmetic scalar curvature (the subleading term after FE kills the kinetic term)
GR Hamiltonian constraint: `H = G_{abcd}π^{ab}π^{cd} − √h(R(h)−2Λ) = 0` — a **kinetic** DeWitt-metric term minus a **potential** = the **scalar curvature** `R(h)`. In the dictionary, the FE self-duality kills the *leading kinetic* form exactly as 4d-diffeo kills the ellipticity of `D_{λ=1}` (Finding 3); rh-corp's frame-5 says the RH-deciding sign then sits in the **subleading/anomaly term** (critic:1392). 
> **Conjecture A.** That subleading term is the arithmetic image of the **scalar curvature `R`** in the Hamiltonian constraint; RH ⟺ its positivity on the FE-fixed (critical) locus, after the kinetic `G`-term degenerates.
*Payoff:* imports the GR curvature-positivity toolkit (Hamiltonian-constraint `R`-term, Lichnerowicz–Yamabe, the `R(h)<0`-existence theorem Giulini uses p.3) onto the anomaly sign. *Grade:* EMBASSY / reframe-with-new-tools — RH-equivalent per critic:1392, but the GR identification of the subleading term with curvature is new. Ties to the cross-prime curvature `F_{pq}` (#118, RH-blind at generator level) — here the *archimedean-coupled* curvature (the seam), consistent with the project's localization.

## Seed B — the info-geometric horizon IS the DeWitt signature-change wall  `[RESOLVED → split out, 2026-06-19 DeWitt]`
> **Resolved & banked** as `../2-fully-proven/critical-line-fisher-signature-wall.md` (D2, BRIDGE substrate):
> `‖ψ‖²=ζ(2σ)` changes signature at `σ=½` (+/degenerate/ghost, verified), `g=(log ζ)''(2σ)∼1/(2σ−1)²`
> (verified `g·(2σ−1)²→1`); = Giulini's supermetric signature change; a **distinct** degeneracy from
> Finding 3's `λ=1` ellipticity (weight ⟂ position). RH-blind classical fact, not C5. (Seeds A, C remain open.)
rh-corp (theorist:1467): `‖ψ(s)‖²=ζ(2σ)` (>0 for `σ>½`, pole at `½`, ghost `σ<½`); quantum-Fisher/Fubini–Study metric `g=(log ζ)''(2σ) ∼ 1/(2σ−1)²` at `½` ⟹ **critical line = info-geometric horizon (infinite Fisher distance)**. Giulini (Finding 1): the DeWitt supermetric is **signature-changing, with regions where no metric exists** (Fig 1).
> **Conjecture B.** The arithmetic DeWitt-supermetric's signature change is exactly the **Fisher-information horizon** `g∼1/(2σ−1)²` at `σ=½`; the locus "no metric defined" (GR) = the infinite-Fisher-distance wall (arithmetic).
*Payoff:* identifies rh-corp's info-geometric horizon with Giulini's signature change — a concrete arithmetic realization of "regions where no metric exists." *Grade:* D2-candidate (cross-parent identification; survives the D2 strip if `1/(2σ−1)²` is the same degeneracy as `2(1−λ)→0`). To test: is the Fisher blowup the metric-degeneracy of the *same* supermetric `A−P`, or a different metric?

## Seed C — one clock: dBN heat-flow = Tomita modular flow = Connes scaling
Finding 3b (dBN heat-flow `H_t`) × rh-corp type-III spine (critic:1735, "type-III uniqueness-without-margin"; the clock = Tomita modular flow of a type-III₁ KMS state) × Connes' scaling action (zeros = absorption spectrum).
> **Conjecture C.** The de Bruijn time `t`, the **Tomita modular time** of the archimedean type-III₁ factor, and the Connes scaling flow are **one emergent WDW clock**. `Λ_dBN≥0` (Rodgers–Tao) = the **KMS/H-theorem entropy monotonicity** of the modular flow (measured/free half); **RH = modular faithfulness** (`κ₋=0`, the integer/upper half).
*Payoff:* unifies my dBN free/RH split (Finding 3b) with the operator-algebra "measured vs faithful" mechanism (critic:2605); feeds the time bucket's M1 (KMS/Bost–Connes, `β=½` self-dual). *Grade:* D2 / EMBASSY — substantiates `constraint-not-flow` (no Hamiltonian, only a modular constraint), but RH-equivalent.

**TEST DONE -> literal one-clock identification FALSIFIED (2026-07-13).**  Born `beta` is a state
label, Tomita `tau` is an automorphism parameter, and de Bruijn `t` deforms the function.  More
decisively, a modular automorphism is multiplicative while quadratic heat flow sends `X^2` to
`X^2+2t` and fixes `X`, so it is multiplicative only at `t=0`.  Formal proof and the positive
covariant-family replacement are recorded in
`../5-failed/born-modular-dbn-one-clock-identification.md`.

## Seed D — ζ as the no-boundary extremum of L-superspace  `[SPLIT OUT → own card, 2026-06-19]`
GR's "which entire geometries are admissible?" + Hartle–Hawking no-boundary = a **selection principle** for a
distinguished state. The banked supermetric work (`../2-fully-proven/dewitt-supermetric-no-margin.md`) shows ζ
*sits at* the kinetic degeneracy — a statement about **position** that **assumes** ζ. Seed D asks the prior
question — **why ζ** — variationally.
> **Conjecture D.** ζ is selected from the superspace of Dirichlet-series objects as the **no-boundary
> extremum** of an action; the genuine Euler product = the compactness/no-boundary closure (#81 fake-filter);
> **RH = the selected extremum has no unstable mode (`κ₋=0`)**; the no-margin (`Λ_dBN=0`) = marginal
> stability (infimum approached, not attained). Classical anchor: Nyman–Beurling / Báez-Duarte.
**Split to `no-boundary-selection-of-zeta.md`** (own backlog card). *Grade:* EMBASSY / D2-candidate; BRIDGE if
it reduces to Báez-Duarte. New vs the realization bucket (#84/#86): the **variational selection** framing.

## Seed E — the constraint-algebra structure functions live at the moment/ring-product level, not the generators (sharpens parent Finding 4)
GR's hypersurface-deformation algebra closes with **structure functions** (metric-dependent), making it a Lie
**algebroid**, not a Lie algebra — the algebraic root of many-fingered time. Parent **Finding 4** verified the
HGT *generators* are flat/abelian (`[σ_p,σ_q]=[σ_p,∂_s]=0`, #133/#136) — so **no** structure functions at the
generator level — and steers the obstruction to the **moment/ring-product level** `e_m·e_{m'}=e_{m+m'}`.
> **Conjecture E.** If a hypersurface-deformation-style structure-function algebra exists in HGT, it lives at
> the **ring-product/moment level**; its non-closure-on-constants (genuine structure *functions* there) is
> exactly **why `G_L` is a groupoid, not a group, and why the Langlands group `L_ℚ` (#28) resists an
> unconditional definition** — the algebroid obstruction = the curvature `F_{pq}` (N2) at the product level =
> the C5 locus Finding 4 points to (#104).
*Grade:* D2-candidate / new (algebroid framing absent from drafts). Premise refuted at the generator level
(Finding 4); redirected to the moment level. **Test:** compute the `{moment, moment}` bracket closure and
check for genuine structure functions (vs constants).

**TEST DONE → Seed E FALSIFIED (2026-06-19, DeWitt).** The moment algebra is the **commutative group algebra
`ℚ[ℤ^{(P)}]`**: `e_m·e_{m'}=e_{m+m'}=e_{m'+m}=e_{m'}·e_m`, so `[e_m,e_{m'}]=0` — **no structure functions at
the moment level either.** Combined with Finding 4 (`[σ_p,σ_q]=[σ_p,∂_s]=0`; diagonal action
`σ_p e_m=p^{−m_p}e_m`, `∂_s e_m=−(\log n)e_m`, `n=∏p^{m_p}`), the **entire HGT constraint algebra is
abelian/flat at every level** — generators, moments, and all cross-brackets commute. There is **no
hypersurface-deformation algebroid** in HGT, at any level. Seed E's conjecture is therefore **false**.

> **Positive content (BRIDGE, structural — the falsification's payload).** The groupoid-nature of `G_L` /
> the Langlands-group resistance is **NOT** a structure-function/algebroid phenomenon; it is the **corank ∞**
> (the infinite relation lattice, #125). The generator-curvature `F_{pq}=0` (flat); non-holonomicity is
> carried by the **infinite-rank relation lattice**, not by a non-abelian algebroid. This sharpens **N2**:
> "non-flat ⟺ non-holonomic" must be read as **corank**, not literal generator-curvature (which vanishes,
> Finding 4). The many-fingered-time obstruction is a *rank* phenomenon (∞ independent commuting clocks), not
> an *algebroid* phenomenon (no structure functions exist to close).

Door-2: the flatness/diagonality is `𝕋^∞` harmonic analysis (#136, a parent) ⟹ BRIDGE. Seed E → resolved
(falsified); Seeds A, C remain open EMBASSY (RH-equivalent reframes).

## Gates
- [ ] 0 → 1: pick one (Seed A is the most generative — it recruits a new toolkit; Seed E is the most native —
  it targets the moment-level C5 locus); pose precisely, source-pure, Door passport. Seed B is the cheapest
  D2 test (one metric-degeneracy comparison). Seed D is split to its own card.
- [ ] 1 → 2: …

## Cross-references
- `../2-fully-proven/dewitt-supermetric-no-margin.md` — the parent card (Findings 1–5); Seeds A/B/C extend Findings 3/1/3b respectively.
- `../2-fully-proven/constraint-not-flow-theorem.md` — Seed C's WDW-timelessness anchor.
- `../../door/bucket-time-and-non-holonomic-time.md` — M1 (KMS), the home for Seed C.
- `cross-prime-curvature-reducibility.md` (#118) — Seed A's curvature object (RH-blind at generator level; Seed A needs the archimedean-coupled curvature).

## Log
- 2026-06-19 — created in 0-backlog from the rh-corp × Giulini synthesis (3 opus subagents over `docs/rh-corp/`, spot-checked). Three GR-lens conjectures that rh-corp lacks (it has no WDW material). All graded honestly against rh-corp's own honest-kill (the no-margin lane is RH-equivalent): value = new GR tools / cross-links, not a C5 bypass. No web search.
- 2026-06-19 — added **Seed D** (ζ as the no-boundary extremum / variational selection; split to its own card
  `no-boundary-selection-of-zeta.md`) and **Seed E** (constraint-algebra structure functions at the
  moment/ring-product level, sharpening parent Finding 4's flat-generator dis-analogy → the groupoid/Langlands
  obstruction) from the GR-superspace chat thread. SO-1 check: a fourth proposed seed — the supermetric
  signature (1,∞) / `κ₋`=timelike / conformal=archimedean-time — was found **already fully banked** in
  `../2-fully-proven/dewitt-supermetric-no-margin.md` (Findings 1/2/3c/5) and **not** re-filed.
- 2026-06-19 (DeWitt) — **Seed E FALSIFIED** (the {moment,moment} test). The HGT constraint algebra is
  abelian/flat at every level (generators commute, Finding 4; moment algebra `ℚ[ℤ^{(P)}]` commutative;
  diagonal action) — no hypersurface-deformation structure functions / algebroid anywhere. Payload (BRIDGE):
  `G_L`'s groupoid-nature / Langlands-resistance and HGT non-holonomicity are the **corank ∞** (relation
  lattice), NOT a non-abelian algebroid; generator-curvature `F_pq=0`. Sharpens N2 ("non-flat⟺non-holonomic"
  = corank, not literal curvature). Seeds A, C remain open EMBASSY (RH-equivalent); card stays 0-backlog seed list.
- 2026-06-19 (DeWitt) — **Seed-E payload deepened → a foundational N2 clarification.** Chasing the
  flat-yet-non-holonomic tension: Finding 4 gives `[σ_p,σ_q]=[σ_p,∂_s]=0` ⟹ the arithmetic connection is
  **FLAT** (`F_pq=0`; the brackets genuinely vanish — `σ_p,σ_q` act on independent coordinates, and `σ_p` =
  the shift `s↦s+1` in the p-th coordinate, which commutes with `∂_s=d/ds`). Yet corank `=∞` (G3:
  `dim⟨g⟩`-closure `=∞`, dense in `𝕋^∞`). So the arithmetic system is a **flat connection with infinite
  (dense) holonomy** — like an irrational flow on a torus, **not** a bracket-generating sub-Riemannian
  distribution. **Correction to N2's framing:** "non-flat ⟺ non-holonomic" is misleading — the curvature is
  **zero** (flat / sub-Riemannian-integrable, brackets vanish); the non-holonomicity is the **infinite
  holonomy = corank ∞** (a *rank* phenomenon, the dense `⟨g⟩`-closure), not non-zero curvature. The two
  notions of "non-holonomic" — (i) bracket-generating/curvature [FALSE here] and (ii) infinite-holonomy/rank
  [TRUE here] — are distinct, and HGT is (ii), not (i). G3's "corank = dim⟨g⟩-closure" is the holonomy-group
  dimension; "holonomic ⟺ corank<∞" is the *finite-holonomy* statement, and the arithmetic extreme is
  **flat-with-infinite-holonomy**. (BRIDGE/structural: from banked Finding 4 + G3; the flat-but-infinite-holonomy
  reading is the clarification.)

## R13 finding (2026-06-20, novelty loop) — RH is an Aharonov–Bohm effect, not gravity: the lens is wrong because the connection is FLAT `[wild leap; voids Seed A]`

**Attack (the ticket's own Seed E kills Seed A).** GR's content is the scalar curvature `R(h)` in the
Hamiltonian constraint. Seed E PROVED the arithmetic connection is flat (`F_{pq}=0`, all brackets vanish). A
flat connection has no scalar curvature ⟹ **Seed A ("RH = positivity of the arithmetic `R`") is void** — it
asks RH to live in a zero object. Gravity is curvature; this system is flat. Wrong lens.

**The leap.** Flat connection + nonzero holonomy = **Aharonov–Bohm**, not gravity. Primes are flux lines
(flux `log p`); `π_1(𝕋^∞)=ℤ^{(P)}`; the holonomy rep is `ρ_s(p)=p^{−s}`, i.e. `n↦n^{−s}`, and
**`ζ(s)=Σ_n n^{−s}` = the regularized sum of Wilson loops** = the AB partition function; zeros = dark
interference fringes; RH = all fringes on one screen `Re s=½`.

**Invariant + payoff.** A flat connection's only invariant is its holonomy rep (no local invariant — curvature
≡0). So **RH is a topological/global (holonomy) invariant, and no local quantity can resolve it** — this is the
single deepest CAUSE of the RH-blindness pattern (#137; R09/R10/R11), unifying them as *flatness*. Predicts:
(i) curvature positivity (Seed A) void; (ii) the Fisher/DeWitt supermetric is a SEPARATE, curved, **RH-blind**
structure (`critical-line-fisher-signature-wall`, proven) — the GR lens conflates the two geometries; (iii) the
only RH-biting positivity is global/holonomy-type, and **Weil's explicit-formula form IS a prime/Wilson-loop
sum** (right kind), not a local energy; (iv) the correct lens is flat gauge theory / Wilson loops, in which
**RH = unitary holonomy on the FE-fixed locus = G5** becomes the *natural* statement.

**Structural separation (durable):** (A) the flat connection `(∂_s,σ_p)` — sole invariant holonomy →
RH-bearing, topological (AB), = G5; (B) the Fisher supermetric — curved but RH-blind. RH is in (A), not (B).
Full derivation + self-judgment (prior ~13, significance ~45, proof ~42) in
`logs/2026-06-20-novelty-generation-loop.md` Round 13.

**Forward lead:** off-line zeros as *fractional flux quanta* (AB phase ≠0 mod the FE period) — test whether
`κ₋` (off-line pair count, #32) is an AB winding/flux-quantum count.
