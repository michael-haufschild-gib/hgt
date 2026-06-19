# 00 — STATUS: everything we have, at a glance

**What this is.** One table of every statement in the field — lemma, theorem, conjecture, candidate,
falsified — with where it lives, what kind of thing it is, and how important it is. Built from the
buckets in this folder (which were sorted from `../support-extraction-log.md` + the charter).

**Two ways to use it.** (1) *"I want to prove something today — what can I pick?"* → jump to **§B Pick
something to prove**. (2) *"Is this a branch yet? How many conjectures are theorems? Do you have the
doors?"* → read **§A Scorecard**.

---

## Legend (so the table reads itself)

**Type — what kind of statement it is:**
| Tag | Means |
|---|---|
| `THEOREM (Lean)` | proven AND machine-checked, axiom-clean (the LEDGER) |
| `THEOREM (paper)` | proven on paper in the difference category / draft; not yet in Lean |
| `IMPORT` | a known classical theorem we borrow (named author) |
| `LEMMA` | a small proven support fact |
| `CONJECTURE` | open, clearly stated — **this is what you can try to prove** |
| `CANDIDATE` | a new conjecture *idea*, not yet fully posed — needs shaping first |
| `OPEN CORE` | the wall: the hard unsolved heart of a gatekeeper |
| `FALSIFIED` | shown false (kept for the record) |
| `FRAMING` | a physics/metaphor picture (embassy) — *not mathematics*, inspiration only |
| `BRANCH STATUS` | a charter criterion verdict (MET / PARTIAL / NOT MET) |
| `STRUCTURAL` | a synthesis/diagnosis, not a single provable statement |

**Priority — how big a deal it is:**
| Tag | Means |
|---|---|
| `FOUNDATIONAL` | branch-defining: needed to answer "is this a real branch of math?" Many are tractable. |
| `FUTURE` | a sibling / extension / nice-to-have. Often bite-size — good for a single session. |
| `FIELDS MEDAL` | proving it ≈ proving RH / DSS / Langlands. **Do not expect to finish it.** |

---

## §A Scorecard — *"Is this a branch? Do you have the doors?"*

**Branch verdict: NOT YET — it is a `proto-branch`.** It has native definitions and a precisely-located
problem, but **not one irreducible (C5) theorem** that a parent discipline couldn't also prove. Until
C5 is earned it is a *programme*, not a *branch*. (Charter Part IV.)

**The seven branchhood criteria:**
| C1 ontology | C2 category | C3 invariant | C4 problem | **C5 irreducible thm** | C6 bridge | C7 autonomy |
|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| ✅ MET | ✅ MET | ◐ PARTIAL | ✅ MET | ❌ **NOT MET (the gap)** | ✅ **MET** (bridge) | ❌ NOT MET |

**The doors (the litmus tests):**
| Door-1 object | **Door-2 load-bearing (master key)** | Door-3 native invariant | Door-4 native zone | Door-5 faithful restriction |
|:-:|:-:|:-:|:-:|:-:|
| ✅ pass | ⚠️ **re-test DONE — §59/§60 both FAIL → BRIDGE; C5 unearned** | ◐ partial | ✅ pass (for §59/§60) | ✅ pass (over `F_q`) |

> **The decision that moved everything (resolved 2026-06-19):** §59 (difference-Hölder = G1) and §60
> (corank dichotomy = G3) were tested against **Door-2** and **both FAIL** — stripped of the multi-q
> words their proofs are single-operator difference Galois + Kronecker–Weyl on `𝕋^∞` + unique
> factorization, none of it the native simultaneous-`σ_p` apparatus. They are **BRIDGE**, not NATIVE;
> **C5 is still unearned.** A real C5 theorem must use the `σ_p` jointly and irreducibly. See rows
> #6, #23, #50 and [[door-C5-irreducibility-and-door-2-retest]].

> **C6 (faithful bridge) resolved 2026-06-19 → MET (bridge level).** The three border specialization
> functors are built and verified (`../pipeline/2-fully-proven/c6-specialization-functors.md`): each
> recovers its parent on the overlap (single-prime = van der Put–Singer; function-field =
> Deligne–Papanikolas–Deligne–Katz; diagonal = Bohr–Kronecker), and `𝓜` **strictly extends** the
> single-prime border via the **proven** difference-Hölder theorem (G1: ζ is finite-base-holonomic at
> every finite truncation yet non-holonomic in the limit). This satisfies the charter's literal C6 test
> (recover **and** strictly extend). The *native/irreducible* strict extension (the cleanest one) = C5★,
> still open — so C6 is MET at bridge level, C5 stays the gap. See rows #47, #116.

> **Structural collapse note (2026-06-19):** C3-native, C6-native, and C7-native all reduce to **C5★**.
> The `Ш` gluing group gives the C3 cohomological face (BRIDGE, no surplus beyond `Ш_arith⟺C5★`), and
> bridge-level C7 autonomy is now proven. Thus C5★ is the single remaining lock behind native C3/C6/C7;
> C7 stays NOT MET until a Door-2-surviving flagship theorem exists.

**Gatekeeper scoreboard — how many foundational conjectures are theorems:**
| Gate | What | Best status today |
|---|---|---|
| **G1** | no single q-difference equation | ✅ **THEOREM (paper)**, difference category — Door-2: **BRIDGE** (not C5); multiplier-coboundary Source-A/B separator now proven (#134, BRIDGE), while the C5 weld remains open |
| **G2** | DSS (zeros independent) | ◐ **half**: upper bound proven; lower-bound architecture assembled (#7/#15/#18): A (Bombieri–Vaaler) discharged, B (zero estimate) restored as a BRIDGE theorem **along the canonical exhaustion `S_N={first N primes}`** (#14; PNT converts `P_S=p_N` to `N log N`), and C reduced to the named Schanuel-for-prime-logs / joint `{log p}∪{γ_n}` target; FF/Door-5 recovery via Papanikolas banked (#16); #103/#122/#124 bridges stand; the ℚ lower bound remains obstruction C |
| **G3** | holonomy ⟺ corank dichotomy | ✅ **THEOREM (paper)** — Door-2: **BRIDGE** (also fails Door-3) |
| **G4** | Picard–Vessiot / Langlands group | ◐ structurally built; FF Deligne–Katz recovery + weight-torus corank banked (#123, BRIDGE); `ω` localized as purely archimedean under SEED-R (#27/#71); `ω=0` open |
| **G5** | unitarity ⟺ RH (candidate) | ◐ finite anchors are **THEOREM (Lean)**; the infinite case is open core |

**Count:** **NATIVE/C5 theorems certified = 0** — the two leading candidates (§59, §60) were re-tested
and graded **BRIDGE**, so C5 stays open. Proved bridge theorems in the difference/completed-connection program = **4 (§59, §60, #134, #135)**;
machine-checked supporting theorems (Lean) = ~10 distinct statements (full list:
[[bucket-ledger-footholds]]). The five apex faces (RH, DSS, Langlands, realization, the archimedean
obstruction) are all **FIELDS MEDAL** and open.

> **Provenance / strategy correction (2026-06-19).** `docs/support-extraction-log.md` already contains the
> novelty audit that the pure positivity route collapses to the dBN/no-margin axis (`Λ≤0`) with no new
> mechanism (log L1430–1438). Treat exact finite-free / single-orbit positivity criteria (#104/#126), the
> no-margin rows (#89–#91), the face-orthogonality / three-cut rows (#54/#82), and the Pólya–Schur framing
> as proofs, localizations, or repackagings of mined log content unless a card explicitly supplies a new
> proof. Correction: Wheeler's gap-difference condition (GD) is not the exact Hermite tautology; it is a
> concrete non-tautological sufficient condition. DeWitt's near-resonance scorecard closed the proposed
> integer-gap C5 lane negatively: after normalizing by Hermite gaps, the `Δ_l` factor cancels, so
> `sup_t |Δε_l(t)|/Δ_l` is an upper-bound/large-values problem, not something the integer-gap separation
> bound closes. The support-`≤2d` near-resonance route is therefore `5-failed`; current grade is BRIDGE unless
> genuinely new non-parent large-values technology appears.
> This is leverage, not a free implication: DSS/genericity and RH/Li-positivity are separate faces
> (#54/#82), so do not read "RH as a corollary of DSS" as a proved implication.

---

## §B Pick something to prove — *"what could I work on today?"*

To actually work an item, open a card for it in the **pipeline** (`../pipeline/`, template
`../pipeline/_card-template.md`) and move it `0-backlog → … → 4-publication-ready`. Foundational topics
are now carded in the pipeline; §C rows carry the card links.

**Milestone 1 — "this is actually a branch."** Branchhood = all seven of C1–C7 MET (§A). C1/C2/C4 are
MET; **C6 is now MET (bridge level, 2026-06-19, below)**. The criteria each have a pipeline card:
- **C5** (irreducible theorem — the keystone, NOT MET): the finite-free / combination-mode lane remains
  active at `../pipeline/1-in-progress/combination-mode-baker-reducibility.md` and
  `../pipeline/1-in-progress/finite-free-convolution-flow.md`, but the exact positivity criterion is
  the already-mined dBN/no-margin axis. Wheeler's gap-difference condition (GD) is a non-tautological
  sufficient condition, yet DeWitt's `../pipeline/5-failed/c5-near-resonance-large-values.md` closes the
  support-`≤2d` near-resonance/integer-gap route negatively: normalized control of `Δε_l(t)` is a parent
  large-values upper-bound problem, so this lane does **not** supply C5.
- **C3** (native invariant, PARTIAL): **reduced to C5 (resolved 2026-06-19).** Cheap invariants proven
  BRIDGE (`../pipeline/2-fully-proven/c3-gluing-invariants-bridge.md`): joint gluing invariants exist
  (per-prime-equal yet jointly-distinct modules) but are all character-variety pullbacks; the only
  Door-3-surviving invariant is the arithmetic layer = **C5★**, so **C3-native ⟺ C5★** and closing C5
  closes C3. The independent-C3 goal failed (`../pipeline/5-failed/c3-native-invariant-door3.md`).
  Resolved follow-up: `multi-q-shafarevich-gluing-group.md` (2-fully-proven BRIDGE; rank-1 `Ш=0`,
  `Ш_const` is a non-split subobject via `ℂ↪𝒪`, arithmetic residue = C5★ by direct coboundary, no surplus).
  Remaining follow-up:
  `cross-prime-curvature-reducibility.md` (0-backlog; the curvature-language C5★ carrier).
- **C6** (faithful bridge): **MET (bridge level), resolved 2026-06-19**
  (`../pipeline/2-fully-proven/c6-specialization-functors.md`). The three border functors are built and
  each recovers its parent (single-prime = vdPS / function-field = Deligne–Papanikolas–Deligne–Katz /
  diagonal = Bohr–Kronecker); `𝓜` strictly extends the single-prime border via the **proven** difference-
  Hölder theorem (G1: ζ finite-base-holonomic but non-holonomic in the limit). The native/irreducible
  strict extension = **C5★**, still open.
- **C7** (autonomy, NOT MET): bridge-level autonomy is **proven** at
  `../pipeline/2-fully-proven/holonomicity-limit-nonclosure.md` (`𝓜 ≠ lim_T 𝓓_T`, BRIDGE); native autonomy
  remains `../pipeline/0-backlog/c7-autonomy-foundational-core.md` / **C5★**. Conjectural reduction:
  **C7-native ⟺ C5★**.

**Most leverage (a few sessions, not a lifetime):**
- **#6 / #23 / #50 — Door-2 re-test of §59/§60: DONE (2026-06-19).** Both FAIL → **BRIDGE**; C5 still
  unearned. The next C5 attempt must use the `σ_p` jointly and irreducibly (not the single shift
  `s↦s+1`). See [[door-C5-irreducibility-and-door-2-retest]].
- **#10 / #11 — formalize the DSS reduction** (`DSS ⟺ {π,ζodd,Stieltjes} indep`) + the conditional
  Nesterenko→DSS as Lean `Prop`s: `../pipeline/0-backlog/dss-reduction-formalize.md`.

**Bite-size & tractable (good single-session targets):**
- **#104 — finite-free convolution flow:** pinned carrier for the known positivity/no-margin axis
  (in-progress). The exact criterion is not C5 by itself; GD remains a non-tautological sufficient
  condition, but the near-resonance/integer-gap closure has failed (`../pipeline/5-failed/c5-near-resonance-large-values.md`):
  normalized gap control is a parent large-values upper-bound problem. #126 remains the BRIDGE/localization
  input for the gap shifts.
- **#59 — erosion threshold (G19):** write up `½ = the marginal-variance locus`; the hard analytics
  (Selberg/Ingham) are already theorems (#60).
- **#95 — is `Λ` (the dBN constant) a period?** `../pipeline/0-backlog/is-lambda-a-period.md`.
- **#19 — "a Baker for the Stieltjes constants":** reframed by #122/#124 as the joint
  `{log p}∪{γ_n}` obstruction-C target with explicit Nesterenko measure `H_C`; isolated
  `trdeg_ℚ{γ_n}=∞` phrasing is superseded: `../pipeline/1-in-progress/baker-for-stieltjes.md`.
- **#96 / #100 — shape a sibling into a real conjecture:** `../pipeline/0-backlog/lee-yang-localization.md`
  and `../pipeline/0-backlog/family-dss-gsh.md`.

**Heroic but well-posed (the gatekeepers' open cores — expect long campaigns):**
- **#15 / #18 — obstruction C / DSS-cross** (the joint Stieltjes/log side):
  `../pipeline/1-in-progress/g2-dss-lower-bound.md`; the Stieltjes sub-target is
  `../pipeline/1-in-progress/baker-for-stieltjes.md`.
- **#125 — corank as the unifying seam invariant:** `../pipeline/0-backlog/corank-seam-invariant.md`;
  the open content is a G1-anchored lower-bound realization of `corank=∞` across G1/G2/G4 over ℚ.
- **#127 / #128 — archimedean generator (consolidation + corank connector):** build
  `../pipeline/0-backlog/completed-connection-category.md` (the completed `(σ,∂)` connection #91 calls
  "the work no one has done"); lead falsifiable bet =
  `../pipeline/0-backlog/fields-medal-for-later/archimedean-corank-collapse.md` (`∂_s` = the
  product-formula relation collapsing ℚ-corank `∞→1`; missing single Frobenius `=∂_s`).
- **#27 — compute `ω ∈ H²(G_L)`** (Tannakian / motive / realization):
  `../pipeline/1-in-progress/compute-omega-h2-gl.md`; partial progress localizes `ω` to the
  archimedean regularization counterterm under SEED-R, but `ω=0` remains open.
- **#38 / #41 — the carrier infinite passage:** `../pipeline/0-backlog/weil-positivity-operator.md` and
  `../pipeline/0-backlog/carrier-herglotz-rh.md`.

**Do NOT pick to "finish" (FIELDS MEDAL):** any row tagged `FIELDS MEDAL` — RH itself in any of its 7
G5 faces, full DSS, the Langlands-group identity, the realization IFF. Chip at their *sub-lemmas*
instead.

---

## §C The full table

| # | Shortest version of what it is | Bucket | Type | Priority |
|---:|---|---|---|---|
| 1 | `{log p}` are ℚ-linearly independent | [[G1-difference-holder]] | THEOREM (Lean) | FOUNDATIONAL |
| 2 | each Euler factor solves a 1st-order q-difference eqn | [[G1-difference-holder]] | LEMMA | FOUNDATIONAL |
| 3 | ζ & all arithmetic L have **no** finite q-difference eqn | [[G1-difference-holder]] | THEOREM (paper) | FOUNDATIONAL |
| 4 | ζ satisfies no algebraic *differential* eqn (classical Hölder 1887) | [[G1-difference-holder]] | IMPORT | FOUNDATIONAL |
| 5 | differential Hölder for general L | [[G1-difference-holder]] | CONJECTURE | FUTURE |
| 6 | §59 Door-2 verdict — **BRIDGE, not NATIVE** (resolved; proof reduces to parents) | [[door-C5-irreducibility-and-door-2-retest]] | STRUCTURAL | FOUNDATIONAL |
| 7 | DSS: trdeg = orbit-dim ⟹ zeros independent — lower-bound architecture now assembled in `g2-dss-lower-bound.md`: A (Bombieri–Vaaler) discharged; B (uniform zero estimate) restored as **THEOREM (paper), BRIDGE** along the canonical exhaustion `S_N={first N primes}` (#14), with Lean anchors for the height/Vandermonde/order subclaims and PNT conversion still for Lean re-review; C reduced to the single named Schanuel-for-prime-logs bound; core lower bound remains open | [[G2-multi-q-siegel-shidlovsky]] | CONJECTURE | FIELDS MEDAL |
| 8 | upper bound trdeg ≤ dim G_M (T-up) — restricts along `S_ff` in the G2-over-`F_q` recovery of Papanikolas (#16; `g2-over-fq-papanikolas-dss.md`) | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper) | FOUNDATIONAL |
| 9 | diagonal orbit closure = `𝕋^∞` (orbit dim ∞, free) | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper) | FOUNDATIONAL |
| 10 | `P_k` closed form + Li↔secular ℤ change-of-basis — formalization card: `dss-reduction-formalize.md` | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (Lean) | FOUNDATIONAL |
| 11 | DSS = independence of `{π}∪{ζ(odd)}∪{Stieltjes γ_n}` — formalization card: `dss-reduction-formalize.md` | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper)+PSLQ | FOUNDATIONAL |
| 12 | Siegel's lemma in ∞ variables (obstruction A) = Bombieri–Vaaler | [[G2-multi-q-siegel-shidlovsky]] | IMPORT | FOUNDATIONAL |
| 13 | multi-q zero estimate, finite-S (obstruction B) — finite-S/order and per-form height anchors remain, and the G2-relevant diagonal wrapper is uniform along the canonical prime exhaustion `S_N` by #14; do not read this as uniform over arbitrary finite prime sets | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper) | FUTURE |
| 14 | uniformity of the zero estimate (Conj 5′, corrected domain) — **THEOREM (paper), BRIDGE**: the valid per-form height bound (`logPrime_height_bound`), Vandermonde moment core, and exponential-sum order wrapper give constants polynomial in `P_S`, the largest prime in `S`; the repaired statement restricts to the G2-relevant canonical exhaustion `S_N={first N primes}`, where PNT / Rosser–Schoenfeld gives `P_S=p_N≪N log N`, hence polynomial-in-`|S|` constants at fixed degree. Leaner's singleton `{p}` objection remains valid for arbitrary finite `S`, so the ledgered theorem is **canonical-exhaustion uniformity**, not all-finite-sets uniformity. Card: `../pipeline/2-fully-proven/zero-estimate-uniformity.md` | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper), BRIDGE | FUTURE |
| 15 | arithmetic of the L-values (obstruction C) — explicit form from #103 and assembled in #7/#18: at `s=1`, `F^{(T)}(1)=(-1)^TΣ_m λ_m(m·ℓ)^T/n_m`, a ℚ-linear form in degree-`T` prime-log monomials `∏_p(log p)^{a_p}`; the needed lower bound is effective algebraic independence of `{log p}` (quantitative Schanuel for prime logs), so the degree-`T` log-monomial linear form is the posed bound; difficulty is conserved (`T=1` linear/corank free, all `T` algebraic/Schanuel wall), with no bypass; card: `g2-dss-lower-bound.md` | [[G2-multi-q-siegel-shidlovsky]] | OPEN CORE | FIELDS MEDAL |
| 16 | full DSS over `F_q(t)` = Papanikolas — now recovered via `S_ff` + corank-1 collapse to a single-Frobenius `t`-motive (`g2-over-fq-papanikolas-dss.md`, Door-5 BRIDGE); over ℚ the lower bound remains obstruction C | [[G2-multi-q-siegel-shidlovsky]] | IMPORT + THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 17 | edge value transcendence at `s=1` = Baker | [[G2-multi-q-siegel-shidlovsky]] | IMPORT | FUTURE |
| 18 | DSS-cross obstruction C — reframed by #103/#122/#124 from isolated `{γ_n}` independence to the joint Schanuel-entangled target `trdeg_ℚ ℚ({log p}∪{γ_n})=∞`, with `γ_n` contributing beyond the prime-log field; explicit friable-auxiliary linear form is `F^{(T)}(1)` in degree-`T` prime-log monomials; residual = missing-F₁ / infinite-corank wall; provenance: this Stieltjes/log wall is already mined in `support-extraction-log.md` #72/#74/#128, so current cards are proofs/repackagings of known log content, not new discovery; card: `g2-dss-lower-bound.md` | [[G2-multi-q-siegel-shidlovsky]] | OPEN CORE | FIELDS MEDAL |
| 19 | a "Baker for the Stieltjes constants" — now the `s=1` route to the joint obstruction-C measure `H_C` on `{log p}∪{γ_n}`; FF exact case + feeding mechanism + upper bound are proven BRIDGE (#122), and #124 proves nontrivial friable auxiliaries cannot isolate a clean `γ_n`-only lower bound; provenance: re-derives/sharpens `support-extraction-log.md` #72/#74/#128, where DSS was already the joint Stieltjes/log Schanuel-type wall; card: `baker-for-stieltjes.md` | [[G2-multi-q-siegel-shidlovsky]] | CONJECTURE | FUTURE |
| 20 | holonomic ⟺ `corank(Λ)<∞` (corank dichotomy) | [[G3-holonomy-dichotomy]] | THEOREM (paper) | FOUNDATIONAL |
| 21 | pro-torus inverse problem `dim=corank` (P3) | [[G3-holonomy-dichotomy]] | THEOREM (paper) | FOUNDATIONAL |
| 22 | solvability (not abelianness) ⟺ `L=0` (DMR) | [[G3-holonomy-dichotomy]] | THEOREM (paper) | FOUNDATIONAL |
| 23 | §60 Door-2 verdict — **BRIDGE** (also fails Door-3) (resolved) | [[door-C5-irreducibility-and-door-2-retest]] | STRUCTURAL | FOUNDATIONAL |
| 24 | infinite-base Galois correspondence — specializes via `S_ff` in #123 to recover Deligne–Katz monodromy and the weight/angle split | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (paper) | FOUNDATIONAL |
| 25 | inverse-Galois: `R_multi = {G:π₀ finite abelian}` | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (paper) | FOUNDATIONAL |
| 26 | Satake λ-ring algebra (⊗,⊕,Adams,plethysm,e–h) | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (Lean) | FOUNDATIONAL |
| 27 | `ω=0` ⟺ Tannakian ⟺ motive exists ⟺ realization — **partial progress (SEED-R-conditional BRIDGE):** the unregularized ∞-prime Koszul complex is acyclic (`H(t)E(−t)=1` in `Λ`, finite shadow `eh_koszul_duality`), so the multiplicative shadow of `ω` vanishes and any nonzero `ω` is carried entirely by the archimedean Γ-factor/`s=1` regularization counterterm; compute-`ω` reduces to a purely archimedean Koszul-homology defect, while core `ω=0⟺RH` stays open; provenance: the conclusion "ω is purely archimedean" is already `support-extraction-log.md` #90 / Attack 6, while §R supplies a new proof mechanism, not a new conclusion; card: `compute-omega-h2-gl.md` | [[G4-multi-q-picard-vessiot-and-langlands-group]] | OPEN CORE | FIELDS MEDAL |
| 28 | `G_𝒜` = the Langlands group `L_ℚ` — card: `compute-omega-h2-gl.md` | [[G4-multi-q-picard-vessiot-and-langlands-group]] | CONJECTURE | FIELDS MEDAL |
| 29 | Rankin–Selberg = ⊗ (unramified places) | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (paper) | FUTURE |
| 30 | G4 over `F_q` = Deligne–Katz — native Door-5 recovery done in #123 via `S_ff`; `dim W=corank(Λ_ff)=1` identifies the weight torus, while geometric monodromy is the angle face | [[G4-multi-q-picard-vessiot-and-langlands-group]] | IMPORT | FOUNDATIONAL |
| 31 | σ-fixed-modulus locus = the critical line (Lemma 1) | [[G5-unitarity-gatekeeper]] | LEMMA | FOUNDATIONAL |
| 32 | `κ₋` = #off-line zero-pairs, **exactly** (finite carrier) | [[G5-unitarity-gatekeeper]] | THEOREM (Lean) | FOUNDATIONAL |
| 33 | `m_ξ` Herglotz (`κ₋=0`) ⟺ RH (carrier form) — card: `carrier-herglotz-rh.md` | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 34 | CMV operator unitary ⟺ `|γ_k|<1` ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE+numeric | FIELDS MEDAL |
| 35 | `ι=κ` (FE-involution = adjoint) ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 36 | secular Jacobi / Berry–Keating self-adjoint ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 37 | Hodge–Riemann `Q_W⪰0` (Weil rep of `SL₂`) ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 38 | `H_W=−Δ_prime+V_arch ≥ 0` ⟺ RH (operator built; domination open) — card: `weil-positivity-operator.md` | [[G5-unitarity-gatekeeper]] | OPEN CORE | FIELDS MEDAL |
| 39 | HP = gen(`G_L`), `[D,P]=0` ⟺ RH (mean rigorous) — card: `weil-positivity-operator.md` | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 40 | unitary holonomy of completed flat connection ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 41 | the infinite passage (lift finite carrier to actual ξ) — card: `carrier-herglotz-rh.md` | [[G5-unitarity-gatekeeper]] | OPEN CORE | FIELDS MEDAL |
| 42 | C1 native ontology — **MET** | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 43 | C2 native category — **MET** | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 44 | C3 native invariant — **PARTIAL → reduced to C5** (resolved 2026-06-19): cheap invariants proven BRIDGE (#115); native invariant ⟺ C5★; independent goal failed (`../pipeline/5-failed/c3-native-invariant-door3.md`) | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 45 | C4 native problem — **MET** | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 46 | C5 irreducible theorem — **NOT MET** (the gap); exact finite-free/combination-mode positivity is provenance-graded as the known dBN/no-margin axis. Wheeler's gap-difference condition (GD) is non-tautological, but the proposed support-`≤2d` near-resonance/integer-gap route to control `Δε_l(t)/Δ_l` is now **failed** (`../pipeline/5-failed/c5-near-resonance-large-values.md`): after gap normalization the problem is a parent large-values upper bound. Cross-prime curvature reducibility is also **BRIDGE / RH-blind** (#118), the archimedean×prime FE-conspiracy cocycle is **BRIDGE** (#135), and the `(σ_p,∂_s)` generator/connection level is Fourier-diagonal BRIDGE (#136). Thus no C5 theorem is banked in reducibility, FE/factorization, or generator structure; the live C5 loci are moment/product positivity (finite-free Hankel, #104) and global G5 positivity / unitary holonomy of the completed `(σ,∂)` connection (#38/#127). | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 47 | C6 faithful bridge — **MET** (bridge level, 2026-06-19): three border functors built; recover vdPS / Deligne–Papanikolas–Deligne–Katz / Bohr–Kronecker; `𝓜` strictly extends single-prime via proven G1 (#116); native extension = C5★ (`../pipeline/2-fully-proven/c6-specialization-functors.md`) | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 48 | C7 autonomy — **NOT MET**; bridge-level autonomy proven (#119: `𝓜 ≠ lim_T 𝓓_T`, BRIDGE), but native autonomy remains `../pipeline/0-backlog/c7-autonomy-foundational-core.md` / **C5★**; conjectural reduction **C7-native ⟺ C5★** | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 49 | σ-parity = FE-parity weld (Lean foothold); cross-term Door-2 lens (#135) reads the prime-lane parity `θ_p↦−θ_p` as the free zero-blind multiplicative involution, while the archimedean surplus is the Source-A-alone `χ`, so any native surplus is doubtful / flagged for team confirmation rather than banked as C5 | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (Lean) | FOUNDATIONAL |
| 50 | Door-2 re-test of §59/§60 — **DONE: both BRIDGE; C5 open** | [[door-C5-irreducibility-and-door-2-retest]] | STRUCTURAL | FOUNDATIONAL |
| 51 | carrier germ: RH = global type, DSS = infinite jet (one object) — card: `a1-a2-unification-brick.md` | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 52 | ridgeline: boundary rep unitary ∧ faithful (no-margin = faithful) — card: `a1-a2-unification-brick.md` | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 53 | period matrix Π: RH = purity, DSS = period-fullness — card: `a1-a2-unification-brick.md` | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 54 | Face A ⊥ Face B (orthogonality theorem) — provenance: largely re-derives `support-extraction-log.md` #75/B29 (`(E)/(A)/(P)` cuts, positivity does not imply genuineness) plus G10/#84 framing; read as proof/repackaging, not new discovery; card: `faces-orthogonality.md` | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FUTURE |
| 55 | secular point in Li-cone AND generic (cone∩generic) — card: `a1-a2-unification-brick.md` | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 56 | `Z_n ≻ A_n` (Ω_∞≻Π) ⟺ RH (explicit Li coords) — card: `a1-a2-unification-brick.md` | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE+numeric | FIELDS MEDAL |
| 57 | μ pseudorandom = RH + LI (one statement) — card: `a1-a2-unification-brick.md` | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 58 | both finite layers ledgered (`κ₋` + esymm indep) | [[bucket-A1-A2-unification-the-carrier]] | THEOREM (Lean) | FOUNDATIONAL |
| 59 | `½` = erosion threshold of the ∞-frequency cocycle (G19) — **in progress**; backbone (#110) returned to `0-backlog-lean` for a variance-normalization mismatch; 19a cocycle reducibility (#111) proven; open: 19b; provenance: Selberg/marginal-regime content was already mined in `support-extraction-log.md` #87 §12, so this is a write-up/proof-localization lane | [[bucket-time-and-non-holonomic-time]] | CONJECTURE | FUTURE |
| 60 | marginal regime = Selberg CLT / Keating–Snaith | [[bucket-time-and-non-holonomic-time]] | IMPORT | FUTURE |
| 61 | non-holonomic = no native clock (Hölder = WDW timelessness) | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 62 | HP = a **constraint**, not a Hamiltonian | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 63 | equidistributed clock ⟺ timelike ⟺ on-line zeros | [[bucket-time-and-non-holonomic-time]] | CONJECTURE | FUTURE |
| 64 | `Λ_dBN` = arrow of time / transcendence clock | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 65 | FE = a handshake across time (absorber/two-state) | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 66 | no-margin = clock marginally null (light-cone) | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 67 | primes = CTCs, zeros = time-crystal, BH/causal-set | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 68 | the seam = the period / non-period divide; `corank` is the shared readout across G1 holonomicity (#121), G2 period-transcendence (#16/#122/#124), G4 weight torus (#123), and the archimedean obstruction; row #125 gives the corank-number pipeline home | [[bucket-the-seam-archimedean-obstruction]] | STRUCTURAL | FOUNDATIONAL |
| 69 | both apex faces = **ONE** archimedean obstruction; finite-free realization = archimedean margin `A_d` vs joint-prime fluctuation `δH_d` race (#104); seam-corank conjecture (#125): `corank(Λ_ℚ)−corank(Λ_ff)=∞−1`, equivalently `ζ` non-holonomic ⟺ no single Frobenius ⟺ seam non-trivial; G2/DSS lower-bound rigidity is the same corank gap (FF corank 1 gives Papanikolas, ℚ corank ∞ gives obstruction C); G4 group face reads the gap as `dim W=1` over `F_q` versus conjectural archimedean weight corank ∞ over ℚ (#123); unified split form: the seam is the obstruction to a σ-equivariant splitting of the σ-invariant/archimedean part from the mean-zero/prime part, seen as non-split `Ш_const` (#117), Stieltjes-log weld/no-isolation (#19/#122/#124), and finite-free `A_d^{-1}` spectral coupling (#104); #125 is the corank-number view complementary to the split-obstruction view | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
| 70 | missing Frobenius = F₁ = three names (B24=B8=DSS); on the G2 face, single-Frobenius rigidity is exactly the Papanikolas/ABP lower bound over `F_q`, absent over ℚ | [[bucket-the-seam-archimedean-obstruction]] | STRUCTURAL | FOUNDATIONAL |
| 71 | `ω=0` ⟺ D trace-class ⟺ HP ⟺ RH (unifies 5 programs); finite-free seam face = the σ-invariant average `A_d=E_tH_d(t)` coupled to `δH_d` through the relative metric `A_d^{-1}` (#104); G2 seam face = Stieltjes continuation data failing to decouple from `{log p}` (#19/#122/#124); C3 seam face = `Ш_const` non-split because there is no σ-fixed torus point (#117); G4 seam face = weight torus `W` has `dim W=corank=1` over `F_q` and conjectural corank ∞ over ℚ (#123), plus #27's SEED-R localization of `ω` as a purely archimedean class after the multiplicative Koszul part vanishes; provenance: `support-extraction-log.md` #90 / Attack 6 already names the archimedean/F₁ trace-defect interpretation; card: `compute-omega-h2-gl.md` | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
| 72 | two towers (spectral dead, motivic live) = the seam | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FUTURE |
| 73 | superzeta = additive resolvent trace (Σ, not ∏) | [[bucket-the-seam-archimedean-obstruction]] | THEOREM (Lean) | FOUNDATIONAL |
| 74 | multiplicative-only methods are apex-blind (structural) — now has a cohomological proof for the realization obstruction under #27 §R: `ω∈H²(G_L)` is invisible to Euler/Satake/multiplicative Koszul data, so any nonzero obstruction lives in the archimedean regularization counterterm | [[bucket-the-seam-archimedean-obstruction]] | STRUCTURAL | FOUNDATIONAL |
| 75 | regularization is transcendence-creating (G16 freshness) — **CONJECTURE (native), structural BRIDGE backbone, 1-in-progress**: "fresh" means algebraic independence from the `MT(ℤ)` period algebra (DSS-cross); R2 proves structurally that `γ_n = lim_m[Σ_{k≤m}(log k)^n/k - ∫_1^m (log x)^n/x dx]`, so `γ_n` is the regularized discrete–continuous defect, i.e. the archimedean–arithmetic seam made into a number; freshness is equivalent to the seam/F₁ being non-trivial, hence to the obstruction-C / Schanuel-for-prime-logs wall on the regularized limit; provenance: the Stieltjes/no-motive and Schanuel-type target is already `support-extraction-log.md` #72/#74/#128; transcendence itself remains open; card: `regularization-freshness.md` | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FUTURE |
| 76 | keystone over `F_q` = Grothendieck; FF campaign: G1 resolved by corank-collapse degeneration (#121), G2/DSS recovered via Papanikolas under `S_ff` (#16), G3 trivial at corank 1, G4 Deligne–Katz recovered via `S_ff` with `dim W=corank=1` (#123); remaining native reproof G5 stays in `function-field-native-reproof.md` | [[bucket-function-field-proving-ground]] | IMPORT | FOUNDATIONAL |
| 77 | RH over `F_q` = Deligne (Weil II) | [[bucket-function-field-proving-ground]] | IMPORT | FOUNDATIONAL |
| 78 | Weil FE of the L-polynomial | [[bucket-function-field-proving-ground]] | THEOREM (Lean) | FOUNDATIONAL |
| 79 | CM/non-CM = rotation / almost-Mathieu cocycle dichotomy | [[bucket-function-field-proving-ground]] | THEOREM (paper)+cert | FUTURE |
| 80 | the bracket: 2 solved corners vs 2 open apexes | [[bucket-function-field-proving-ground]] | STRUCTURAL | FUTURE |
| 81 | First Theorem: Euler product ⟺ Bohr factorization (fake filter) | [[bucket-realization-and-fake-family]] | THEOREM (Lean) | FOUNDATIONAL |
| 82 | three cuts (E)/(A)/(P): positivity ≠ genuineness — provenance: this is `support-extraction-log.md` #75/B29 content, a governing filter for positivity claims rather than a new conclusion | [[bucket-realization-and-fake-family]] | THEOREM (paper) | FOUNDATIONAL |
| 83 | Spectral Torelli: `{s_m}` determine ξ | [[bucket-realization-and-fake-family]] | THEOREM (Lean, finite) | FOUNDATIONAL |
| 84 | overdetermination locus = genuineness (G17) — card: `realization-problem.md` | [[bucket-realization-and-fake-family]] | CONJECTURE | FUTURE |
| 85 | off-line Beurling systems exist ⟹ RH non-generic | [[bucket-realization-and-fake-family]] | IMPORT | FOUNDATIONAL |
| 86 | realization problem: is Euler ⟺ two-faces an **IFF**? (#7) — card: `realization-problem.md` | [[bucket-realization-and-fake-family]] | CONJECTURE | FIELDS MEDAL |
| 87 | superzeta is a "fake" (no Euler product) | [[bucket-realization-and-fake-family]] | THEOREM (paper) | FUTURE |
| 88 | moment positivity ⇏ frequency positivity (N6, witness) | [[bucket-realization-and-fake-family]] | THEOREM (paper) | FOUNDATIONAL |
| 89 | no-margin = one missing uniform bound (4 coordinates); concrete finite-free form is the relative metric race `S_d=A_d^{-1/2}δH_dA_d^{-1/2}` with floor `λ_min(S_d)≥−1` (#104); provenance: `support-extraction-log.md` #89/Part XI and #77 Thm 7 already establish the no-margin phenomenon, so #104 localizes it rather than discovering it — card: `no-margin-uniform-bound.md` | [[bucket-the-no-margin]] | OPEN CORE | FOUNDATIONAL |
| 90 | two-rate signature: margin ~ δ, cost ~ log(1/δ) — provenance: already mined in `support-extraction-log.md` #89/Part XI / #77 Thm 7; current uses are proofs/localizations of prior log content — card: `no-margin-uniform-bound.md` | [[bucket-the-no-margin]] | THEOREM (paper) | FOUNDATIONAL |
| 91 | off-line zero breaks TP at order→∞, magnitude→0 (Thm 7) | [[bucket-the-no-margin]] | THEOREM (paper) | FOUNDATIONAL |
| 92 | RH ⟺ `Λ=0`; Rodgers–Tao `Λ≥0` (the FE-forced half) | [[bucket-the-no-margin]] | IMPORT (half) + CONJECTURE | FIELDS MEDAL |
| 93 | no-margin = an exceptional point (PT-unbroken) | [[bucket-the-no-margin]] | CONJECTURE+cert | FUTURE |
| 94 | no-margin = the Law of the Iterated Logarithm | [[bucket-the-no-margin]] | STRUCTURAL | FUTURE |
| 95 | is `Λ` itself a period / transcendental? — card: `is-lambda-a-period.md` | [[bucket-the-no-margin]] | CONJECTURE | FUTURE |
| 96 | Lee–Yang localization (RH = marginal-crystalline) — card: `lee-yang-localization.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 97 | FE ⟺ measure is a Fourier quasicrystal — card: `fe-fourier-quasicrystal.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 98 | RH lives only on the pure+polarized locus (G9) — card: `intrinsic-rh-locus-pure-polarized.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 99 | Koszul-acyclicity ⟺ Tannakian/RH (G15) — card: `koszul-acyclicity.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 100 | family-DSS = the Grand Simplicity Hypothesis (G13) — card: `family-dss-gsh.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FIELDS MEDAL |
| 101 | Tate–prime rigidity weld (G12) — card: `tate-prime-rigidity.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 102 | live motivic period tower (SEED-U) — card: `motivic-period-tower.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 103 | friable Dirichlet polynomial = native auxiliary (N5) — **THEOREM (paper), BRIDGE**: object built as the diagonal native auxiliary space; pillar A (Bombieri–Vaaler height) is discharged, and pillar B is restored through #14 as the canonical-exhaustion zero estimate (`S_N={first N primes}`, PNT `p_N≪N log N`; not arbitrary finite `S`). With A and B discharged, obstruction C is reduced at `s=1` to the explicit degree-`T` prime-log monomial lower bound, i.e. effective algebraic independence of `{log p}` / quantitative Schanuel for prime logs; residual C-bound remains open. Lean anchor `iteratedDeriv_friableExponentDirichletExp_at_one` remains valid; Lean re-review now also needs the PNT conversion for B. Provenance: headline Schanuel-for-prime-logs obstruction and smooth-number auxiliary were pre-named in `support-extraction-log.md` (L128, L389), while the explicit `s=1` mechanism and no-bypass/surjectivity proof are new; card: `../pipeline/2-fully-proven/friable-dirichlet-auxiliary.md` | [[bucket-new-sibling-conjectures]] / [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 104 | finite-free / Hankel carrier (degree-`d` section of `Ξ`) — reducibility **resolved** (σ>¾, RH-blind, #120); exact single-orbit positivity of `det H_d` is equivalent to hyperbolicity (`λ_min(S_d(t))≥−1 ∀d,t`) and is the already-mined dBN/no-margin axis. Wheeler's **gap-difference condition (GD)** is a stronger, non-tautological sufficient condition: `sup_t|ε_l(t)−ε_{l+1}(t)|<Δ_l` for all adjacent Jensen roots; with #126, `Δε_l(t)=Σ_p p^{-1/2}e^{-it\log p}[K_d(r_l;p)−K_d(r_{l+1};p)]`. DeWitt's scorecard closes the integer-gap route negatively: in `Δε_l/Δ_l` the gap factor cancels, so the required upper bound is parent large-values/BRIDGE, while support-`≤2d` near-resonance controls only RH-blind separation/variance (`../pipeline/5-failed/c5-near-resonance-large-values.md`). Together with #135/#136, FE/factorization and generator-level carriers are BRIDGE; if C5 is earned here, it must be at the moment/product positivity level (Hankel `P_{i+j}` / ring products), not by local generators or cocycles. | [[door-C5-irreducibility-and-door-2-retest]] | CONJECTURE | FOUNDATIONAL |
| 105 | positive direction strength = exactly 1 (Tamagawa, SEED-B) — card: `tamagawa-strength-one.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 106 | seam firewall: finite-place ⊥ archimedean positivity (SEED-A) — **THEOREM (paper), BRIDGE**: the algebraic firewall holds at the difference-Galois generator level, so finite-place generator data does not force the archimedean positivity. Operational hook = the CC / σ-orbit-balance class (#130/#134): the prime block is all-CC, Fourier-diagonal, and FE-null (#135/#136), while the archimedean block is the unique non-CC Source-A place carrying `[χ]` / `ω` (#27/#135). The prime block contributes null to every cross-obstruction: FE-cocycle (#135), curvature/reducibility (#118), `ω` (#27), and generator-level combination modes (#136). Thus `ind(D)` is purely archimedean and the positivity residual is the G5/moment apex, not a sub-apex seam route. Door-5: vacuous over `F_q` (all CC), so this is precisely what ℚ adds. Card: `../pipeline/2-fully-proven/seam-firewall.md` | [[bucket-new-sibling-conjectures]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 107 | transcendence ⟹ GUE statistics (B11) — **REFUTED as stated**: family-DSS/transcendence does not imply full GUE; small-scale sine-kernel is prime/explicit-formula-forced, while transcendence/GSH controls only the large-scale non-resonance. Surviving scale-decomposition is a corollary of faces-orthogonality propagated to `R_k`, not a standalone theorem; failed card: `../pipeline/5-failed/transcendence-implies-gue.md` | [[bucket-new-sibling-conjectures]] | FALSIFIED | — |
| 108 | HP operator "can't be too algebraic" (B18) — card: `hp-not-too-algebraic.md` | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 109 | a profinite Galois group acts on the zeros (B24) | [[bucket-new-sibling-conjectures]] | FALSIFIED | — |
| 110 | Re=½ = abscissa of a.s. convergence of the random Euler product (G19 backbone) — **review fixes applied 2026-06-19** (`V ~ log(1/(2σ−1))`; the `½` is `Var(Re 𝓛)=½V`, exact; divergence via Mertens), numerically certified, ready for Lean; provenance: Selberg/CLT/extremes/marginal-regime framing was already `support-extraction-log.md` #87 §12, so this row is a proof/write-up of prior mined content (`../pipeline/0-backlog-lean/critical-line-abscissa-of-convergence.md`) | [[bucket-time-and-non-holonomic-time]] | THEOREM (paper) | FUTURE |
| 111 | Euler cocycle reducible (L²-coboundary) over 𝕋^∞ iff σ≥½ (G19/19a; Door-2 BRIDGE, axis-mode) | [[bucket-time-and-non-holonomic-time]] | THEOREM (paper) | FUTURE |
| 112 | Baker load-bearing for mixed-sign combination-mode reducibility (finite base; Liouville counterexample) | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 113 | C5★-as-reducibility **RESOLVED & RH-blind** (threshold σ>¾, #120); reducibility⟺RH **refuted** (σ=½ non-reducible); RH **relocated** to single-orbit positivity (#104). Cocycle reducibility was the wrong handle | [[door-C5-irreducibility-and-door-2-retest]] | STRUCTURAL | FOUNDATIONAL |
| 114 | Hankel ↔ combination-mode degree lemma: under axis-mode secular data, the degree-d real-rootedness certificate (det H_j) has Fourier support ≤ j ≤ d, attained — **not axis-mode for d≥2** (genuine mixed-sign cross-prime modes); fixed-d Baker exponent (≤d logs) | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 115 | joint gluing invariants exist (per-prime-equal yet jointly-distinct modules; rank-2 two-prime witness) but all are character-variety pullbacks ⟹ BRIDGE; native invariant ⟺ C5★ (the C3 dividing line) | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 116 | three border specialization functors (C6 MET, bridge): each recovers its parent (single-prime=vdPS / function-field=Deligne–Papanikolas–Deligne–Katz / diagonal=Bohr–Kronecker); `𝓜` strictly extends single-prime via proven G1 (finite-base-holonomic but non-holonomic limit); native extension = C5★ | [[bucket-function-field-proving-ground]] | THEOREM (paper) | FOUNDATIONAL |
| 117 | multi-q Shafarevich gluing group `Ш(M)=ker(joint H¹→∏ per-prime H¹)` — **THEOREM (paper), BRIDGE**: canonical Tate–Shafarevich cohomological home of the C3 invariant; rank-1 abelian `Ш≡0` by semisimplicity; `Ш_const` is a constant-representable **non-split subobject** via the equivariant inclusion `ℂ↪𝒪` (Procesi/character variety BRIDGE), with no equivariant ring retraction `𝒪→ℂ` and no augmentation exact sequence; arithmetic residue = C5★ by direct coboundary; no Door-3-surviving surplus beyond C5★, collapse invisible below rank 2 | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 118 | cross-prime curvature reducibility — **THEOREM (paper), BRIDGE / RH-blind (terminal)**: for the minimal rank-2 unipotent extension `A_p=I+b_pE` (`E²=0`), `F_{pq}=I+φ_{pq}E` with `φ_{pq}=(1-σ_q)b_p-(1-σ_p)b_q` (discrete curl); genuine support-2 mixed-sign combination modes appear when `b_p` is cross-dependent (Door-1/4), while constant `b_p` is flat/BRIDGE (#115). Trivializability is the coboundary condition `b_p=(σ_p-1)f`, equivalently the same `L²` small-divisor / uniform-Baker reducibility problem as #111/#113; by faces-orthogonality (#54), this is an A2 integrability/variance handle and is RH-blind, not a second C5 carrier. Arithmetic residue remains C5★; verdict module-independent. Card: `../pipeline/2-fully-proven/cross-prime-curvature-reducibility.md` | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 119 | holonomicity not closed under the border inverse limit — **THEOREM (paper), BRIDGE**: for diagonal `M=lim_T S_T(M)`, holonomic ⟺ `corank(Λ_M)<∞` ⟺ finite-slice coranks `c_T` stabilize; every finite truncation is holonomic, and `M_ζ` shows the comparison `𝓜→lim_T𝓓_T` does not reflect holonomicity (`𝓜 ≠ lim_T𝓓_T`); banks bridge-level C7, while **C7-native ⟺ C5★** remains the reduction; FF border specialization (#121) identifies the two regimes as number-field `corank=∞` vs function-field `corank=1` | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 120 | d→∞ finite-free **edge reducibility threshold**: the coboundary norm `Σ|ĝ(m)|²/|m·ℓ|²` converges **iff σ>¾**; consecutive-/balanced-integer-driven, **Baker-free** (elementary integer-gap bound), and **RH-blind** (`𝕋^∞`-variance) — proven, conditional on the explicit-formula coefficient model | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 121 | function-field holonomicity degeneration — **THEOREM (paper), BRIDGE**: over `F_q(C)`, every place-dilation `g_v=q^{−deg v}` is a power of one unit, so `Λ_ff=ker(deg)` and `corank(Λ_ff)=1`; the `σ_v` tower collapses to `u=q^{−s}`; `ζ_C` is holonomic (Weil), so difference-Hölder/non-holonomicity and the jump `𝓜≠lim 𝓓_T` (#119) are number-field-only; corank `1` (FF) vs `∞` (ℚ) is #119's border dichotomy; seam-corank identity remains conjectural | [[bucket-function-field-proving-ground]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper) | FOUNDATIONAL |
| 122 | corank–transcendence identity for L-function continuation data — **THEOREM (paper), BRIDGE**: exactly over `F_q(C)`, `trdeg_{\overline{ℚ}} T_1(ζ_C)=corank(Λ_ff)=1` (`ln q`, Lindemann + Weil-algebraicity), and generally `trdeg T_{s_0}(L)≤corank(Λ)` when the block is polynomial in multiplier logs; over ℚ the corresponding lower-bound wall is now the joint `{log p}∪{γ_n}` baker-for-Stieltjes target (#124), not a banked isolated `γ_n` theorem; #103 identifies the corank→trdeg gap as the linear→algebraic-independence upgrade for prime logs | [[G2-multi-q-siegel-shidlovsky]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 123 | G4-over-`F_q` native reproof — **THEOREM (paper), BRIDGE**: `S_ff` composed with the infinite-base Galois correspondence (#24) recovers Deligne–Katz geometric/arithmetic monodromy, tensor of sheaves, and Katz–Sarnak/Sato–Tate; the weight/angle split `1→G^0_geom→G_L→W→1` has `dim W=corank(Λ_ff)=1`, so the corank-1 diagonal is exactly the Frobenius/Tate weight torus while `G^0_geom` is the angle monodromy; over ℚ the group-face seam `corank(W)=∞` is conjectural, not banked | [[G4-multi-q-picard-vessiot-and-langlands-group]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 124 | Stieltjes–log weld / no-isolation theorem — **THEOREM (paper), BRIDGE**: in the friable-auxiliary pairing `H=F·(s−1)ζ`, `[H]_N = c_N/N! + Σ_{n<N}(c_{N−n−1}/(N−n−1)!)(−1)^nγ_n/n!`; each lower `γ_n` carries positive-weight log-`p` coefficient `c_{N−n−1}∈R_{N−n−1}`, and killing all positive weights for every `N` forces `F≡const`; hence nontrivial auxiliary iff nonzero log-`p` residual, Stieltjes transcendence cannot be isolated from multiplier-log transcendence, and the honest G2/DSS-cross target is the joint Schanuel-entangled `trdeg_ℚ ℚ({log p}∪{γ_n})=∞`; seam realized inside the construction | [[bucket-the-seam-archimedean-obstruction]] / [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 125 | corank as the unifying seam invariant — `corank(Λ_M)=rank(ℤ^{(P)}/Λ_M)=dim⟨g⟩`-closure is one invariant with three proven faces: G1 holonomicity (`<∞⟺` holonomic, #119), G2 continuation/period transcendence (`trdeg≤corank`, exact `=1` over `F_q`, #122), and G4 weight torus (`dim W=corank=1` over `F_q`, #123); finite over every border (`Λ_ff=ker deg`, corank `1`, #121). **Conjecture:** over ℚ, `corank=∞` is realized, not just an upper bound, on all three faces simultaneously, and the gap `∞−1` is the missing single Frobenius / archimedean seam (`ζ` non-holonomic ⟺ no single Frobenius ⟺ corank `∞` ⟺ seam non-trivial); open content = one G1-anchored lower-bound realization over ℚ. Door-3: `corank`-native ⟺ seam non-trivial; kept distinct from C5★, which remains the branchhood lock | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
| 126 | Jensen-section prime kernel, first order — **THEOREM (paper), BRIDGE**: the prime-induced displacement of degree-`d` Jensen-section roots is `ε_l(t)=Σ_n c_n e^{-𝔦t\log n}K_d(r_l;n;t)`, with prime coefficients `c_p=p^{-1/2}` and `K_d(r_l;p;t)` an explicit degree-`≤d` polynomial in `\log p` with archimedean coefficients; pins the kernel flagged in #104 and converts the C5★ root-collision crux into the concrete weighted-Bohr-resonance inequality `sup_t |Σ_p p^{-1/2}K_d(r_l;p;t)e^{-𝔦t\log p}| ≥ Δ_l`; provenance: a legitimate proof/localization of the already-mined SEED-AB prime-kernel direction, not a new strategic conclusion; first-order and explicit-formula regularization caveats remain, and the uniform-in-`d` edge bound stays open | [[door-C5-irreducibility-and-door-2-retest]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 127 | completed `(σ,∂)` connection category (consolidation/construction): build `𝓜⁺` = the flat prime connection + the ∞-lane as a connection term `D=x d/dx=−Σ(log p)θ_p` (Connes scaling op, #88§7/#90§1), parameterized Galois `gen(G_L⁺)=D+{σ_p}` (#90§7), with `FE=flatness` of the completed connection and RH = unitary holonomy (#91§4) — the weld #91§3 calls "the work no one has done"; inputs already mined/ledgered (`BerryKeating`, `primeDiagonal_shift`, `FlatConnection`; mean essentially self-adjoint #90§8). Generator-level construction is now BRIDGE by #136 (`σ_p` and `∂_s` are Fourier-diagonal and combination-mode-free); any native content must be global holonomy / G5 positivity, not the generators or FE=flatness alone | [[bucket-archimedean-generator]] / [[G5-unitarity-gatekeeper]] | CONJECTURE | FOUNDATIONAL |
| 128 | archimedean corank collapse (the one new connector, postdates the mining): the product formula `∏_v|x|_v=1` (= FE/base-swap `0↔∞`, #70/#90§64.3) in operator form **is** `∂_s=−Σ(log p)θ_p` (Connes `D`, #88§7); conjecture the completed lattice `Λ⁺` has `corank=1`, so the seam gap `∞−1` (#125) reads "`∞` finite primes, `1` archimedean relation" and the missing single Frobenius `=∂_s`; falsifiable (relation-in-`Λ⁺` vs new infinite generator); Stieltjes test `trdeg=1` in the `∂_s`-direction; `F_q` anchor `corank=1` | [[bucket-archimedean-generator]] / [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
| 129 | KMS / modular temperature (the WDW/thermal-time crystallization; EMBASSY→native target): Bost–Connes `KMS_β` has `β=s` and partition function `ζ(β)`; `∂_s=D=−Σ(log p)θ_p` = the Tomita–Takesaki modular flow = emergent thermal time (Connes–Rovelli, the type-III "no trace" forces it); conjecture `σ`=inverse temperature, FE `s↔1−s` = a temperature self-duality `β↔1−β`, RH = self-dual (`β=½`) KMS criticality; honest subtlety = condensation at `β=1` (the pole/pump) vs FE self-duality at `½`, so the object is the modular structure on `{0,½,1}`; the one time-bucket EMBASSY ingredient with a rigorous engine (Bost–Connes), hence the best candidate to follow the erosion threshold into native math; card: `../pipeline/0-backlog/kms-modular-temperature.md` | [[bucket-time-and-non-holonomic-time]] / [[bucket-archimedean-generator]] | CANDIDATE | FUTURE |
| 130 | two sources of hypertranscendence — **THEOREM (paper), BRIDGE**, now grounded by a complete decidable invariant: a rank-1 shift multiplier `a` is constant-up-to-shift-coboundary (CC) iff its divisor has degree 0 on every σ-orbit `O=β+ℤ` (`deg_O(a)=0` for all `O`), equivalently rational shift-summability / Abramov in divisor form. This completes #134's sufficient degree-at-∞ test: degree-at-∞ is the summed orbit-degree shadow, while orbit-balance is the exact classifier. It localizes `Λ`'s unique Source-A place to the single Γ orbit `ℤ` (`div(z)=[0]-[∞]`, `deg_ℤ=+1`), while every prime lane is orbit-balanced/CC (q-orbit analog). The weld is sharpened to `{one non-CC archimedean place} × {CC prime places}`; seam/corank `∞-1`/missing Frobenius = the archimedean orbit imbalance, vanishing over `F_q` (all-balanced, holonomic/Weil). Does not earn C5; it classifies the borders. Card: `../pipeline/2-fully-proven/two-sources-of-hypertranscendence.md` | [[bucket-archimedean-generator]] / [[G1-difference-holder]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 131 | general-`t` Jensen-section hyperbolicity perturbation lemma (value+slope) — **RETURNED TO LEAN BACKLOG / under review**: the strict-interior-window repair (`w_i=½ min(ρ_i,δ_i/2)`, `m_i>0`) fixes the curvature-minimum issue, but the current statement still chooses `x_i'` as a root of `F'` in the open interval `(x_i-ε_i,x_i+ε_i)` with `ε_i=sup_{window}|D'|/m_i`; when `sup_{window}|D'|=0`, `ε_i=0` and that open interval is empty, while the natural witness is `x_i`. Required repair: use a closed interval or split the zero-slope case with an explicit witness convention. Until then the perturbation barrier is not a banked theorem; it remains a proposed support lemma for #104/#126. Card: `../pipeline/0-backlog-lean/c5-jensen-perturbation-lemma.md` | [[door-C5-irreducibility-and-door-2-retest]] / [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE (under Lean review) | FOUNDATIONAL |
| 132 | completed base `R⁺` (the definitional foundation): adjoin the archimedean coordinate to the Bohr ring `R=ℂ[x_p^{±1}]` — the `s`/`Γ` direction on which `∂_s=−Σ(log p)θ_p` is a generator, a `Γ`-symbol with polynomial-multiplier recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, and the product-formula relation `∏_v|x|_v=1` — giving the difference–differential ring `(R⁺,{σ_p},∂_s)` with `[∂_s,σ_p]=0`; the brick under `completed-connection-category`, and the first Lean floor of the reorientation. Card: `../pipeline/0-backlog/completed-base-archimedean-coordinate.md` | [[bucket-archimedean-generator]] | CONJECTURE | FOUNDATIONAL |
| 133 | Γ-module `M_∞` (first Source-A object): construct the archimedean Euler factor `π^{-s/2}Γ(s/2)` as a rank-1 polynomial-multiplier difference module with recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)` (`a(s)=s/2π`, #90 §64) and `ζ`-regularized determinant `=Γ`; then `M_Λ=M_∞⊗M_ζ` has the completed `Λ` as diagonal section. Difference-simple realization of the differential-wild `Γ`, feeding the completed category and weld. Card: `../pipeline/0-backlog/gamma-module-construction.md` | [[bucket-archimedean-generator]] | CONJECTURE | FOUNDATIONAL |
| 134 | multiplier-coboundary dichotomy — **THEOREM (paper), BRIDGE**: for a rank-1 difference module `σe=a·e`, a solution is holonomic/differentially algebraic iff the multiplier is constant-up-to-σ-coboundary (CC), while non-CC rank-1 shift multipliers are on the hypertranscendental side (Hölder for `Γ`; ADH/Hardouin–Singer as cited import for the general rational converse). **Proved here:** CC gauge-trivializes to `σe'=c·e'`, Galois lies in `𝔾_m`, and in the shift case `f=g·c^z` satisfies a first-order ODE; also `g(z+1)/g(z)→1`, so non-constant polynomial multipliers such as `Γ(z+1)=zΓ(z)` are not CC. Corollary: CC is the Source-B/prime holonomic regime, the archimedean `Γ` lane is the unique non-CC Source-A lane, and over `F_q` all place multipliers are CC, matching the corank-1 holonomic shadow (#121). #130 is the complete orbit-balance classifier refining this row's degree-at-∞ obstruction. This proves the Source-A/B separator but **does not earn C5**; #135 further shows the FE-cocycle weld form is BRIDGE, so C5 points to G5 positivity / unitary holonomy. Card: `../pipeline/2-fully-proven/multiplier-dichotomy-theorem.md` | [[bucket-archimedean-generator]] / [[G1-difference-holder]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 135 | archimedean×prime FE-conspiracy cocycle — **THEOREM (paper), BRIDGE**: on `M_Λ=M_∞⊗M_ζ`, the obstruction to factoring `ι:s↦1−s` as `ι_∞⊗ι_ζ` is the cocycle product relation `ρ_∞·ρ_ζ=1`, with `ρ_∞=Γ_ℝ(1−s)/Γ_ℝ(s)=χ` and `ρ_ζ=ζ(1−s)/ζ(s)=χ^{-1}`. The defect `[χ]` is purely archimedean (`χ=π^{s−1/2}Γ((1−s)/2)/Γ(s/2)`), the prime lane carries `ι` by the free inversion `θ_p↦−θ_p` plus `σ_p`-shift with zero FE-defect, and `χ` is not `∂_s`-horizontal, so `ι_∞` is not a module automorphism. Door-2 verdict: BRIDGE, because the value is the classical FE and the obstruction is Source-A-alone; it **does not earn C5**. Payload: C5 is not in FE/factorization structure but in G5 positivity / unitary holonomy (#38/#127). `F_q`: no `M_∞`, so `χ≡1` and the cocycle is trivial, matching corank 1 (#121). Card: `../pipeline/2-fully-proven/archimedean-prime-cross-term.md` | [[bucket-the-seam-archimedean-obstruction]] / [[bucket-archimedean-generator]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 136 | `(σ_p,∂_s)` generators are Fourier-diagonal — **THEOREM (paper), BRIDGE/structural**: on Bohr modes `e_m`, `σ_p e_m=p^{-m_p}e_m` and `∂_s e_m=-(m·ℓ)e_m`, so the archimedean generator `∂_s=-Σ(log p)θ_p`, despite summing over all primes, creates no combination modes; only the Source-A digamma term is non-axis, and it is prime-free. Combination modes, the native C5 zone, arise from ring/product/moment structure `e_m e_{m'}=e_{m+m'}`, never from connection generators. Payload: the full generator/connection/flatness level is BRIDGE; C5 is forced to moment-product positivity (#104) or global G5 holonomy (#38/#127). `F_q`: one diagonal Frobenius generator, corank 1 (#121). Card: `../pipeline/2-fully-proven/archimedean-generator-axis-mode.md` | [[bucket-archimedean-generator]] / [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |

---

## §D Tally (counted from §C with `grep` — 136 rows; the table is the source of truth)

A few rows carry a **compound** tag (e.g. #92 `IMPORT (half) + CONJECTURE`, #56/#93 `…+numeric/cert`),
so these counts overlap slightly and sum to a little above 136 — they are "rows mentioning each tag,"
not a strict partition.

| Type | Count |
|---|---:|
| THEOREM (Lean) — machine-checked | 10 |
| THEOREM (paper) — difference category / draft | 40 |
| IMPORT — borrowed classical theorems | 10 |
| LEMMA | 2 |
| CONJECTURE — open & stated (pickable) | 36 |
| CANDIDATE — new ideas to shape | 10 |
| OPEN CORE — the walls | 6 |
| FALSIFIED | 2 |
| FRAMING — embassy / not math | 6 |
| BRANCH STATUS / STRUCTURAL | 16 |

*Reading it:* we have **real proven content** — **52 proven statements** (10 machine-checked in
Lean + 40 paper + 2 lemmas), resting on **10 imported** classical theorems — and a large, well-located
**frontier**: **36 stated conjectures + 10 candidates + 6 walls (open cores)**. The proven content is
the *scaffolding*; **zero of it is yet certified NATIVE/C5** — the two leading candidates (§59/§60) were
re-tested and came back **BRIDGE**, so earning a first irreducible (C5) theorem is the highest-leverage
open problem.

*Maintenance:* when a row changes status (a conjecture becomes a theorem, a candidate gets posed, the
Door-2 verdict lands), edit its row here and update the bucket file + `00-index.md`.
