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

**Gatekeeper scoreboard — how many foundational conjectures are theorems:**
| Gate | What | Best status today |
|---|---|---|
| **G1** | no single q-difference equation | ✅ **THEOREM (paper)**, difference category — Door-2: **BRIDGE** (not C5) |
| **G2** | DSS (zeros independent) | ◐ **half**: upper bound proven; lower bound = open core; reduced to `{π,ζodd,Stieltjes}` indep |
| **G3** | holonomy ⟺ corank dichotomy | ✅ **THEOREM (paper)** — Door-2: **BRIDGE** (also fails Door-3) |
| **G4** | Picard–Vessiot / Langlands group | ◐ structurally built (but likely IMPORT under Door-2); `ω=0` open |
| **G5** | unitarity ⟺ RH (candidate) | ◐ finite anchors are **THEOREM (Lean)**; the infinite case is open core |

**Count:** **NATIVE/C5 theorems certified = 0** — the two leading candidates (§59, §60) were re-tested
and graded **BRIDGE**, so C5 stays open. Proved difference-category bridge theorems = **2 (§59, §60)**;
machine-checked supporting theorems (Lean) = ~10 distinct statements (full list:
[[bucket-ledger-footholds]]). The five apex faces (RH, DSS, Langlands, realization, the archimedean
obstruction) are all **FIELDS MEDAL** and open.

---

## §B Pick something to prove — *"what could I work on today?"*

To actually work an item, open a card for it in the **pipeline** (`../pipeline/`, template
`../pipeline/_card-template.md`) and move it `0-backlog → … → 4-publication-ready`. Several backlog
cards already exist.

**Milestone 1 — "this is actually a branch."** Branchhood = all seven of C1–C7 MET (§A). C1/C2/C4 are
MET; **C6 is now MET (bridge level, 2026-06-19, below)**. The criteria each have a pipeline card:
- **C5** (irreducible theorem — the keystone, NOT MET): **in work** at
  `../pipeline/1-in-progress/combination-mode-baker-reducibility.md` (C5★) with the carrier pinned at
  `../pipeline/1-in-progress/finite-free-convolution-flow.md` (degree-`d` finite-free/Hankel section;
  bounded-degree ∧ RH-relevant; Baker load-bearing at each `d`, the `d→∞` uniform edge = the open crux).
- **C3** (native invariant, PARTIAL): **reduced to C5 (resolved 2026-06-19).** Cheap invariants proven
  BRIDGE (`../pipeline/2-fully-proven/c3-gluing-invariants-bridge.md`): joint gluing invariants exist
  (per-prime-equal yet jointly-distinct modules) but are all character-variety pullbacks; the only
  Door-3-surviving invariant is the arithmetic layer = **C5★**, so **C3-native ⟺ C5★** and closing C5
  closes C3. The independent-C3 goal failed (`../pipeline/5-failed/c3-native-invariant-door3.md`).
- **C6** (faithful bridge): **MET (bridge level), resolved 2026-06-19**
  (`../pipeline/2-fully-proven/c6-specialization-functors.md`). The three border functors are built and
  each recovers its parent (single-prime = vdPS / function-field = Deligne–Papanikolas–Deligne–Katz /
  diagonal = Bohr–Kronecker); `𝓜` strictly extends the single-prime border via the **proven** difference-
  Hölder theorem (G1: ζ finite-base-holonomic but non-holonomic in the limit). The native/irreducible
  strict extension = **C5★**, still open.
- **C7** (autonomy, NOT MET): `../pipeline/0-backlog/c7-autonomy-foundational-core.md` — axiomatized
  N1–N4 + one native structural theorem. *(C5 and C7 are coupled.)*

**Most leverage (a few sessions, not a lifetime):**
- **#6 / #23 / #50 — Door-2 re-test of §59/§60: DONE (2026-06-19).** Both FAIL → **BRIDGE**; C5 still
  unearned. The next C5 attempt must use the `σ_p` jointly and irreducibly (not the single shift
  `s↦s+1`). See [[door-C5-irreducibility-and-door-2-retest]].
- **#10 / #11 — formalize the DSS reduction** (`DSS ⟺ {π,ζodd,Stieltjes} indep`) + the conditional
  Nesterenko→DSS as Lean `Prop`s. The change-of-basis is already in Lean.

**Bite-size & tractable (good single-session targets):**
- **#104 — finite-free convolution flow:** now the **pinned C5★ carrier** (in-progress). Bite-size piece
  remaining = the numerical test (finite-free cumulants of `J^{d,n}` vs `Σ_p κ_k(p)`; runpod).
- **#59 — erosion threshold (G19):** write up `½ = the marginal-variance locus`; the hard analytics
  (Selberg/Ingham) are already theorems (#60).
- **#95 — is `Λ` (the dBN constant) a period?** A PSLQ probe + a writeup.
- **#19 — "a Baker for the Stieltjes constants":** scope the sub-problem (the rung just above Baker).
- **#96 / #100 — shape a sibling into a real conjecture:** Lee–Yang localization, or family-DSS=GSH.

**Heroic but well-posed (the gatekeepers' open cores — expect long campaigns):**
- **#15 / #18 — obstruction C / DSS-cross** (the Stieltjes side): the G2 wall.
- **#27 — compute `ω ∈ H²(G_L)`** (Tannakian / motive / realization, all at once).
- **#38 / #41 — the carrier infinite passage:** lift `κ₋=0`/`m_ξ` Herglotz from finite to actual `ξ`.

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
| 7 | DSS: trdeg = orbit-dim ⟹ zeros independent | [[G2-multi-q-siegel-shidlovsky]] | CONJECTURE | FIELDS MEDAL |
| 8 | upper bound trdeg ≤ dim G_M (T-up) | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper) | FOUNDATIONAL |
| 9 | diagonal orbit closure = `𝕋^∞` (orbit dim ∞, free) | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper) | FOUNDATIONAL |
| 10 | `P_k` closed form + Li↔secular ℤ change-of-basis | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (Lean) | FOUNDATIONAL |
| 11 | DSS = independence of `{π}∪{ζ(odd)}∪{Stieltjes γ_n}` | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper)+PSLQ | FOUNDATIONAL |
| 12 | Siegel's lemma in ∞ variables (obstruction A) = Bombieri–Vaaler | [[G2-multi-q-siegel-shidlovsky]] | IMPORT | FOUNDATIONAL |
| 13 | multi-q zero estimate, finite-S (obstruction B) | [[G2-multi-q-siegel-shidlovsky]] | THEOREM (paper) | FUTURE |
| 14 | uniformity-in-S of the zero estimate (Conj 5′) | [[G2-multi-q-siegel-shidlovsky]] | CONJECTURE | FUTURE |
| 15 | arithmetic of the L-values (obstruction C) | [[G2-multi-q-siegel-shidlovsky]] | OPEN CORE | FIELDS MEDAL |
| 16 | full DSS over `F_q(t)` = Papanikolas | [[G2-multi-q-siegel-shidlovsky]] | IMPORT | FOUNDATIONAL |
| 17 | edge value transcendence at `s=1` = Baker | [[G2-multi-q-siegel-shidlovsky]] | IMPORT | FUTURE |
| 18 | `{γ_n}` independent of all `MTM(ℤ)` periods (DSS-cross) | [[G2-multi-q-siegel-shidlovsky]] | OPEN CORE | FIELDS MEDAL |
| 19 | a "Baker for the Stieltjes constants" | [[G2-multi-q-siegel-shidlovsky]] | CONJECTURE | FUTURE |
| 20 | holonomic ⟺ `corank(Λ)<∞` (corank dichotomy) | [[G3-holonomy-dichotomy]] | THEOREM (paper) | FOUNDATIONAL |
| 21 | pro-torus inverse problem `dim=corank` (P3) | [[G3-holonomy-dichotomy]] | THEOREM (paper) | FOUNDATIONAL |
| 22 | solvability (not abelianness) ⟺ `L=0` (DMR) | [[G3-holonomy-dichotomy]] | THEOREM (paper) | FOUNDATIONAL |
| 23 | §60 Door-2 verdict — **BRIDGE** (also fails Door-3) (resolved) | [[door-C5-irreducibility-and-door-2-retest]] | STRUCTURAL | FOUNDATIONAL |
| 24 | infinite-base Galois correspondence | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (paper) | FOUNDATIONAL |
| 25 | inverse-Galois: `R_multi = {G:π₀ finite abelian}` | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (paper) | FOUNDATIONAL |
| 26 | Satake λ-ring algebra (⊗,⊕,Adams,plethysm,e–h) | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (Lean) | FOUNDATIONAL |
| 27 | `ω=0` ⟺ Tannakian ⟺ motive exists ⟺ realization | [[G4-multi-q-picard-vessiot-and-langlands-group]] | OPEN CORE | FIELDS MEDAL |
| 28 | `G_𝒜` = the Langlands group `L_ℚ` | [[G4-multi-q-picard-vessiot-and-langlands-group]] | CONJECTURE | FIELDS MEDAL |
| 29 | Rankin–Selberg = ⊗ (unramified places) | [[G4-multi-q-picard-vessiot-and-langlands-group]] | THEOREM (paper) | FUTURE |
| 30 | G4 over `F_q` = Deligne–Katz | [[G4-multi-q-picard-vessiot-and-langlands-group]] | IMPORT | FOUNDATIONAL |
| 31 | σ-fixed-modulus locus = the critical line (Lemma 1) | [[G5-unitarity-gatekeeper]] | LEMMA | FOUNDATIONAL |
| 32 | `κ₋` = #off-line zero-pairs, **exactly** (finite carrier) | [[G5-unitarity-gatekeeper]] | THEOREM (Lean) | FOUNDATIONAL |
| 33 | `m_ξ` Herglotz (`κ₋=0`) ⟺ RH (carrier form) | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 34 | CMV operator unitary ⟺ `|γ_k|<1` ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE+numeric | FIELDS MEDAL |
| 35 | `ι=κ` (FE-involution = adjoint) ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 36 | secular Jacobi / Berry–Keating self-adjoint ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 37 | Hodge–Riemann `Q_W⪰0` (Weil rep of `SL₂`) ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 38 | `H_W=−Δ_prime+V_arch ≥ 0` ⟺ RH (operator built; domination open) | [[G5-unitarity-gatekeeper]] | OPEN CORE | FIELDS MEDAL |
| 39 | HP = gen(`G_L`), `[D,P]=0` ⟺ RH (mean rigorous) | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 40 | unitary holonomy of completed flat connection ⟺ RH | [[G5-unitarity-gatekeeper]] | CONJECTURE | FIELDS MEDAL |
| 41 | the infinite passage (lift finite carrier to actual ξ) | [[G5-unitarity-gatekeeper]] | OPEN CORE | FIELDS MEDAL |
| 42 | C1 native ontology — **MET** | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 43 | C2 native category — **MET** | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 44 | C3 native invariant — **PARTIAL → reduced to C5** (resolved 2026-06-19): cheap invariants proven BRIDGE (#115); native invariant ⟺ C5★; independent goal failed (`../pipeline/5-failed/c3-native-invariant-door3.md`) | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 45 | C4 native problem — **MET** | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 46 | C5 irreducible theorem — **NOT MET** (the gap); in work `../pipeline/1-in-progress/combination-mode-baker-reducibility.md` (C5★) | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 47 | C6 faithful bridge — **MET** (bridge level, 2026-06-19): three border functors built; recover vdPS / Deligne–Papanikolas–Deligne–Katz / Bohr–Kronecker; `𝓜` strictly extends single-prime via proven G1 (#116); native extension = C5★ (`../pipeline/2-fully-proven/c6-specialization-functors.md`) | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 48 | C7 autonomy — **NOT MET**; ticket `../pipeline/0-backlog/c7-autonomy-foundational-core.md` | [[door-C5-irreducibility-and-door-2-retest]] | BRANCH STATUS | FOUNDATIONAL |
| 49 | σ-parity = FE-parity weld (candidate native theorem) | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (Lean) | FOUNDATIONAL |
| 50 | Door-2 re-test of §59/§60 — **DONE: both BRIDGE; C5 open** | [[door-C5-irreducibility-and-door-2-retest]] | STRUCTURAL | FOUNDATIONAL |
| 51 | carrier germ: RH = global type, DSS = infinite jet (one object) | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 52 | ridgeline: boundary rep unitary ∧ faithful (no-margin = faithful) | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 53 | period matrix Π: RH = purity, DSS = period-fullness | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 54 | Face A ⊥ Face B (orthogonality theorem) | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FUTURE |
| 55 | secular point in Li-cone AND generic (cone∩generic) | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 56 | `Z_n ≻ A_n` (Ω_∞≻Π) ⟺ RH (explicit Li coords) | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE+numeric | FIELDS MEDAL |
| 57 | μ pseudorandom = RH + LI (one statement) | [[bucket-A1-A2-unification-the-carrier]] | CONJECTURE | FIELDS MEDAL |
| 58 | both finite layers ledgered (`κ₋` + esymm indep) | [[bucket-A1-A2-unification-the-carrier]] | THEOREM (Lean) | FOUNDATIONAL |
| 59 | `½` = erosion threshold of the ∞-frequency cocycle (G19) — **in progress**; backbone (#110) + 19a cocycle reducibility (#111) proven; open: 19b | [[bucket-time-and-non-holonomic-time]] | CONJECTURE | FUTURE |
| 60 | marginal regime = Selberg CLT / Keating–Snaith | [[bucket-time-and-non-holonomic-time]] | IMPORT | FUTURE |
| 61 | non-holonomic = no native clock (Hölder = WDW timelessness) | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 62 | HP = a **constraint**, not a Hamiltonian | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 63 | equidistributed clock ⟺ timelike ⟺ on-line zeros | [[bucket-time-and-non-holonomic-time]] | CONJECTURE | FUTURE |
| 64 | `Λ_dBN` = arrow of time / transcendence clock | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 65 | FE = a handshake across time (absorber/two-state) | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 66 | no-margin = clock marginally null (light-cone) | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 67 | primes = CTCs, zeros = time-crystal, BH/causal-set | [[bucket-time-and-non-holonomic-time]] | FRAMING | FUTURE |
| 68 | the seam = the period / non-period divide | [[bucket-the-seam-archimedean-obstruction]] | STRUCTURAL | FOUNDATIONAL |
| 69 | both apex faces = **ONE** archimedean obstruction | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
| 70 | missing Frobenius = F₁ = three names (B24=B8=DSS) | [[bucket-the-seam-archimedean-obstruction]] | STRUCTURAL | FOUNDATIONAL |
| 71 | `ω=0` ⟺ D trace-class ⟺ HP ⟺ RH (unifies 5 programs) | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
| 72 | two towers (spectral dead, motivic live) = the seam | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FUTURE |
| 73 | superzeta = additive resolvent trace (Σ, not ∏) | [[bucket-the-seam-archimedean-obstruction]] | THEOREM (Lean) | FOUNDATIONAL |
| 74 | multiplicative-only methods are apex-blind (structural) | [[bucket-the-seam-archimedean-obstruction]] | STRUCTURAL | FOUNDATIONAL |
| 75 | regularization is transcendence-creating (G16 freshness) | [[bucket-the-seam-archimedean-obstruction]] | CANDIDATE | FUTURE |
| 76 | keystone over `F_q` = Grothendieck | [[bucket-function-field-proving-ground]] | IMPORT | FOUNDATIONAL |
| 77 | RH over `F_q` = Deligne (Weil II) | [[bucket-function-field-proving-ground]] | IMPORT | FOUNDATIONAL |
| 78 | Weil FE of the L-polynomial | [[bucket-function-field-proving-ground]] | THEOREM (Lean) | FOUNDATIONAL |
| 79 | CM/non-CM = rotation / almost-Mathieu cocycle dichotomy | [[bucket-function-field-proving-ground]] | THEOREM (paper)+cert | FUTURE |
| 80 | the bracket: 2 solved corners vs 2 open apexes | [[bucket-function-field-proving-ground]] | STRUCTURAL | FUTURE |
| 81 | First Theorem: Euler product ⟺ Bohr factorization (fake filter) | [[bucket-realization-and-fake-family]] | THEOREM (Lean) | FOUNDATIONAL |
| 82 | three cuts (E)/(A)/(P): positivity ≠ genuineness | [[bucket-realization-and-fake-family]] | THEOREM (paper) | FOUNDATIONAL |
| 83 | Spectral Torelli: `{s_m}` determine ξ | [[bucket-realization-and-fake-family]] | THEOREM (Lean, finite) | FOUNDATIONAL |
| 84 | overdetermination locus = genuineness (G17) | [[bucket-realization-and-fake-family]] | CONJECTURE | FUTURE |
| 85 | off-line Beurling systems exist ⟹ RH non-generic | [[bucket-realization-and-fake-family]] | IMPORT | FOUNDATIONAL |
| 86 | realization problem: is Euler ⟺ two-faces an **IFF**? (#7) | [[bucket-realization-and-fake-family]] | CONJECTURE | FIELDS MEDAL |
| 87 | superzeta is a "fake" (no Euler product) | [[bucket-realization-and-fake-family]] | THEOREM (paper) | FUTURE |
| 88 | moment positivity ⇏ frequency positivity (N6, witness) | [[bucket-realization-and-fake-family]] | THEOREM (paper) | FOUNDATIONAL |
| 89 | no-margin = one missing uniform bound (4 coordinates) | [[bucket-the-no-margin]] | OPEN CORE | FOUNDATIONAL |
| 90 | two-rate signature: margin ~ δ, cost ~ log(1/δ) | [[bucket-the-no-margin]] | THEOREM (paper) | FOUNDATIONAL |
| 91 | off-line zero breaks TP at order→∞, magnitude→0 (Thm 7) | [[bucket-the-no-margin]] | THEOREM (paper) | FOUNDATIONAL |
| 92 | RH ⟺ `Λ=0`; Rodgers–Tao `Λ≥0` (the FE-forced half) | [[bucket-the-no-margin]] | IMPORT (half) + CONJECTURE | FIELDS MEDAL |
| 93 | no-margin = an exceptional point (PT-unbroken) | [[bucket-the-no-margin]] | CONJECTURE+cert | FUTURE |
| 94 | no-margin = the Law of the Iterated Logarithm | [[bucket-the-no-margin]] | STRUCTURAL | FUTURE |
| 95 | is `Λ` itself a period / transcendental? | [[bucket-the-no-margin]] | CONJECTURE | FUTURE |
| 96 | Lee–Yang localization (RH = marginal-crystalline) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 97 | FE ⟺ measure is a Fourier quasicrystal | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 98 | RH lives only on the pure+polarized locus (G9) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 99 | Koszul-acyclicity ⟺ Tannakian/RH (G15) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 100 | family-DSS = the Grand Simplicity Hypothesis (G13) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FIELDS MEDAL |
| 101 | Tate–prime rigidity weld (G12) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 102 | live motivic period tower (SEED-U) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 103 | friable Dirichlet polynomial = native auxiliary (N5) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 104 | finite-free convolution flow ⟹ RH-stability — **pinned C5★ carrier** (degree-`d` finite-free/Hankel section; power-sums axis-mode, Hankel-PSD condition combination-mode, support ≤ d; bounded-degree ∧ RH-relevant) | [[door-C5-irreducibility-and-door-2-retest]] | CONJECTURE | FOUNDATIONAL |
| 105 | positive direction strength = exactly 1 (Tamagawa, SEED-B) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 106 | seam firewall: finite-place ⊥ archimedean positivity (SEED-A) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FOUNDATIONAL |
| 107 | transcendence ⟹ GUE statistics (B11) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 108 | HP operator "can't be too algebraic" (B18) | [[bucket-new-sibling-conjectures]] | CANDIDATE | FUTURE |
| 109 | a profinite Galois group acts on the zeros (B24) | [[bucket-new-sibling-conjectures]] | FALSIFIED | — |
| 110 | Re=½ = abscissa of a.s. convergence of the random Euler product (G19 backbone) | [[bucket-time-and-non-holonomic-time]] | THEOREM (paper) | FUTURE |
| 111 | Euler cocycle reducible (L²-coboundary) over 𝕋^∞ iff σ≥½ (G19/19a; Door-2 BRIDGE, axis-mode) | [[bucket-time-and-non-holonomic-time]] | THEOREM (paper) | FUTURE |
| 112 | Baker load-bearing for mixed-sign combination-mode reducibility (finite base; Liouville counterexample) | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 113 | C5★ (refined): bounded-degree finite-free reducibility — carrier pinned (#104); Baker load-bearing at each d (edge); d→∞ uniform edge control = near-zero distribution of `{Σ a_p log p}` beyond Baker's floor (the open native crux) | [[door-C5-irreducibility-and-door-2-retest]] | CONJECTURE | FOUNDATIONAL |
| 114 | Hankel ↔ combination-mode degree lemma: under axis-mode secular data, the degree-d real-rootedness certificate (det H_j) has Fourier support ≤ j ≤ d, attained — **not axis-mode for d≥2** (genuine mixed-sign cross-prime modes); fixed-d Baker exponent (≤d logs) | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 115 | joint gluing invariants exist (per-prime-equal yet jointly-distinct modules; rank-2 two-prime witness) but all are character-variety pullbacks ⟹ BRIDGE; native invariant ⟺ C5★ (the C3 dividing line) | [[door-C5-irreducibility-and-door-2-retest]] | THEOREM (paper) | FOUNDATIONAL |
| 116 | three border specialization functors (C6 MET, bridge): each recovers its parent (single-prime=vdPS / function-field=Deligne–Papanikolas–Deligne–Katz / diagonal=Bohr–Kronecker); `𝓜` strictly extends single-prime via proven G1 (finite-base-holonomic but non-holonomic limit); native extension = C5★ | [[bucket-function-field-proving-ground]] | THEOREM (paper) | FOUNDATIONAL |

---

## §D Tally (counted from §C with `grep` — 116 rows; the table is the source of truth)

A few rows carry a **compound** tag (e.g. #92 `IMPORT (half) + CONJECTURE`, #56/#93 `…+numeric/cert`),
so these counts overlap slightly and sum to a little above 116 — they are "rows mentioning each tag,"
not a strict partition.

| Type | Count |
|---|---:|
| THEOREM (Lean) — machine-checked | 10 |
| THEOREM (paper) — difference category / draft | 23 |
| IMPORT — borrowed classical theorems | 10 |
| LEMMA | 2 |
| CONJECTURE — open & stated (pickable) | 30 |
| CANDIDATE — new ideas to shape | 13 |
| OPEN CORE — the walls | 6 |
| FALSIFIED | 1 |
| FRAMING — embassy / not math | 6 |
| BRANCH STATUS / STRUCTURAL | 15 |

*Reading it:* we have **real proven content** — **35 proven statements** (10 machine-checked in
Lean + 23 paper + 2 lemmas), resting on **10 imported** classical theorems — and a large, well-located
**frontier**: **30 stated conjectures + 13 candidates + 6 walls (open cores)**. The proven content is
the *scaffolding*; **zero of it is yet certified NATIVE/C5** — the two leading candidates (§59/§60) were
re-tested and came back **BRIDGE**, so earning a first irreducible (C5) theorem is the highest-leverage
open problem.

*Maintenance:* when a row changes status (a conjecture becomes a theorem, a candidate gets posed, the
Door-2 verdict lands), edit its row here and update the bucket file + `00-index.md`.
