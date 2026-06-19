# Bucket DOOR — C5 irreducibility & the Door-2 re-test

**Bucket grade:** organizational (SEARCH channel). Sorted from `00-charter-wall-and-door.md` +
`docs/support-extraction-log.md`.
**Scope (one line).** The charter's branchhood criteria (C1–C7), the five Door tests, the proto-branch
verdict, and the **concrete worklist** that could move the verdict: the §59/§60 Door-2 re-test.
**Status (resolved 2026-06-19).** The **Door-2 re-test** of §59 (difference-Hölder) and §60 (corank
dichotomy) is **done: both FAIL → BRIDGE**, so C5 stays open (see Verdict below). The next step is to
construct a theorem that uses the `σ_p` **jointly and irreducibly** — not the single shift `s↦s+1`.

---

## The charter machinery (the gate every item passes through)

### The seven branchhood criteria (charter Part I)
- **C1** native ontology · **C2** native category · **C3** native invariant · **C4** native problem ·
  **C5** irreducibility (the keystone — a theorem whose statement/proof *essentially requires* the
  apparatus) · **C6** faithful bridge · **C7** autonomy.
- The worked template (differential Galois theory) passes all seven; it *is* a branch **because of C5**
  (the Airy = SL₂ theorem proves what ODE methods can't see). Our field must produce its analogue.

### The five Door tests (charter Part III) — the master key is Door-2
- **Door-1 (object):** does it *essentially* refer to a multi-q module / `σ_p`-family / `G_L`?
- **Door-2 (load-bearing, MASTER KEY):** *strip every word of multi-q-difference-Galois vocabulary.
  Does a parent discipline still prove it intact? If yes, it FAILS.*
- **Door-3 (native invariant):** does it genuinely use `G_L`, `corank(Λ)`, the difference-trdeg, the
  holonomy type — not a renamed classical invariant?
- **Door-4 (native zone):** does it live in `{multiple independent bases} ∩ {difference not
  differential} ∩ {infinite/arithmetic base}` (all three parents fail at once)?
- **Door-5 (faithful restriction):** specialized to a P5 border (one prime, finite truncation,
  function field), does it recover the known classical answer?
- **The one-line Door:** *Remove the new vocabulary. If a parent still proves it, it never came
  through the door.*

### The verdict on the field (charter Part IV)
- C1, C2, C4 **MET** (definitionally); C3 **PARTIAL** (`G_L` is, in built work, the Bohr–Kronecker
  `𝕋^∞⋊σ` relabeled); **C5 NOT MET — the gap**; **C6 MET** (bridge level, 2026-06-19: three border
  functors built + G1 strict extension); **C7 NOT MET**.
- **Verdict:** a well-posed **proto-branch** — native definitions + faithful borders, but failing the
  keystone C5 and autonomy C7. *"A vocabulary with conjectures and a precisely-located problem — not
  yet a distinct branch."* Until C5 is earned, the project is a **programme**, not a "field/branch."

### The grades & pruning protocol (charter Part V)
- Grades: **NATIVE** / **CONJECTURE (native)** / **BRIDGE** / **IMPORT** / **EMBASSY** / **SUSPECT**.
- Pruning is **reversible re-grading + relocation**, never deletion of team work; every draft carries a
  grade banner with a one-line Door justification; the manifest is the official census.

---

## The worklist that can move the verdict — the Door-2 re-test (#68 implication, #101 action item)

The mining found that the charter's "0 proven native theorems" verdict may be **too pessimistic**: two
difference-category theorems inside the corpus were the leading C5 candidates. They have now been
re-tested; the verdict (below) is that **both are BRIDGE**.

### The two candidates (re-tested — verdict below)
1. **§59 — difference-Hölder (= G1).** Holonomic diagonal ⟹ finite-dim s-difference-Galois group, but
   the arithmetic s-monodromy `g=(p^{−1})_p` has infinite-dim Zariski closure when `Λ=0` ⟹ no
   finite-order difference equation. *Verdict: BRIDGE — the proof reduces to single-operator difference
   Galois + Kronecker–Weyl on `𝕋^∞` + unique factorization (see Verdict below).* See [[G1-difference-holder]].
2. **§60 — corank dichotomy (= G3 = C6).** Holonomic ⟺ `corank(Λ)<∞`, via `dim⟨g⟩-closure =
   corank(Λ)`. See [[G3-holonomy-dichotomy]].
   - Supporting native-invariant candidate (#101 7b/§43.2): the pro-torus inverse problem
     `dim=corank` (P3 solved).

### Candidate NATIVE welds with Lean footholds (worth a Door-2 look)
- **§3 difference-galois-cohomology — the σ-parity = FE-parity weld (#73):** `σ|_{∧^k V}=(−1)^k` ⟹
  `H^even` FE-surviving / `H^odd` FE-killed (`fe_odd_moment_vanish`, `exteriorPower_map_neg_id`,
  ledger-proven). *Ties the difference-Galois cohomology grading to the FE — a parent would not state
  it without the prime-lattice apparatus.* Candidate native theorem; re-test against Door-2.

### Explicitly **likely IMPORT** under Door-2 (do NOT bank these as NATIVE)
- Inverse-Galois §55, λ-subring §56, the main structure theorem (Tannakian 7g), rank-2 flora,
  weight=Oseledets/Newton≥Hodge=Mazur, archimedean=polynomial-multiplier prime, FE=base-symmetry
  (Tate), the D6 theorems (Grothendieck/Deligne/Deligne–Katz), period cases (Papanikolas/Chudnovsky/
  gap-labelling). These rest on classical imports (Etingof, classical IGP, Deligne, Tate, RSZ) and are
  IMPORT-reframed.
- The finite Torelli / symmetric-function theorems (#75, `powerSum_torelli`) are symmetric-function
  theory ⟹ **likely IMPORT** under Door-2; only the *infinite* resolvent/Hadamard passage is native-Tier-B.

### The grading discipline to apply throughout (the §42 trap)
- **#68 §42 self-correction #12:** *"any two RH-equivalent statements are trivially equivalent"* — the
  multi-route "convergence" rhetoric is content-free *qua* logical equivalence. **A SEED that is merely
  RH-equivalent is worthless; a SEED giving a new explicit object or a non-trivial identity is real.**
  Apply when promoting anything out of these buckets into a work package.

---

## Verdict (2026-06-19): §59 and §60 both FAIL Door-2 → BRIDGE

The re-test is done. **Neither §59 nor §60 is NATIVE; C5 is not yet earned.**

- **§59 (difference-Hölder).** Stripped of multi-`q` vocabulary the proof is: single-operator difference
  Galois on the one shift `s↦s+1` (van der Put–Singer — the source draft cites them, and §49.3 names
  ADH as the tool) + the closure of `⟨g⟩` in `𝕋^∞` having dimension `= corank` (Kronecker–Weyl /
  harmonic analysis on `𝕋^∞`, a *named* Door-2 parent) + `{log p}` ℚ-independent (unique factorization).
  The native simultaneous-`σ_p` group `G_L` is never used. A parent proves it intact ⟹ **fails Door-2.**
- **§60 (corank dichotomy).** (⟹) = §59's argument; (⟸) = §49.2 + Lipshitz 1988 (the diagonal of a
  `D`-finite series is `D`-finite — an explicit import). Its invariant `corank(Λ)` is the dimension of a
  torus-subgroup closure, a classical algebraic-group invariant renamed ⟹ also **fails Door-3.** BRIDGE.
- **Their real value:** a faithful bridge (C6) and a clean reframing of Hölder (infinite-corank base,
  uniform over all L). But a reframing a parent proves is not irreducible (the §42 trap). The two
  difference-category theorems are genuine and useful; they are not the keystone.

**What a real C5 theorem needs (forward), sharpened by the 19a cocycle analysis.** A Door-2-surviving
theorem must use the `σ_p` **jointly**, and there is now a concrete criterion. View objects by their
Fourier support on `𝕋^∞`:
- **Axis modes** `kδ_p` (one prime each) ⟹ the object **decouples prime-by-prime** into `𝕋^1` /
  single-shift problems ⟹ a parent proves it ⟹ **BRIDGE.** This is exactly what sinks §59, §60, and the
  19a erosion cocycle: the Euler product, the diagonal `log ζ`, and the `s`-monodromy are all additive
  in the primes, hence axis-mode.
- **Combination modes** `m = m_pδ_p + m_qδ_q + …` (≥ 2 nonzero prime entries) are where the joint
  structure is load-bearing: the proof must use **(a)** `m·ℓ ≠ 0` for `m ≠ 0` (unique factorization, no
  resonance) and **(b)** `|m·ℓ| ≥ Baker(|m|)` (linear forms in logs, the small-divisor bound),
  `ℓ = (log p)_p`.

So the C5 search should leave the additive/`log` world and target **cross-prime** objects: the
curvature / integrability class `F_{pq}` (§16, which couples `p` and `q`), Rankin–Selberg `⊗` and the
`n`-level correlations (#79/#86), and the joint `G_L` monoidality class `ω`
([[G4-multi-q-picard-vessiot-and-langlands-group]]). The multiplicative/product world (`ζ²`, `⊗`,
moments) carries combination modes; the additive world does not. *(Derivation:
`../pipeline/2-fully-proven/erosion-cocycle-reducibility.md`.)*

**First instance (2026-06-19).** On mixed-sign combination modes (the near-resonances `p^a ≈ q^b`)
Baker **is** load-bearing: the cohomological equation `Dh=g` is solvable for the prime frequencies
`(log p)` and *unsolvable* for Liouville frequencies (proved, with the Liouville counterexample —
`../pipeline/1-in-progress/combination-mode-baker-reducibility.md`, Lemma R). The **finite-base** case
is BRIDGE (`𝕋^d` KAM + Baker, two parents); the **infinite-base uniform** version — *Conjecture C5★*,
infinite-`d` Baker–KAM reducibility on the prime-frequency `𝕋^∞` flow — is the **first genuine C5
candidate**: it uses the `σ_p` jointly (cross-prime mixed-sign modes), needs Baker essentially, and
sits outside every single parent (finite-`d` KAM does not reach it). Open.

**C5★ refined (2026-06-19, after attacking it).** The *naive* infinite-support C5★ is **killed**:
Baker–Wüstholz's constant `C(s)` grows super-exponentially in the support size `s`, and Dirichlet
pigeonhole shows `(log p)_∞` is **not polynomially Diophantine** over unbounded-support modes — so
standard (fixed-exponent) KAM cannot close it. C5★ must therefore be **bounded-degree** (support `≤ d`,
`d → ∞` taken after the Diophantine control).

**C5★ carrier pinned + Baker verdict (2026-06-19).** The bounded-degree↔RH-relevance tension is
**resolved** by the **degree-`d` finite-free / Hankel section** of `Ξ`
(`../pipeline/1-in-progress/finite-free-convolution-flow.md`): its power-sums `P_k` are axis-mode, but
real-rootedness ⟺ the **Hankel form `H_d=(P_{i+j})` PSD**, a *nonlinear* condition whose `det H_j` carries
**mixed-sign combination modes of support `≤ d`** — so the section is **bounded-degree ∧ RH-relevant** at
once (RH ⟺ all sections hyperbolic, Pólya–Jensen / GORZ), exactly what the flat `F_{pq}` and the
unbounded-support RS moment could not be.

**C5★ resolved (2026-06-19) — reducibility threshold `σ = ¾`, RH-blind; RH relocated to single-orbit
positivity.** The `d → ∞` limit was **worked to conclusion**. The edge coboundary norm
`Σ_m |ĝ(m)|²/|m·ℓ|²` (explicit-formula coefficient model) converges **iff `σ > ¾`**; the controlling
small-divisor bound is the **elementary integer-gap** `|\log(n_+/n_-)| ≥ |n_+−n_-|/\max` — **not Baker**
(Baker rules only the toy `e^{−ρ|m|}` profile of Lemma R) — and the obstruction in `(½,¾]` is the
**consecutive-/balanced-coprime-integer** near-resonances `(M, M−1)`. Crucially this norm is a
`𝕋^∞`-variance (`L²`) quantity, so by the **A1/A2 split** (Weyl: `L²` controls the typical fluctuation, not
the single-orbit sign) it is **RH-blind** — `σ = ½` sits deep in the non-reducible zone. **So
reducibility ⟺ RH is refuted, and the cocycle-reducibility framing is the wrong handle.** The RH content
relocates to the **single-orbit hyperbolicity** of the section (positivity of `det H_d` along the diagonal
= Pólya–Jensen / GORZ) — a **positivity/sign** statement, the project's recurring wall, now in a sharp
finite-free form (its Door-2 status is the next gate). The structural lemma and Lemma R stand as proven;
only the reducibility-as-RH conjecture is refuted. Details:
`../pipeline/1-in-progress/combination-mode-baker-reducibility.md`, `../pipeline/1-in-progress/finite-free-convolution-flow.md`.

**C3 folds into C5 (2026-06-19).** Working the C3 ticket to its end showed the **native invariant is not
independent of the native theorem**. The joint-vs-per-prime *gluing* of multi-`q` modules is genuinely
finer than per-prime data (explicit rank-2 two-prime witness: per-prime conjugate, `tr(A_pA_q)` differs),
so a joint invariant exists — **but every gauge-combinatorial one** (curvature `[A_p,A_q]`, joint
conjugacy, word-traces) is a **character-variety pullback** (Procesi), with the `σ_p` inert and `(log p)`
absent ⟹ BRIDGE (the same failure as corank #23). The arithmetic of the primes enters the module
classification **only** through the *quantitative* trivialization of cocycles (transfer-function
regularity) = the combination-mode object of **C5★**. Hence **C3-native ⟺ C5★**: closing C5 closes C3,
and there is no cheaper native invariant. Proven:
`../pipeline/2-fully-proven/c3-gluing-invariants-bridge.md`; the independent-C3 goal failed:
`../pipeline/5-failed/c3-native-invariant-door3.md`. *(Consequence for the milestone: C3 and C7 both
reduce/couple to C5 — with **C6 now MET** (bridge level; see below), the branch hinges on C5 (C3
reduces to it, C7 couples to it).)* **Follow-ups spawned (0-backlog):**
`../pipeline/0-backlog/multi-q-shafarevich-gluing-group.md` (the gluing invariant's native home `Ш` =
per-prime-trivial joint classes; `Ш_arith` vs C5★) and
`../pipeline/0-backlog/cross-prime-curvature-reducibility.md` (the curvature-language C5★ carrier —
coordinate-dependent `F_{pq}`, sibling of the finite-free carrier).

**C6 resolved → MET (bridge level, 2026-06-19).** The three border specialization functors are built and
verified (`../pipeline/2-fully-proven/c6-specialization-functors.md`): single-prime `S_p` recovers van der
Put–Singer; function-field `S_ff` recovers Deligne / Grothendieck / Papanikolas / Deligne–Katz; diagonal
`S_diag` recovers Bohr–Kronecker (#9). And `𝓜` **strictly extends** the single-prime border via the
**proven** difference-Hölder theorem (G1: ζ finite-base-holonomic at every truncation yet non-holonomic in
the limit — the §59 "faithful bridge" value made functorial). That satisfies the literal C6 test (recover
**and** strictly extend), so **C6 is MET at bridge level**. The *native/irreducible* strict extension (the
cleanest one, where the apparatus genuinely adds content) = **C5★**, still open — closing C6 does **not**
close C5; the branch still hinges on C5.

## Open core / the work package
1. **Door-2 re-test of §59/§60 — DONE: both FAIL (BRIDGE).** C5 remains open (see the verdict above).
2. **Re-test the §3 σ-parity = FE-parity weld** as the next candidate: does tying the cohomology grading
   to the FE reduce to a parent, or does it genuinely need the prime-lattice apparatus?
3. **The decades (task #66):** construct a genuinely irreducible theorem along the "forward" line above —
   the only thing that turns the programme into a branch.

## Cross-references
- [[G1-difference-holder]], [[G3-holonomy-dichotomy]] — the two re-test subjects.
- [[bucket-function-field-proving-ground]] — Door-5's proving ground (where all gatekeepers are theorems).
- [[bucket-ledger-footholds]] — which candidates already have axiom-clean Lean anchors.
