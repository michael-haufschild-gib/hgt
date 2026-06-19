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
  `𝕋^∞⋊σ` relabeled); **C5 NOT MET — the gap**; C6 **PARTIAL**; **C7 NOT MET**.
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

**What a real C5 theorem needs (forward).** Use the `σ_p` **jointly and irreducibly** — a statement
whose proof does NOT factor through (the single shift `s↦s+1`) + (Kronecker–Weyl on `𝕋^∞`). The places
to look are the multi-`q` connection's curvature / integrability (the joint structure of the `{σ_p}`,
not one diagonal shift) or the joint group `G_L`'s monoidality class `ω`
([[G4-multi-q-picard-vessiot-and-langlands-group]]) — not the diagonal's hypertranscendence.

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
