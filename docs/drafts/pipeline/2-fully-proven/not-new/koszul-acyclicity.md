# Koszul-acyclicity (G15) — the multiplicative limit IS acyclic; G15 is the Koszul face of ω=0, not a new gatekeeper

- **ID:** koszul-acyclicity
- **Stage:** 0-backlog-lean
  the RH half (ω=0) is the marked open core (= #27, FIELDS-MEDAL).
- **Type:** THEOREM (paper, structural verdict) — Door **BRIDGE (substrate)**
- **Priority:** FUTURE
- **Source:** #73 SEED-R / #79 SEED-T (`bucket-new-sibling-conjectures`), G4 bucket · 00-status row #99;
  uses #27 §R (`compute-omega-h2-gl`: `H(t)E(−t)=1` in the limit ring `Λ`), the ledgered `eh_koszul_duality`
  (`EHKoszulDuality.lean`) and `additive-koszul-cocycle-skeleton` (3-formalized), #137/#148 (orthogonality).
  Prior research checked (standing order): SEED-R + §20/§32 of support-extraction-log (difference cohomology
  `H^*_σ=H^*(ℤ^{(P)},M)`, rank-1 acyclicity dichotomy) are the seeds; no 5-failed prior.
- **Original candidate (G15):** read `ω ∈ H²(G_L)` as the Koszul homology of the prime lattice in the `∏_p`
  limit; **"RH / Tannakian ⟺ no Koszul homology condenses in the limit."** Open 1→2 question (card's own):
  *does the finite `e–h` acyclicity survive `∏_{p≤P} → ∏_p`?*

## Verdict — the multiplicative limit IS acyclic (proven); G15 = the Koszul face of ω=0
The candidate's posed question is answered for the multiplicative complex, and G15 is thereby consolidated.

### §1 The complex `[setup]`
The prime lattice `ℤ^{(P)}` acts via `{σ_p}`; its difference (group) cohomology `H^*_σ(M)=H^*(ℤ^{(P)},M)`
carries the Koszul/exterior structure (support-log §20). The monoidality obstruction is `ω ∈ H²`. The
multiplicative wing is the `e–h` / `∧•V ⊣ Sym•V` Koszul pair, with reciprocity `E(x)H(x)=1`.

### §2 The multiplicative ∞-prime Koszul stays acyclic in the limit — UNCONDITIONAL `[PROVEN, cites #27 §R]`
The finite shadow `Σ_{i+j=k}(−1)^i e_i h_j = 0` is ledger-proven (`eh_koszul_duality`). #27 §R proves it
**survives the limit**: `H(t)E(−t) = 1` holds in the limit ring `Λ` (the `∏_p` symmetric-function limit), so
the **multiplicative ∞-prime Koszul complex is acyclic** and its homology does **not** condense — and this is
**independent of RH** (it is the `λ`-ring reciprocity, true always). 

> **Consequence.** "Koszul-acyclicity ⟺ RH" is **FALSE for the multiplicative complex**: acyclicity holds
> unconditionally. The card's open question ("does acyclicity survive the limit?") is answered **YES on the
> multiplicative side** — so no RH-bearing class can live there.

### §3 The RH content is the ARCHIMEDEAN-completed Koszul = ω=0 = #27 `[reduction]`
Since the multiplicative homology is acyclic in the limit (§2), any nonzero `ω` is carried **entirely by the
archimedean regularization counterterm** (#27 §R, verbatim; #137/#148: the multiplicative wing is
archimedean-content-free). Hence the RH-bearing statement is **not** the multiplicative Koszul-acyclicity but
the **archimedean-completed** one:
> **RH ⟺ the archimedean-completed prime Koszul complex is acyclic ⟺ `ω = 0`** — which is exactly
> `compute-omega-h2-gl` (#27), the open core.

**So G15 is not an independent gatekeeper.** It is the **Koszul-homological face of `ω=0`/#27**: the
multiplicative half is a proven acyclicity (RH-blind), and the RH half *is* `ω=0`. The "fourth language" the
card sought is genuine, but it names the **same** archimedean obstruction (#27), not a new RH-route — exactly
the orthogonality pattern (#137/#148: prime/multiplicative ⟂ RH; the archimedean carries it).

### §4 Honesty / Door
- **Not RH, not C5.** §2 is the `λ`-ring reciprocity (parent-grade); §3 reduces to #27 (= RH). Value: the
  candidate is **resolved** (multiplicative half proven, RH half = #27), pruning an apparent independent
  gatekeeper — substrate housekeeping, BRIDGE.
- **Door-5:** over `F_q` the single Frobenius / `corank=1` makes the completed complex acyclic with no
  archimedean defect (`ω` trivial), so G15 is satisfied = Weil; number-field-only obstruction (#121/#125).

## Gates
- [x] 0 → 1: complex pinned; `ω = H²`; finite `e–h` floor stated.
- [x] 1 → 2: **multiplicative-limit acyclicity decided = YES, unconditional** (§2, #27 §R `H(t)E(−t)=1` in
  `Λ`); G15 consolidated to the Koszul face of `ω=0`/#27 (§3); honesty/Door (§4). BRIDGE (substrate).
- [ ] 2 → 3: finite `e–h` + additive-Koszul skeleton already in `3-formalized`; the limit/archimedean `ω` is
  #27's target, not separately formalizable here.
- [ ] 3 → 4: folds into the `ω`/#27 exposition as its homological face.

## Cross-references
- `compute-omega-h2-gl.md` (#27) — **G15 = its Koszul face**; the RH content (`ω=0`) lives there.
- `../2-fully-proven/universal-prime-side-orthogonality.md` (#148), `orthogonality-meta-theorem.md` (#137) —
  the multiplicative wing is RH-blind / archimedean-content-free (same pattern).
- `../3-formalized/additive-koszul-cocycle-skeleton.md`, `bucket-ledger-footholds.md` (`eh_koszul_duality`)
  — the proven finite/multiplicative acyclicity.

## Log
- 2026-06-19 — created in 0-backlog (G15, SEED-R/T: homological reading of `ω`).
- 2026-06-19 (DeWitt) — **resolved → 2-fully-proven (BRIDGE substrate).** Answered the card's open
  limit-question for the multiplicative complex: it **stays acyclic** (`H(t)E(−t)=1` in `Λ`, #27 §R) —
  unconditionally, RH-blind. Hence "Koszul-acyclicity ⟺ RH" is false for the multiplicative complex; G15 is
  the **Koszul face of `ω=0`/#27**, not an independent gatekeeper (the RH content is the archimedean-completed
  acyclicity = `ω=0`, open core). Prunes an apparent gatekeeper; consistent with #137/#148. Prior research
  grepped first; no web, no runpod.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the card admits the RH/`ω=0` half is the open core and only the finite/multiplicative Koszul anchors are formalized. The limit-ring statement `H(t)E(-t)=1` and the archimedean-completed `ω` reduction are not Lean theorems in this project.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.
