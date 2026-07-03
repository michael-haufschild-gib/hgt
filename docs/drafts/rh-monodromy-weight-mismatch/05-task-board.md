# MWM task board — wave 2 (after Arc A + R1–R3)

State on entry (2026-07-03): Arc A fully formalized and gated; campaign R1–R3 closed
(findings in `worklog.md`); mechanisms after audit: M1 primary, M2 downgraded, M3 only as
FE ∧ positivity. Sequencing rule: **C2 first** (it gates the novelty inventory), then
paper-math (C1) and cheap compute (R3b/R5) interleaved; Arc B after checks #3/#7/#8.
Entropy discipline per research-rules §4 at every open choice.

## C-arc — mechanism (the theory spine)

**C2 — Bagchi verified reading (check #1). GATING, do first.**
Fetch and read the actual statements: Bagchi 1981 thesis ("The statistical behaviour and
universality properties of the Riemann zeta-function...") and the Math. Z. (~1982) paper.
Answer: (a) is strong recurrence sup-norm-on-compacts of the open strip? (b) does his proof
pass through zero-counting/Rouché+density (if so, is the mod-2^k coarsening implicit)?
(c) any follow-up stating a coarse/topological-invariant version? Outcomes: implicit →
novelty item 2 (00-approach §10) downgrades to "grading + formalization of known"; absent →
item 2 stands. Deliverable: check-note appended to worklog.md + §8/§10 updated in place.
Method exception: positioning literature lookup, sanctioned.

**C0 — bundled checks #2/#3/#4/#5/#7/#8 (one verified-reading session).**
- #8 first (fresh data wants it): known theorems on D–H off-line zero density (Davenport–
  Heilbronn 1936 original; Balanzario–Sánchez-Ortiz numerics; positive-proportion results for
  linear combinations, Bombieri–Hejhal adjacent). Compare with measured T/21.
- #3 Hamburger exact hypotheses (bounds Arc B's search space).
- #2 random Euler product a.s. convergence/nonvanishing σ > 1/2 (fixes 00-approach §4.3).
- #5 any literature on multiplicity parity of hypothetical off-line zeros (expect none —
  confirms the ladder's novelty-candidate status).
- #7 Bohr almost-periodicity ⟺ zero-free statements (perimeter of §4.3).
- #4 DRH/partial-Euler on the critical line (Conrad; Kurokawa school).
Deliverable: one check-note; every §8 [CHECK] item resolved to verified/refuted-with-citation.

**C1 — the Reduction, rigorous paper proof.**
Theorem: fix σ₀ > ½, H > 0, k ≥ 1; if the defect set {T : w_k(T) ≠ 0} is relatively dense
once nonempty, then lim sup N(σ₀,T)/T > 0; with Ingham ⟹ w_k ≡ 0 ⟹ (box-shrinking)
2^k ∣ ord at every zero right of σ₀. Full care: boundary zeros (a.e. boxes / interior
winding), the box-shrinking localization, quantifier order over (σ₀, k). Write as
`06-reduction.md` in this directory (paper note, LEDGER-candidate register with explicit
hypotheses). Lean version later as its own card (Ingham as named hypothesis — NOT an axiom).
Depends on: nothing (C2 only repositions the writeup's claims).

**C3 — explicit formula as index formula (M1 made precise).**
(a) w_k as ∮ ξ'/ξ mod 2^k, connect to S(T)-type quantities mod 2^k; (b) inventory
parity-sensitive test-function families (ledger says linear probes are β-blind — the absence
is the opening); (c) transpose the `index_formula_split` + resonance-pinning pattern: state
M1 as a conditional theorem ("defect term's spectral content vs the {j log p} side ⟹
recurrence"), isolate its hypothesis as the new open core. Depends on C1.

## Arc B — parity in FE ∧ positivity (open math; after C0's #3/#7/#8)

**B1 — FE-grafting hunt (attack-as-false).** Start from DMV positive systems; ask whether an
FE can be grafted; if "Beurling + FE" is provably thin (Hamburger-type), the emptiness proof
IS a parity theorem for that class and direct progress on realization problem #85. Either
exit terminalizes (pipeline card when the statement stabilizes).

**B2 — L1-lemma attempts.** FE ∧ positive-log ⟹ divisibility/pairing structure on the
divergence-strip divisor: paper attempts, each failure names the missing Euler feature.
Wild-analogy slot (scripts/rng) when plateaued.

**B3 — real-structure equivariance (small Lean).** Conjugation-symmetric cycles carry even
winding; level-1 obstruction lives on classes separating ρ from ρ̄. Needs `xi_conj`
(probe `completedRiemannZeta₀` conjugation lemma in mathlib; if absent, derive from
Hurwitz-zeta layer or state on abstract f with f(s̄) = conj f(s)). Extends RHTower.

## R-campaign — wave 2 (all parallel-batched on the pod, minutes each; results →
`computations/` here, per standing order)

**R3b — FE-minimum replication, window 2.** Same k-scan over t ∈ [150, 200) (contains the
banked-adjacent defects at ~167, ~177). Pre-register: minimum again at the FE fiber; floor
count = the window's D–H zero count (2); linear plateau scaling replicates.

**R3c — pinning order + exponent refinement.** Bands σ₀ ∈ {0.5025, 0.505, 0.51} × fine k;
track WHICH zeros exit the band last as k → κ (pinning order vs height/initial σ); refine
the width coefficient. Deliverable: defect-velocity per zero — the family's "spectral gap"
profile.

**R5 — NEW: the Euler-approach profile (the opened question).** Extend the pencil to complex
c: walk c from the D–H point (1−iκ)/2 toward c = 1 (pure L(s,χ) — Euler product, GRH-clean
in range). Measure the off-line defect count along the path (window t ≤ 200, band σ₀ = 0.51).
Pre-register: count decreases to 0 at c = 1; the SHAPE near c = 1 (linear vanishing vs
threshold) is the observable — "the Euler cut as the second, deeper minimizer." Any pinned
defect that survives to near c = 1 would be a major anomaly (early-fail sensor for the family
picture). Engine: f_pencil generalized to complex c (small edit).

**R4 — (unchanged, optional)** three-way extreme-statistics comparison; run only on momentum.

## Bookkeeping / publication track

**P1 — mailbox post to the parent lab** after C2 + C1: the RH_{2^k} ladder + tower Lean bank
+ the FE-minimizer measurement (ledger-aligned: B7 shape + proof_shape's "fake families
producing unsanctioned linking"). Flag the Bagchi verdict honestly; don't oversell.

**P2 — fold RHTower into the publication surface** (formalization-paper.md section or a
standalone short note "A machine-checked multiplicity-parity ladder for RH") — decide AFTER
C2's novelty verdict. Card gate 3 → 4 rides on this.

**A3 — (deferred until C1 fixes the invariant)** formalize the cocycle w_k (argument-principle
mod 2^k); check the atlas's formalized Schur–Cohn winding=inertia bridge for reuse before
writing new Lean (audit F5).

## Default order

C2 → C0 → R3b + R5 (parallel with C1 writing) → C1 → C3 → B1/B2 → R3c → P1 → P2.
At each session start: `scripts/rng seed`; if two consecutive sessions only re-derive,
force a wild-analogy collision on B2 (research-rules §4).

---

## Wave-2 status (2026-07-03, second half of day)

DONE: **C2** (delegated verified reading, spot-checked — Bagchi confirmed, mechanism =
full-magnitude count, coarsening ABSENT-FROM-LITERATURE; §8/§9/§10 of 00-approach updated,
`checks/c2-bagchi-note.md`); **C1** (`06-reduction.md` — (D) × (R_k) ⟹ RHLadder k, cluster-sum
subtlety handled, level-1 corollary isolated); **R3b** (window-2 replication exact, coeff 4.0);
**R5** (profile 4 → 29 → 0; Euler point exact minimizer, no anomaly; linear flux n ≈ 120(1−u)
near u = 1). C0 delegated, in flight. Results: `computations/R3b-R5-RESULTS.md`, worklog.

NEW (opened by wave 2):
**R5b — near-Euler mobility scan.** u ∈ [0.90, 1.0] step 0.005, σ₀ = 0.51, t ≤ 200.
Pre-register: the linear law n ≈ 120·(1−u) persists at fine resolution (no staircase
clustering, i.e. wall-crossings u* roughly uniformly spread); n(0.995) ∈ {0,1,2}; n(1) = 0.
Deliverable: per-zero wall-crossing estimates u* (mobility distribution) → cross with R3c.
**C4 = [CHECK #9] — where density proofs consume the Euler product.** Verified reading of
Carlson/Ingham-style density proofs (mollifier coefficients? mean-value inputs?) + the precise
structural reason D–H evades them (it must: measured T/21). Feeds §4 of 06-reduction.md.

## Wave-2 status, second update (2026-07-03 evening)

DONE since last block: **C0** (all six checks verdicted, `checks/c0-checks-note.md`; #5 ABSENT
⟹ §10.1 ladder novelty VERIFIED-ABSENT — with C2, both gating novelty items survived; my added
caveat: Lamzouri–Lee's near-line asymptotic needs G(T)→∞, fixed-strip linear rests on the
unfetched Bombieri–Hejhal pointer); **(R_k) weakened** to conditional positive UPPER density
(Bagchi's own limsup register — user-relayed GPT nuance, verified verbatim, 06-reduction.md
amended, proof adapted); **R5b** (linear flux to u≈0.955, then collapse + defect-free EULER
MOAT u∈[0.98,1]; mobility ranking banked). New: **R5c** (moat scaling in T, #106, pre-register
first). Remaining default order: **C3 → B1/B2 (+B3 small) → R3c/R5c → P1 → P2**; C4 (#105)
delegatable alongside C3. Hooks for C3/P-track: DRH's √2^{ν(ρ)} factor = literature's one
multiplicity-sensitive Euler-product law (on-line central) — cite as adjacent, distinguish
off-line ladder; 237/237 simplicity is publishable new data (no counterpart).

## Wave-2 status, third update (2026-07-03 night)

**C3 DONE** (`07-index-formula.md`): M1 is now a theorem with one isolated hypothesis —
Rouché-transfer + (H_k) ⟹ (R_k); (D) + (H_k ∀k) ⟹ RH. **C4 delegated** (#105, in flight:
density-proof Euler-input + Bombieri–Hejhal exact statement + Speiser + Levinson–Montgomery).
**R6 launched** (#107, pre-registered in 07 §5.1): return-set measurement at the certified
defect box [0.53,1.2]×[166,168], τ ∈ [0,400] step 0.1, 120-pt boundary proxy, winding
certification for candidates. R6 discriminates "defects recur because data returns
(M1/(H))" vs "defects recur for a weaker reason" — either verdict reshapes M1. Remaining:
B1/B2/B3 (B3 next: xi_conj mathlib probe), R3c/R5c, P1 (after C4), P2.
