# 60 — The Full-Chain Audit: RH ⟸ … ⟸ the Open Cores, Every Link Typed

**Register: LEDGER for the status marks (each verified against the named file
this cycle); SEARCH for §4.** Purpose: the one-page truth about distance-to-RH
in the MWM lane — what is machine-checked, what is paper-proved, what is open,
and the exact statements of the open cores. Sources: docs 06/18/33/38/43/50–59;
Lean tree `RHTower/` at umbrella 8626 jobs, lint green, axiom-clean.

## 1. The trunk (banked, machine-checked)

| Link | Statement | Status | Anchor |
|---|---|---|---|
| T1 | RH ⟺ ∀k RHLadder(k) (2^k ∣ every off-line order) | **Lean** | `RiemannTower.rh_iff_forall_ladder` |
| T2 | RHLadder(k) ⟺ analytic 2^k-th root of ξ on Ω | **Lean** | `rhLadder_iff_root` |
| T3 | (ID) D(W) = L(W) + 2N(W); (WR_k) ⟺ RH_{2^k} | (ID) **Lean**; equivalence paper | `WindowRelation`; doc 18 §2 |
| T4 | Dictionary: D = deck class, L = seam/sign product, k=1 = Hardy sign reading; maximality no-go (mod-4 bit forced through DISC) | **Lean** | `DictionarySign`, doc 33 §§4–7 |

## 2. Route I — abstract reduction (parked, correct)

(D) zero-density o(T) [KNOWN: Ingham] × (R_k^θ) power-graded defect recurrence
[OPEN, RH-equivalent at ∀k] ⟹ RHLadder(k): **paper-proved**, quantified form
doc 06 §6 (burden T^{θ(σ₀)}, θ(σ₀) → 0 rightward). Mechanisms: M1 single-test
CLOSED (prime diagonal dominates); M2 REFUTED as soft (11 Thm B); M3 refuted
as positivity-alone. Live residue: Turán power-sum rungs (08 §7). Parked in
favor of Route II; the D–H family witnesses the (D)-vs-(R) division of labor.

## 3. Route II — the AFE-window bridge (the active spine)

Per-stratum architecture (doc 59 §3): **Ingham density governs depths
w ≫ 1/log T; windows govern w ≍ 1/log T; creation control governs in-window.**

| Link | Statement | Status | Anchor |
|---|---|---|---|
| W1 | (MOAT-shallow): shallow odd pairs self-exclude (η ≤ η₀ ≍ √(E*/M_r)) | **paper-proved** | doc 43 §6 |
| W2 | Deep pairs η ≥ 1/4 empty (χ-modulus valley forcing) | derivation + measured | doc 43 §2 |
| W3 | (MID-central): mid-band survivors ≤ K, localized to slip window | **Lean skeleton complete** | `MidCentral`, `DipKillsWiring` |
| W4 | (R2) per-instance order-1 + Rouché certificates | execution (interval tech banked) | doc 54 §3 |
| W5 | (R3) = (CR-density) | **OPEN — two live routes, §4** | docs 55–58 |
| W6 | Cofinality, measure clause (C1) | **paper-sketch proved** (Littlewood mean) | doc 59 §1 |
| W7 | Cofinality, horizontal threading (C2) | open; route 1 = strata-match audit | doc 59 §2 |
| W8 | Traversal across slip blocks | typed; (EPH) dodge [CONJECTURE] | doc 57 §3 |
| W9 | k ≥ 2 rungs: Hermite minor chain (HANK-fin)_k | [CONJECTURE]; mechanism iterates | doc 38 |
| W10 | (SPUR-R)/(S-mono) exactness arc (DISC reader theorem-grade) | partially banked; re-verify at promotion | docs 23–37, `Spur*` modules |
| W11 | Transport dichotomy: deep survivor ⟹ ζ-pair (per-instance Rouché) | [REDUCTION], new this cycle | doc 57 §3(a) |

## 4. The open cores, exactly (SEARCH register)

1. **(CR-density)** (W5). Route A: GAF σ-profile universality — zero intensity
   (1/4π)(log K)″, ε(c) → c/12π, open core = local-statistics universality of
   the deterministic multiplicative phases (doc 55 §6). Route B: mollified dip
   — counting layer **machine-checked this cycle** (`MollifiedDip.lean`:
   `dip_measure_lower`, `separated_dips_count_le`, `sliverCount_le_of_kernel`),
   open core = (K-bdd) ⟸ (K-bdd-∞)[proof skeleton: two-phase co-area + scale
   induction + Baker base case] × (SPEC-decay)[random-model spectral decay]
   (doc 58 §4). Numerically: true, constant 1/12π cross-validated twice.
2. **(EPH)** ephemerality in the level index (doc 57 §3b) — measured (P-DF3);
   if proved, (CR-density) leaves the critical path (Tier-0 budget).
3. **(C2)** horizontal threading (doc 59 §2) — likely dissolves into the
   strata-match audit (route 1); not analysis, bookkeeping.
4. **(WR-core)** (Route III, doc 18 §5): D ≡ L (mod 4) as one exact identity of
   boundary data — the deepest form; the Euler bridge between circle-modulus
   and line-gluing. Untouched this cycle; the constraint-not-flow apex.
5. **(HANK-fin)_k** (W9) + multiplicity thread (Lemma R) — the k ≥ 2 supply.

## 5. Honesty panel

- Every open core above is RH-equivalent-grade or strictly-open mathematics;
  no route claims to be "almost done." What the lane HAS: the burden relocated
  onto finite, boundary-computable, machine-checked-skeleton objects, with the
  open cores typed to single statements and, for W5, two independent live
  engines plus verified numerics and an explicit constant.
- Novelty inventory (gate-facing): the parity ladder + window relation +
  cascade skeleton + mollified-dip reduction + budget-tier audit + ergodic×
  transfer split + Littlewood-mean cofinality are lane-original; the closest
  literature (Gonek–Montgomery/Roy–You; Jensen–Pólya/GORZ) is positioned in
  docs 50 §7 and 38 §4 and reaches none of them.
- Consumption order for the next cycles, by expected leverage:
  (EPH) [walk-tier tools banked, could delete W5 from the critical path] →
  (K-bdd-∞) write-out [complete skeleton exists] → (C2)/strata-match audit →
  (SPEC-decay) [random-model computation] → (HANK-fin)_2 instance data.

## 6. Addendum (same day): Route C inserted at W5 — the designed carrier

Doc 55 §§7–8 (Langevin closed form ε(c) = L(c)/4π; the variance law; the
measured near-line CHIRALITY) + doc 61 (synthesis): a monotone-decreasing
log-scale carrier with frozen-term share ς is SELF-MOLLIFIED — Route B's
machinery (including `MollifiedDip.lean`, carrier-agnostic) applies to it with
no mollifier, and the kernel constant carries a designed e^{−m²/(K−m²)}
suppression. This adds:

- **Route C (design):** choose the tower carrier so the right-sliver creation
  constant is small by construction; consumer = doc 57 Tier 2 (one explicit
  (c₀, ε₀)), which never needed ε(c) → 0. Open items: (SM-bdd) at designed ς
  (kernel class, small target constant), and the block-static tower transport
  (doc 61 §4).
- Consumption order update: (EPH) → **P-SM probe adjudication → (K-bdd-∞)
  at large mean-share** (the co-area induction may terminate at depth 1
  against a dominant frozen term) → (C2) → (SPEC-decay) → (HANK-fin)_2.

## 7. Addendum (cycles 31–34): the Route C-direct spine

Docs 65–68 changed the map. (TIGHT) — the convexity-tangent mean-log floor —
closes the designed carrier's creation bound UNCONDITIONALLY with a free dial
ε₀ (doc 67), p-uniformly (doc 68 §2). The deck demand extracts as
SUBCRITICALITY r(N) ≤ c_deck·log N (doc 68 §1), so the meeting number is the
absolute constant ε₀* = c_deck/C′ — extraction, not analysis. Consequence
[REDUCTION-conjecture, doc 68 §4]: for the DESIGNED tower, W3/W4/W5/W8
collapse — the RH₂ rung runs ladder → window relation → (DOM-W) smoothed-AFE
domination → (MOAT-W)/(DEEP-W) transplants [read carrier-generic] →
plateau-split creation [unconditional] → cofinality (C1 corrected §59.4 + C2)
→ isolation. No cascade, no (CR-density), no (EPH) on the designed spine.
Open items on this spine, all classical-shaped: (DOM-W), the constants pass
(C′, c_deck), C2 strata-match, k ≥ 2 rungs (W9/W10 unchanged). The sharp-
carrier cascade tier is re-classified: explanation layer, not load-bearing.
Doc 59 §1's proof was corrected (§59.4 — convexity-tangent replaces the
broken Littlewood sketch; conclusions survive).
