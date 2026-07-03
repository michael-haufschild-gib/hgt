# R8 results (2026-07-03) — jet census — [MEASURED]

Pre-registration: board wave-4 block (seed 382100489098707208). Chunk 0 raw: `r8c0.out`
(local, `computations/mwm/fprime.py`, central difference h=1e-8, dps 30).

## Chunk 0 — direct jets at the four R7 centers

| | β | t | |f′| (direct) | arg f′ | margin/r proxy (R7) |
|---|------|---------|-------|---------|------|
| ρ₁ | 0.8065 | 85.695 | 1.2586 | −0.1922 | 1.16 |
| ρ₂ | 0.6555 | 114.164 | 0.9254 | +0.3215 | 0.75 |
| ρ₃ | 0.5693 | 166.477 | 0.6183 | −0.3234 | 0.42 |
| ρ₄ | 0.7202 | 176.695 | 1.2110 | −0.2566 | ~1.16 |

Scorecard vs pre-registration: (i) |f′(ρ₂)| vs class {ρ₁,ρ₄}: 24–26% — MARGINAL FAIL of the
≥30% clause. (ii) proxy-was-bad clause CONFIRMED (ρ₃: 0.42 → 0.618 direct). But the falsifier
fired in an unexpected direction:

**VERDICT — |f′|-magnitude is REFUTED as the jet-class carrier.** ρ₃ has the LOWEST |f′| of
all four — farther from ρ₁ (1.259) than the isolated ρ₂ (0.925) — yet ρ₃ receives certified
transfers from ρ₁ and ρ₄ while ρ₂ receives none. Magnitude ordering cannot produce the
measured graph.

**The carrier is the PHASE.** arg f′ clusters exactly as the transfer graph does:
{ρ₁, ρ₃, ρ₄} at arg f′ ∈ [−0.32, −0.19] (spread 0.13), ρ₂ alone at +0.32 (distance ≥ 0.51
from every class member). |Δ arg f′| per pair: (1,4)=0.064, (4,3)=0.067, (1,3)=0.131 —
the three certified edges; (1,2)=0.514, (4,2)=0.578, (2,3)=0.645 — the three failures.
Perfect separation with a factor-4 gap.

**Second-term calibration (rough).** Reading the R7 ratio tables as ratio ≈ Δβ/r + δ′:
class-separating edges give δ′/|Δ arg f′| ≈ 0.98–1.45 (1→2: 0.50/0.514; 4→2: 0.63–0.84/0.578);
in-class edges give order-unity but noisy values (1→3: 0.17/0.131 ≈ 1.27; 4→3: 0.02–0.14/0.067).

> **Refined jet-proximity law [MEASURED]: ratio ≈ Δβ/r + c·|Δ arg f′|, c = Θ(1) (≈ 1.0–1.4
> on the well-measured edges).** Transfer ⟺ r ≳ |Δβ| and the local conformal DIRECTIONS agree.

Geometric reading: a Rouché return needs f(·+iτ) to track f around the seed circle; a phase-
rotated jet rotates the image curve, and the sup-norm mismatch on the circle picks up
|f′|·r·|Δ arg f′| to first order — dividing by margin ≈ |f′|·r gives an r-independent floor
≈ |Δ arg f′| with coefficient 1. The measured c ≈ 1.0–1.4 MATCHES this first-order model.
The law is now derived, not just fitted: **floor = |Δ arg f′| + O(r·|f″|/|f′|)**.

Opened: (a) the phase is a NEW sort key for the population — chunk A census records
(β, |f′|, arg f′) triples; are phase classes discrete (lattice?) or a continuum with
transfer-radius ~0.15? (b) phase-weighted universality: 09/10's universality imports are
phase-blind; the measured returns select on phase. Is there a joint-universality statement
conditioned on jet direction? (c) does arg f′ at D–H zeros correlate with an arithmetic
invariant (character angle χ(2)=i suggests quarter-turn structure)?

## Chunk A — census t ∈ [200, 320) (raw: r8a.out; pod, engine6, σ > 0.52)

ONE new zero: **ρ₅ = (0.8653, 240.398)**, w = 1 (simple), highest β in the population so far.
Sparse vs R2's T/21 average (~5.7 expected in 120 units; chunk 0's window gave 4) — either
clustering variance or zeros hugging σ ∈ (0.5, 0.52] below the cut; noted, not resolved.
Caveat: boxes whose winding integration fails are skipped silently.

Jet at ρ₅ (local, appended to r8c0.out): |f′| = 1.5637, **arg f′ = +0.2559**.

Phase-prediction scorecard (board, chunk 0′ block): CLUSTERING CONFIRMED, band missed —
ρ₅ does not scatter; it lands 0.066 from ρ₂ (+0.3215), i.e. it JOINS the second cluster.
The five-zero phase population is two tight clusters:
{ρ₁ −0.192, ρ₄ −0.257, ρ₃ −0.323} and {ρ₅ +0.256, ρ₂ +0.322} — intra-cluster spread ≤ 0.13,
inter-cluster gap ≥ 0.45. ρ₂ is not an outlier; it was the first-seen member of a CLASS.

`[CONJECTURE]` The two clusters sit near ±0.28 — a sign structure. If phase classes realize
a finite group (ℤ/2 here; χ(2) = i suggests testing for a hidden 4-fold), the jet phase is a
COARSE GRADED INVARIANT of exactly the kind the lane's w_k language wants: monodromy data
visible in the jets of the off-line population. Census chunks B/C grow the sample to test
2-cluster vs 4-cluster vs continuum.

## Chunk C pre-registration — the β-law vs phase-law duel at ρ₅

The two laws now make OPPOSITE predictions on the same zero:

| pair | Δβ | |Δ arg f′| | β-law says | phase-law says |
|------|------|--------|-----------|----------------|
| 1→5 | 0.0588 | 0.448 | transfer at r ≳ 0.062 | blocked: floor ≈ 0.45; no sub-margin for r ≤ 0.089 |
| 2→5 | 0.2098 | 0.066 | hard (large Δβ) | transfer at r ≳ 0.24; ratio ≈ Δβ/r + 0.07 |

PRE-REGISTERED (before any run): (i) 2→5 (τ ≈ 126.234) reaches sub-margin at r ∈
{0.24, 0.28, 0.315} with ratio within ±0.1 of Δβ/r + 0.066. (ii) 1→5 (τ ≈ 154.703) FAILS at
r ∈ {0.059, 0.072, 0.089} with excess over Δβ/r of 0.45±0.15. (iii) Large-r probe 1→5 at
r ∈ {0.15, 0.20, 0.25}: IF the floor is additive, sub-margin appears by r ≈ 0.20–0.25
(ratio → 0.5–0.7); IF the ratio plateaus ≥ 1, the additive form is refuted and the phase
term is a hard gate (max/multiplicative). FALSIFIER of the phase law itself: 2→5 failing
everywhere while 1→5 succeeds at small r.

## Chunk B — census t ∈ [320, 420) (raw: r8b.out) + the 9-point phase population

Four new zeros (all simple): ρ₆ = (0.8228, 320.883), ρ₇ = (0.7697, 331.055),
ρ₈ = (0.6316, 366.648), ρ₉ = (0.8122, 411.789). Chunk A's lone zero was a lull;
population density back near R2's rate. Jets (direct, appended to r8c0.out):

| | β | t | |f′| | arg f′ |
|---|------|---------|-------|---------|
| ρ₁ | 0.8065 | 85.695 | 1.259 | −0.192 |
| ρ₂ | 0.6555 | 114.164 | 0.925 | +0.322 |
| ρ₃ | 0.5693 | 166.477 | 0.618 | −0.323 |
| ρ₄ | 0.7202 | 176.695 | 1.211 | −0.257 |
| ρ₅ | 0.8653 | 240.398 | 1.564 | +0.256 |
| ρ₆ | 0.8228 | 320.883 | 1.769 | −0.280 |
| ρ₇ | 0.7697 | 331.055 | 1.425 | −0.257 |
| ρ₈ | 0.6316 | 366.648 | 1.018 | +0.068 |
| ρ₉ | 0.8122 | 411.789 | 1.651 | −0.437 |

**Cluster-claim REVISION (against our own chunk-A reading).** Sorted phases:
−0.437, −0.323, −0.280, −0.257, −0.257, −0.192, +0.068, +0.256, +0.322. The negative group's
spread grew to 0.245 (was ≤ 0.13 at n=5) and ρ₈ interpolates between the old clusters. The
crisp two-cluster/ℤ2 conjecture is WEAKENED at n=9: the distribution is not uniform (knots
exist — ρ₄, ρ₇ IDENTICAL to 4 digits at Δt = 154; ρ₆ within 0.023) but is richer than two
points; current best reading = local knots, possibly a continuum with concentrations. The
pairwise phase-proximity law is untouched by this (it never needed global discreteness).

Two trends worth follow-up: |f′| grows with t (0.62 at t=166 → 1.77 at t=321 — log t
scaling?); arg f′ shows no t-trend. Sharpest new prediction from the table: **ρ₄ → ρ₇**
(Δ arg f′ = 0.0000, Δβ = 0.0495, τ ≈ 154.36) should be the best transfer edge in the whole
population — floor ≈ 0, ratio ≈ Δβ/r cleanly. Chunk D candidate alongside ρ₈'s
intermediate-phase probes (8→1: Δarg 0.26; 8→5: Δarg 0.19).

## Chunk C — the duel verdict (raw: r8c1.out, r8c2.out): BOTH naive laws lose

| pair | r | margin | best d | ratio | sub-margin? |
|------|------|--------|--------|-------|----|
| 2→5 | 0.24 | 0.0799 | 0.7369 | 9.22 | no |
| 2→5 | 0.28 | 0.0408 | 0.8137 | 19.95 | no |
| 2→5 | 0.315 | 0.0165 | 0.8830 | 53.51 | no |
| 1→5 | 0.059 | 0.0673 | 0.1497 | 2.23 | no |
| 1→5 | 0.072 | 0.0831 | 0.1621 | 1.95 | no |
| 1→5 | 0.089 | 0.1037 | 0.1788 | 1.73 | no |
| 1→5 | 0.15 | 0.1746 | 0.2441 | 1.40 | no |
| 1→5 | 0.20 | 0.2292 | 0.3048 | 1.33 | no |
| 1→5 | 0.25 | 0.2807 | 0.3712 | 1.32 | no |

Scorecard vs pre-registration: clause (i) REFUTED (2→5 fails catastrophically); clause (ii)
direction CONFIRMED, magnitude wrong (floor ≈ 1.1, not 0.45); clause (iii) resolved to the
HARD-GATE branch (1→5 ratio saturates at ≈ 1.32 > 1 as Δβ/r → 0.23 — no large-r rescue).
The falsifier ("2→5 fails while 1→5 succeeds") did NOT fire: 1→5 never transfers either.

Two identified mechanisms behind the failures:
1. **Line-proximity cutoff (geometric, new).** 2→5 needs r ≳ Δβ = 0.21, but ρ₂ sits only
   0.156 from the critical line: the required circle STRADDLES the zero-dense line and the
   margin collapses (0.08 → 0.016 with growing r). A zero can only receive β-distant
   transfers if its distance to the line exceeds Δβ. ρ₂'s R7 isolation was overdetermined:
   phase mismatch AND no geometric room.
2. **The floor is the FULL COMPLEX jet difference, as a hard gate.** First-order model
   (centers aligned at τ*): d ≈ r·|f′_tgt − f′_base| + |f′_tgt|·Δβ, margin ≈ |f′_base|·r,
   so ratio ≈ |Δf′|/|f′_base| + (|f′_tgt|/|f′_base|)·Δβ/r — amplitude AND phase enter
   through |Δf′|; the floor term does not decay with r. For 1→5: |Δf′|/|f′₁| = 0.55
   predicted vs ≈ 1.1 measured — the model captures the shape (saturation) but
   under-predicts by ~1.4–2×; second-order (f″) correction unquantified.

> **Law, current form [MEASURED]: transfer ⟺ r ≳ (|f′_tgt|/|f′_base|)·Δβ AND
> |Δf′|/|f′_base| well below 1 AND r < dist(base, critical line).** Full-jet proximity
> plus geometric room. All three R7 certified edges satisfy all three clauses; all six
> measured failures violate at least one.

## Chunk D pre-registration — the calibration pair ρ₄→ρ₇ (best full-jet match)

ρ₄ = (0.7202, 176.695), f′₄ = 1.211·e^{−0.2566i}; ρ₇ = (0.7697, 331.055),
f′₇ = 1.425·e^{−0.2571i}. Δβ = 0.0495, |Δf′|/|f′₄| = 0.177, amp ratio 1.177,
line distances 0.22/0.27 (room OK), τ ≈ 154.360. PRE-REGISTERED: sub-margin at r = 0.14
under BOTH calibrations (pure model ratio 0.59; ×1.4 corrected 0.83); r = 0.09 and 0.11
discriminate the correction factor (pure: 0.82, 0.71 → YES; ×1.4: 1.15, 0.99 → NO/borderline).
Radii {0.07, 0.09, 0.11, 0.14}. FALSIFIER: no sub-margin at r = 0.14 refutes the full-jet
law's sufficiency side outright (best-matched pair in the population).

## Chunk D — calibration verdict (raw: r8d.out): must-pass PASSED, κ ≈ 1.25

| r | margin | best d | ratio | sub-margin? | pure model | ×1.4 model |
|------|--------|--------|-------|----|------|------|
| 0.07 | 0.0735 | 0.0880 | 1.197 | no | 1.01 | 1.41 |
| 0.09 | 0.0972 | 0.0954 | 0.981 | YES | 0.82 | 1.15 |
| 0.11 | 0.1207 | 0.1032 | 0.855 | YES | 0.71 | 0.99 |
| 0.14 | 0.1554 | 0.1157 | 0.744 | YES | 0.59 | 0.83 |

**Fourth certified transfer edge: ρ₄ → ρ₇** (τ = 154.355, Δt = 154.36 — the largest
certified transfer distance yet). The full-jet law's sufficiency side CONFIRMED on the
best-matched pair; measured ratios sit uniformly at ≈ 1.2–1.3 × the first-order model:

> **Final R8 law [MEASURED]: ratio ≈ κ·( |Δf′|/|f′_base| + (|f′_tgt|/|f′_base|)·Δβ/r ),
> κ ≈ 1.25, valid when r < dist(base, critical line); the jet term is a hard gate.**

R8 arc CLOSED. Population t ≤ 420: nine zeros, four certified edges (1→4, 1→3, 4→3, 4→7),
law derived + calibrated, two structural discoveries (phase/jet carrier; line-proximity
cutoff). Opened and NOT pursued by more computation (theory takes over, doc 11): what
forces copies at all — the recurrence-degree analysis now locates the answer in class
rigidity, not a.p. strength.
