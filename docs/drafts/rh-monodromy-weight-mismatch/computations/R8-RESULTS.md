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
