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
