# R7 results (2026-07-03) — transfer graph of the D–H population, t ≤ 200 — [MEASURED]

Engines: `engine6.py` (chunk 0, winding-bisection localization), `engine5.py` (chunks 1–2,
circle returns). Raw here: `r7c0.out`, `r7c1.out`, `r7c2.out`. Pre-registrations: board
(R7 chunk-1 block).

## Chunk 0 — localized zeros (winding-certified, ±0.01)

| | β | t | w |
|---|------|---------|---|
| ρ₁ | 0.8065 | 85.695 | 1 | (the banked zero)
| ρ₂ | 0.6555 | 114.164 | 1 |
| ρ₃ | 0.5693 | 166.477 | 1 |
| ρ₄ | 0.7202 | 176.695 | 1 |

Derivative-magnitude proxies (margin/r): |f′(ρ₁)| ≈ 1.16, |f′(ρ₂)| ≈ 0.75,
|f′(ρ₃)| ≈ 0.42, |f′(ρ₄)| ≈ 1.16-ish (from pair-14 margins).

## Chunk 1 — the β-proximity law test (pre-registered): PARTIALLY REFUTED, refined

Pre-registered law: sub-margin ⟺ r ≳ 1.05·|Δβ|; ratio ≈ Δβ/r (±25%).

- **Pairs anchored at ρ₁ (jet-matched): LAW HOLDS.**
  - 1→4 (Δβ = 0.086): sub-margin from r/Δβ ≈ 1.2; ratios track Δβ/r within ~10% at all
    four radii. (The R6-loc edge, re-confirmed.)
  - 1→3 (Δβ = 0.237): sub-margin at r = 0.285, 0.290 (ratios 0.999, 0.994 — borderline
    but strict); ratios track Δβ/r. **NEW certified transfer edge ρ₁ → ρ₃ across
    Δβ = 0.237.**
- **Pairs involving ρ₂: LAW FAILS with an r-independent floor.**
  - 1→2 (Δβ = 0.151): no sub-margin even at r/Δβ = 1.5; ratio plateaus ≈ 1.17.
  - 2→3, 2→4: ratios 1.6–3.0, far above Δβ/r; clause (i) FAILS at 1.5× for all three.
- 3→4: under-radiused by design error (base ρ₃ sits 0.049 from the σ = 0.52 cut; radii
  0.32–0.52·Δβ decide nothing). Re-run rebased at ρ₄ (chunk 2).

Scorecard vs pre-registration: clause (i) 11/14 decidable OK, 3 FAIL (all ρ₂-pairs);
clause (ii) 8/24 (exactly the ρ₁-anchored pairs). **Verdict: the naive β-law is refuted
as universal; it is the correct LEADING TERM for jet-matched pairs.**

## The refinement (the actual finding)

The measured ratio behaves as ratio ≈ Δβ/r + δ′, with δ′ an r-independent floor set by
the DERIVATIVE mismatch: ρ₂'s |f′| ≈ 0.75 vs ρ₁,ρ₄'s ≈ 1.16 (and the floor ordering
follows the mismatch ordering). Vertical shifts can move neither β nor the jet moduli:

> **Transfer condition = JET proximity: sub-margin ⟺ r ≳ |Δβ| AND the derivative data
> match (δ′ small). The transfer graph stratifies into jet-classes; within a class it is
> a β-proximity graph.**

Certified edges so far: ρ₁ → ρ₄ (r ≥ 0.104), ρ₁ → ρ₃ (r ≥ 0.285). ρ₂ is
transfer-isolated from ρ₁, ρ₃, ρ₄ at r ≤ 1.5·Δβ — its jet class has its partners at
other heights (09 §1's positive-density returns land on jet-matched zeros; the t ≤ 200
window shows only this fragment of its class).

Consistency with 09: untouched — the theorem guarantees returns at every ε with positive
density; the graph fragment tells WHERE small-ε returns land (jet-matched partners), and
the ρ₂-isolation is a statement about this window, not about the return set.

Opened: (a) jet-class census — measure (β, |f′|, arg f′) for more zeros (t ≤ 500) and
test whether classes are discrete or a continuum; (b) refine the law's second term:
δ′ ≈ c·|Δf′|/|f′|? (needs f′ at the four centers — one tiny job); (c) 09 §3's
primitivity grading now has a concrete micro-version: jet classes as the "primitive
components" of the population.

## Chunk 2 — rebased pairs (raw: r7c2.out)

| pair | Δβ | r | ratio | pred Δβ/r | sub-margin? |
|------|--------|-------|-------|-------|-----|
| 4→3 | 0.1509 | 0.121 | 1.216 | 1.247 | no |
| 4→3 | 0.1509 | 0.151 | 1.023 | 0.999 | no |
| 4→3 | 0.1509 | 0.181 | 0.916 | 0.834 | **YES** |
| 4→3 | 0.1509 | 0.200 | 0.891 | 0.754 | **YES** |
| 4→2 | 0.0647 | 0.052–0.097 | 2.08 → 1.30 | — | no (floor) |

**Third certified transfer edge: ρ₄ → ρ₃** (τ = −10.22, r = 0.181), tracking the law with
a small excess (jet mismatch ≈ 0.1). 4→2 fails with the same signature floor as 2→4 —
ρ₂'s isolation is base-independent, hence intrinsic to its jet.

## Final t ≤ 200 graph fragment

Vertices {ρ₁, ρ₂, ρ₃, ρ₄}; certified edges {1–4, 1–3, 4–3}; ρ₂ isolated at r ≤ 1.5Δβ.
**Jet classes: {ρ₁, ρ₃, ρ₄} (complete subgraph) and {ρ₂}.** Pre-registered clause (iii)
corrected: the transfer graph is a jet-class-stratified β-proximity graph. Caveat logged:
margin/r is a poor |f′| proxy at small radii (ρ₃'s tiny-r proxy 0.42 contradicts its
demonstrated transfer-compatibility at r = 0.18); the class census should measure f′ at
centers directly. Opened: jet-class census at t ≤ 500 (chunked); does the class partition
correlate with any arithmetic invariant of the zeros; second-term calibration of the law.
