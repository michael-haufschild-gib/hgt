# 44 — MOAT⁺ and Its No-Go: the Survivors Are Geometry-Irreducible

**Register: SEARCH** (task #130; route (3) of doc 43 §9, executed and refuted).
Certification: `computations/mwm/moat_plus.py` (P-M1/P-M2/P-M3 pre-registered).

## 1. Lemma MOAT⁺ [PROVED HERE — true, and measured ineffective here]

For any radius r and any subset S of Φ's zeros in the disc around
s₀ = 1/2 + it₀ (flanking on-line zeros z_j at distance d_j):

> |Φ(s₀)| ≤ η² · Π_{j∈S} [d_j/(r−d_j)] · M_r/(r−η)².

Same max-principle proof as doc 43 §6 with the S-zeros divided out of H; each
zero with d_j < r/2 strictly tightens. Two optimization dials: S and r.

## 2. The no-go measurement (all three dials dead at the survivors)

Applied to the 8 mid-band survivors with r ∈ [0.5, 1.5] and S automatic:

- **P-M1 FAIL, P-M2 FAIL — zero survivors killed** (margins 1.08–2.51,
  essentially unchanged from doc 43 §9).
- **Dial S is empty**: for every survivor, NO on-line zero lies within r/2 of
  t₀ (only 1–3 within ±1.7). Structural signature: **mid-band pairs sit in wide
  zero-free gaps of Z_g — the pair forms by consuming its flanking on-line
  zeros** (D-count conservation seen locally). The multi-zero gain is
  unavailable precisely where it is needed.
- **Dial r is flat**: best r = 0.5 for 7/8 — off the line |Φ| grows like
  (t/2π)^{(σ−1/2)/2}, so M_r outruns (r−η)².
- **P-M3 PASS, with the sharpness twist**: the TRUE error |ζ − g_N|(s₀) is
  65–95% of the declared E(t₀) = (t₀/2π)^{−1/4} at every survivor — at
  transition phases the RS first correction is near-maximal (|Ψ(p)| ≈ 0.92 at
  p ≈ 0). The declared bound is valid AND nearly sharp there: no room in the
  E-dial either.

## 3. What the no-go forces (the honest re-cut)

The measured wall — 8 events per 11,800 heights, all within |p − int| ≤ 0.19 —
cannot be removed by window geometry. It must be removed at the level of the
OBJECT: for fixed N, the height interval [2πN², 2π(N+1)²) is exactly one sweep
of p from 0 to 1, and on it g_N is a FIXED symmetrized Dirichlet polynomial. The
p-central statement is therefore:

> **(MID-central) [the wall, final measured form]:** for every N, the fixed
> symmetrized polynomial Φ_N has no off-line pairs of depth η > η₀ with
> ordinates in the middle portion (p ∈ [0.2, 0.8]) of its matched interval.

The survivors' mechanism (birth jump at N → N+1, doc 43 §9) lives at the
interval ENDS; between transitions the object is rigid — no term enters or
leaves — and the #146-measured coherence suppression is the acting force. This
is exactly the AFE-matched slice of the Gonek–Montgomery family (#149: their
fixed-N methods proved 100%-on-line for N ≤ T^{o(1)}; the question is what
their machinery yields on the matched slice t ≍ 2πN²) — the full-text mining is
now precisely targeted.

## 4. Openings

1. (MID-central) as a fixed-polynomial statement: one object per N, rigid on
   its interval — amenable to G–M's own methods, to the doc-12 small-ball
   salvage (valley depth N^{−2η} on a POLYNOMIAL of length N — the coherent
   large-deviation bound), and to the doc 38 minor chain as certificate.
2. The pair-eats-its-neighbors signature (§2): pair creation locally removes
   two on-line zeros — the creation event is a COLLISION in the Z_g zero flow
   as p varies. Tracking zero trajectories across one transition (N → N+1,
   cheap 1-D scans) would give the birth mechanism explicitly — and possibly a
   monotonicity statement (births only near transitions) which IS (MID-central).
3. The transition zone itself (|p| ≤ 0.2) stays excluded by the family choice;
   its parity bookkeeping routes through #144's traversal as designed.
