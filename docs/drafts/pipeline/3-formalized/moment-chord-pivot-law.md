# The chord–pivot law for the moment growth exponent

- **ID:** `moment-chord-pivot-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/lindelof-hypothesis-campaign.md`, cycle 7
- **Statement:** With `M(A)` the growth exponent of `int_T^{2T}|zeta(1/2+it)|^A dt`, the quantity
  `A/8 - (M(A)-1)` — which Legendre duality certifies as a lower bound for the large-value exponent
  `phi(1/8)` — is **identically `1/2` on the whole chord** joining `(4,1)` to `(12,2)`, and exceeds
  `1/2` exactly when `M` dips strictly below that chord somewhere in `(4,12)`.
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT AN LH PROOF]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.MomentChordPivot`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` only. `scripts/formal_tools.py lint` passes.

## Goal

To locate the exact obstruction. `M(1/2,A) = 1` for `A <= 4` (Hardy–Littlewood) and
`M(1/2,12) <= 2` (Heath-Brown 1978) are the only anchors; the ANTEDB records **nothing** on
`4 < A < 12` beyond convexity. This theorem shows that the resulting chord is not merely the best
available bound — it is a *plateau* for the pivot functional, so every derived floor
(`M(8) >= 3/2`, `M(12) >= 2`) is pinned by it, and every improvement of either requires dipping
below the chord.

## Statement

```text
momentChord A      = 1 + (A-4)/8
pivotGain M A      = A/8 - M A + 1

momentChord_upper              : ConvexOn M → M 4 = 1 → M 12 ≤ 2 → 4 ≤ A ≤ 12 → M A ≤ momentChord A
pivotGain_momentChord          : pivotGain momentChord A = 1/2          -- the plateau
pivotGain_gt_half_iff_below_chord : 1/2 < pivotGain M A ↔ M A < momentChord A
pivotGain_le_half              : (known envelope) → 0 ≤ A → pivotGain M A ≤ 1/2
pivotGain_at_four              : M 4 = 1 → pivotGain M 4 = 1/2          -- attained
chord_values                   : momentChord 8 = 3/2 ∧ momentChord 12 = 2
```

`pivotGain_le_half` takes the whole known envelope as hypotheses — `M = 1` on `[0,4]`, `M >=`
chord on `[4,12]`, and the Hölder extension `M A >= 2 + s(A-12)` for `A >= 12` with `s >= 1/8`
(for zeta `s = 2 mu(1/2) <= 13/42 > 1/8`) — and concludes that **no index whatsoever certifies a
gain above `1/2`**. The certified value of `phi(1/8)` is exactly `1/2`.

## Why `1/8`

The plateau is an exact algebraic coincidence: the chord slope is `1/8` and the evaluation point is
`v = 1/8`, so `A/8 - momentChord(A) + 1` is constant. Every other characterisation of the pivot
found in the campaign (crossing of the 4th/12th-moment constraints; `V^4 = sqrt N` at the self-dual
block; the Guth–Maynard `N^{3/4}` threshold; the ceiling of both classical error-term programmes)
lands on the same point.

## Gates
- [x] 0 → 1 well-posed, source-pure
- [x] 1 → 2 complete paper proof, no open dependency
- [x] 2 → 3 Lean theorems above, module builds, axioms clean, lint passes
- [ ] 3 → 4 standalone write-up

## Novelty audit
- The individual bounds (`M(1/2,A)=1` for `A<=4`; `M(1/2,12)<=2`; convexity of `M` in `A`) are
  classical and are recorded in the ANTEDB (Tao–Trudgian–Yang, chapter "Moment growth for the zeta
  function"), which also confirms that **nothing is recorded on `4 < A < 12` beyond convexity**.
- The **plateau/pivot statement** — that the Legendre-certified value of `phi(1/8)` is exactly `1/2`
  across the entire chord, so the chord is a rigidity rather than an artefact — is the new content.
  The ANTEDB is a ledger of bounds; it records no barrier of this kind.
- Corroboration found after the fact: Trudgian–Yang's interpolation `M(1/2,12+delta) <= 2 + delta/8
  + c delta^{3/2}` has linear slope exactly `1/8`, matching the chord slope at `A = 12`.
- Classification: `NEEDS EXTERNAL AUDIT`, provisionally new-in-form.

## Log
- 2026-07-25 — originated, proved, formalized, lint green.
