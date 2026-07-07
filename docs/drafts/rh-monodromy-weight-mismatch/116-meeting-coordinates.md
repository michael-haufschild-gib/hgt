# 116 — The meeting coordinates: mirror-of-mirror bookkeeping, the endpoint no-go, and the staircase design

[ANALYSIS + design; formal bricks follow in TorusWalk/PairStaircase. Everything cited
as proven is machine-checked in the tree.]

## Mirror-of-mirror: who steers whom

The cancellation theorem (doc 114) at a strip point `s` computes the orientation at the
MIRROR point `1−conj s`. Apply it at the mirror-annulus basepoints `P'± = (1−conj ρ) ± ic`:
since `1−conj(P'±) = ρ ± ic = P±`, the orientation at OUR basepoints is

```
Im ι_P(P±) = ‖A_P(P±)‖⁻¹ · Im( e^{−i·anchorTilt P (P±)} · conj(−G(P'±)) ).
```

So the two angles steering the ρ-annulus's own basepoint orientations are the tilts AT
THE BASEPOINTS, `φ± := anchorTilt P (ρ ± ic)` (frequencies τ ± c, real part σ), against
P-FREE member phases at the mirror basepoints. The TorusWalk quadrant/floor machinery
applies verbatim to `φ±` (same heights; `primeTilt_pos_iff` needs only `0 < σ`).

## The endpoint no-go [CONJECTURE → formal target]

Two proven facts collide: the deck class of the anchored member is P-RIGID
(`anchoredSEM_roots_of_sem_roots`), while the endpoint orientation signs
`−sign sin(φ± + β'±)` are P-STEERABLE — and once pair-reachability (below) is in, the
sign PAIR takes all four values as P varies. Therefore NO P-independent function of the
two endpoint Im-signs computes the deck class. The parity criterion's "two-point
boundary-orientation agreement" consequently CANNOT mean the raw endpoint Im-sign
agreement: the dictionary between the orientation reading and the mod-2 deck cocycle
must pass through data that co-varies with P on both sides — the ARGUMENT VARIATION
along the two boundary arcs between the basepoints (the tree's `ArgumentVariation.lean`
is the designated instrument). Formal no-go target: from pair-reachability, exhibit
`P₁, P₂` with the same member (same deck class) and different endpoint sign pairs.

This is a fail-fast refinement, not a dead end: it says the meeting functional's final
coordinates are (steered endpoint phases, arc-winding increments), and the arc-winding
of the ANCHOR is again tilt-differences — prime-indexed, sign-lawed, steerable — while
the member's arc-winding in the hole is pinned by the count (= order). The weld's
conjecture in these coordinates: the anchor's steerable arc contribution can always be
driven to expose the member's parity-pinned winding, and evenness is the only stable
position; the D–H analogue, having no walk, cannot be so driven.

## The staircase design (pair-reachability, the remaining mechanical object)

Sequential fresh-prime drawing has summable floors (geometric window spacing) — pools
are necessary. Design: fix ONE scale `x` and FOUR windowPrimes pools (one per
quadrant); at scale `x` every pool element has floor `f = arctan(x'^{σ−1}·(√2/2)/2)`
(proven), ceiling `δ = 4x^{−σ₀}` (proven), pool size `≥ mass/log` (proven, divergent).
Choose `x` with `δ ≤ ε` and each pool budget `≥ T₊ + T₋ + 4δ`. Staircase induction on
`⌈(d₊ + d₋)/f⌉`: if both deficits `> 0`, draw from the `(sign d₊, sign d₋)` pool — both
deficits shrink; if one deficit is in its `[−δ, δ]` band, draw from the quadrant that
descends the other while keeping the banded one within `[−δ, δ]` (its step is `≤ δ`);
terminate when both are banded. Every ingredient is banked; the induction is the last
uncertified step.

## Addendum — the staircase corrected: naive alternation diverges, two-phase descent works

Working the step ballistics: the naive staircase (drive one coordinate, correct the
other when it exits its band) does NOT terminate — each correction of the banded
coordinate disturbs the driven one by up to the ceiling `δ`, which costs `≥ δ/f ≥ 1`
further corrections: a cascade of ratio `R = δ/f > 1`. The repair is structural: in
each half-plane of need, BOTH quadrant pools advance the driven coordinate by `≥ f`
(they differ only in the other coordinate's direction). So:

- **Phase 1** (while `d₊ > δ`): step from `(+, +)` if `d₋ > 0`, else from `(+, −)` —
  `d₊` descends monotonically by `≥ f` per step (terminates), while `d₋` never leaves
  `[−δ, max(T₋, δ)]`.
- **Phase 2** (while `d₋ > δ`): step from `(sign-need of d₊, +)` — `d₋` descends
  monotonically, `d₊` stays in `[−2δ, 2δ]`.

Final tolerance `2δ` (take `δ = ε/2`); total steps `≤ (T₊+T₋+2δ)/f + 2` per pool, so
budgets `f·|pool| ≥ T₊+T₋+4δ` suffice — supplied by the Chebyshev window counts.
Formal shape: one `phase_descent` lemma (strong induction on the two consumed pools'
total cardinality; drives one coordinate into `(0, δ]` while banding the other), applied
twice with coordinates swapped. The pool hypotheses (per-element signs, floors `f`,
ceilings `δ`, cardinality lower bounds) are exactly the conclusions of
`exists_prime_tilt_sign_pair_floors(_base)` upgraded from ∃-prime to windowPrimes-pool
form plus `windowPrimes_card_ge`.
